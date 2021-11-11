let gf_add x y =  x lxor y;;
(**Substraction in galois field is the same as an addition *)
let gf_sub x y =  x lxor y;;

let gf_mul_noLUT ?(prim=0) x y  =

    let cl_mult x y =
        let z = ref 0 and i = ref 0 in
        while ( y lsr !i) > 0 do
            if y land (1 lsl !i) <> 0 then z :=  !z lxor ( x lsl !i);
        incr i
        done;
        !z
    in

    let bit_length n =
        let bits = ref 0 in
        while n lsr !bits <> 0 do 
            incr bits
        done;
        !bits
    in

    let cl_div ?(divisor=0) dividend =
        let div = ref dividend in
        let dl1 = bit_length !div in
        let dl2 = bit_length divisor in

        if dl1 < dl2 then !div
        else (for i = dl1-dl2 downto 0 do
                if !div land (1 lsl (i + dl2 - 1) ) <> 0 then div := !div lxor (divisor lsl i)
            done;
        !div)
    in

    let result = ref (cl_mult x y) in
    if prim > 0 then result := cl_div ~divisor:prim !result ;
    !result;;



let init_table ?(prim=0x11d) () = 
    let gf_exp = Array.make 512 0 in
    let gf_log = Array.make 256 0 in
    let x = ref 1 in

    for i=0 to 254 do
        gf_exp.(i) <- !x ;
        gf_log.(!x) <- i ;
        x := gf_mul_noLUT !x 2 ~prim:prim
    done; 
    for i = 255 to 511 do
        gf_exp.(i)<- gf_exp.(i - 255)
    done;
    gf_log, gf_exp;;

let gf_log, gf_exp = init_table ();;

let gf_mul x y =
    if x = 0 || y = 0 then 0
    else gf_exp.(gf_log.(x) + gf_log.(y));;


let gf_div x y =
    if y = 0 then failwith "Division by 0" ;
    if x = 0 then 0
    else gf_exp.((gf_log.(x)+255 - gf_log.(y)) mod 255);;

let gf_pow x power = gf_exp.( (gf_log.(x) * power) mod 255);;

let gf_inverse x = gf_exp.(255-gf_log.(x));;

let gf_poly_scale p x = 
    let n = Array.length p in
    for i = 0 to n-1 do
        p.(i) <- gf_mul p.(i) x
    done;
    p;;

let gf_poly_add p q =
    let np = Array.length p and nq = Array.length q in
    let nr = max np nq in
    let r = Array.make 0 nr in
    for i = 0 to np-1 do
        r.(i+nr-np) <- p.(i)
    done;
    for i = 0 to nq-1 do
        r.(i+nr-nq) <- r.(i+nr-nq) lxor q.(i)
    done;
    r;;

let gf_poly_mul p q =
    let np = Array.length p and nq = Array.length q in
    let r = Array.make (np+nq-1)0 in
    for i = 0 to np-1 do
        for j = 0 to nq-1 do
            r.(i+j) <- r.(i+j) lxor (gf_mul p.(i) q.(j))
        done
    done;
    r;;

let gf_poly_eval p x =
    let y = ref p.(0) in
    for i = 1 to Array.length p - 1 do
        y := (gf_mul !y x) lxor  p.(i)
    done;
    !y;;


gf_poly_eval [|0x01; 0x0f; 0x36; 0x78; 0x40|] 0 ;;



let rs_generator_poly n =
    let g = ref [|1|] in
    for i = 0 to n-1 do
        g := gf_poly_mul !g [|1 ; gf_pow 2 i|]
    done;
    !g;;

let gf_poly_div dividend divisor =
    let msg = dividend in
    for i = 0 to Array.length dividend - Array.length divisor do
        let c = msg.(i) in
        if c <> 0 then 
            for j = 1 to Array.length divisor -1 do
                msg.(i+j) <- msg.(i+j) lxor (gf_mul divisor.(j) c)
            done;
    done;
    msg , 1 - Array.length divisor;;

let rs_encode_msg msg n =
    let g = rs_generator_poly n in
    let xmsg = Array.make (Array.length msg + Array.length g -1) 0 in 
    for i = 0 to Array.length msg -1 do
        xmsg.(i) <- msg.(i)
    done;
    let reminder, separator = gf_poly_div xmsg g in
    for i = 0 to Array.length msg - 1 do
        reminder.(i) <- msg.(i)
    done;
    reminder;;



(* 
let test = rs_generator_poly 4;;

rs_encode_msg [|0x12;0x34;0x56|] 4;;
*)

let msg_in = [| 0x40; 0xd2; 0x75; 0x47; 0x76; 0x17; 0x32; 0x06;0x27; 0x26; 0x96; 0xc6; 0xc6; 0x96; 0x70; 0xec |];;

let msg = rs_encode_msg msg_in 10;;
msg = [|0x40; 0xd2; 0x75; 0x47; 0x76; 0x17; 0x32; 0x6; 0x27; 0x26; 0x96; 0xc6; 0xc6; 0x96; 0x70; 0xec;
0xbc; 0x2a ;0x90; 0x13; 0x6b; 0xaf; 0xef; 0xfd; 0x4b; 0xe0|];;




let rs_calcul_syndrome msg nsym = 
    let syndrome = Array.make (nsym) 0 in
    for i = 0 to nsym-1 do
        syndrome.(i) <- gf_poly_eval msg (gf_pow 2 i)
    done;
    syndrome;;
let rs_check msg nsym =  rs_calcul_syndrome msg nsym = Array.make nsym 0;;


let synd = rs_calcul_syndrome msg 10;; (**It's egal to a nul array normaly *)
rs_check msg 10;;

msg.(0) <- 0;;

let synd_error = rs_calcul_syndrome msg 10;;
rs_check msg 10;;


let rs_find_error_location pos =
    let location = ref [|1|] in
    for i = 0 to Array.length pos do
        location := gf_poly_mul !location (gf_poly_add [|1|] [|gf_pow 2 pos.(i);0|])
    done;
    location;;

let rd_find_error_evaluate synd error_location nsym =
    let s = Array.make (nsym+1) 0 in s.(0) <- s.(0) + 1;
    let _, remainder = gf_poly_div (gf_poly_mul synd error_location) s in
    remainder;;
(*
TODO is not finish

let rs_correction msg_in synd error_position =
    let coeff_position = Array.make (Array.length error_position) 0 in
    for i = 0 to Array.length error_position -1 do
        coeff_position.(i) <- Array.length msg_in - error_position.(i) - 1
    done;
    let error_location = rs_find_error_location coeff_position in
    let synd1 = Array.make (Array.length synd) 0 in
    for i = 0 to Array.length synd -1 do
        synd1.(i) <- synd.(Array.length synd - i)
    done;
    let error_evaluation = rs_find_error_evaluate synd1 error_location (Array.length error_location -1) in
    let error_evaluation1 = Array.make (Array.length error_evaluation -1 ) 0 in
    for i = 0 to Array.length error_evaluation -1 do
        error_evaluation1.(i) <- error_evaluation.(Array.length error_evaluation - i)
    done;

     *)