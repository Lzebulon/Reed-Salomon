let gf_add x y =  x lxor y;;
(**Substraction in galois field is the same as an addition *)
let gf_sub x y =  x lxor y;;

(* let gf_mult_noLUT ?(prim=0) x y  =

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
 *)

let gf_mult_noLUT ?(prim=0) ?(field_charac_full=256) ?(carryless=true) x y =
    let y1 = ref y and x1 = ref x in
    let r = ref 0 in
    while !y1 <> 0 do
        if !y1 land 1 <> 0 then r := if carryless then !r lxor !x1 else !r + !x1;
        y1 := !y1 lsr 1 ;
        x1 := !x1 lsl 1 ;
        if prim > 0 && !x1 land field_charac_full <> 0 then x1 := !x1 lxor prim
        done;
    !r;;

let init_table ?(prim=0x11d) () = 
    let gf_exp = Array.make 512 0 in
    let gf_log = Array.make 256 0 in
    let x = ref 1 in

    for i=0 to 254 do
        gf_exp.(i) <- !x ;
        gf_log.(!x) <- i ;
        x := gf_mult_noLUT !x 2 ~prim:prim
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

let gf_pow x power = gf_exp.( (((gf_log.(x) * power ) mod 255) + 255) mod 255 );;

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
    let r = Array.make nr 0 in
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
        y := (gf_mul !y x) lxor p.(i)
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
    msg , Array.length msg - Array.length divisor +1;;

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



let rs_find_error_location pos =
    let location = ref [|1|] in
    for i = 0 to Array.length pos -1 do
        location := gf_poly_mul !location (gf_poly_add [|1|] [|gf_pow 2 pos.(i);0|])
    done;
    !location;;

let rs_find_error_evaluate synd error_location nsym =
    let s = Array.make (nsym+1) 0 in s.(0) <- s.(0) + 1;
    let quotient, separator = gf_poly_div (gf_poly_mul synd error_location) s in
    let remainder = Array.make (Array.length quotient - separator +1) 0 in
    for i = 0 to Array.length quotient - separator -1 do
        remainder.(i) <- quotient.(separator + i)
    done;
    remainder;;

(*Error in this code*)
let rs_correction msg_in synd error_position =
    let coeff_position = Array.make (Array.length error_position) 0 in
    for i = 0 to Array.length error_position -1 do
        coeff_position.(i) <- Array.length msg_in - error_position.(i) - 1
    done;
    let error_location = rs_find_error_location coeff_position in
    let synd1 = Array.make (Array.length synd) 0 in
    for i = 0 to Array.length synd -1 do
        synd1.(i) <- synd.(Array.length synd - 1 - i)
    done;
    let error_evaluation = rs_find_error_evaluate synd1 error_location (Array.length error_location -1) in
    let error_evaluation1 = Array.make (Array.length error_evaluation ) 0 in
    for i = 0 to Array.length error_evaluation -1 do
        error_evaluation1.(i) <- error_evaluation.(Array.length error_evaluation - 1 - i)
    done;

    let x = Array.make (Array.length coeff_position) 0 in
    for i = 0 to Array.length coeff_position -1 do
        x.(i) <- gf_pow 2 (coeff_position.(i) - 255)
    done;

    let e = Array.make (Array.length msg_in) 0 in
    let xlength = Array.length x in
    for i = 0 to xlength -1 do
        let xi_inv = gf_inverse x.(i) in

        let error_location_temp = ref [||] in 

        for j = 0 to xlength -1 do
            if j <> i then error_location_temp := Array.append !error_location_temp [|gf_sub 1 (gf_mul xi_inv x.(j))|];
        done;
        let error_loc_prime = ref 1 in
        for k=0 to Array.length !error_location_temp -1 do
            error_loc_prime := gf_mul !error_loc_prime !error_location_temp.(k)
        done;
        let y = gf_mul (gf_pow x.(i) 1) (gf_poly_eval error_evaluation xi_inv) in
        if !error_loc_prime = 0 then failwith "error";
        e.(error_position.(i)) <- gf_div y !error_loc_prime;
    done;
    gf_poly_add msg_in e ;;



let synd = rs_calcul_syndrome msg 10;; (**It's egal to a nul array normaly *)
rs_check msg 10;;
    
let msg2 = Array.copy msg;;
msg2.(0) <- 0;;
    
let synd_error = rs_calcul_syndrome msg2 10;;
rs_check msg2 10;;

let corr = rs_correction msg2 synd_error [|24|];;
let a = [|0x40; 0xd2; 0x75; 0x47; 0x76; 0x17; 0x32; 0x6; 0x27; 0x26; 0x96; 0xc6; 0xc6; 0x96; 0x70; 0xec;
0xbc; 0x2a ;0x90; 0x13; 0x6b; 0xaf; 0xef; 0xfd; 0x4b; 0xe0|];;
corr = [|0x40; 0xd2; 0x75; 0x47; 0x76; 0x17; 0x32; 0x6; 0x27; 0x26; 0x96; 0xc6; 0xc6; 0x96; 0x70; 0xec;
0xbc; 0x2a ;0x90; 0x13; 0x6b; 0xaf; 0xef; 0xfd; 0x4b; 0xe0|];;


let rs_find_error_locator ?(erase_loc=None) ?(erase_count=0) synd nsym =
    let err_loc, old_loc = if Option.is_some erase_loc then ref (Array.copy (Option.get erase_loc)), ref (Array.copy (Option.get erase_loc)) else ref [|1|], ref [|1|] in
    let synd_shift = Array.length synd - nsym in

    for i = 0 to nsym-erase_count -1 do
        let k = if Option.is_some erase_loc then erase_count + i + synd_shift else i + synd_shift in
        let temp = synd.(k) in
        let delta = ref temp in
        for j = 1 to Array.length !err_loc -1 do
            delta := !delta lxor gf_mul !err_loc.(Array.length !err_loc -(j+1)) synd.(k-j);
        done;

        old_loc := Array.append !old_loc [|0|];

        if !delta <> 0 then (
            if Array.length !old_loc > Array.length !err_loc then (
                let new_loc = gf_poly_scale !old_loc !delta in
                old_loc := gf_poly_scale !err_loc (gf_inverse !delta);
                err_loc := new_loc;
            );
            err_loc := gf_poly_add !err_loc (gf_poly_scale !old_loc !delta);
            )
    done;
    
    while Array.length !err_loc <> 0 && !err_loc.(0) = 0 do
       err_loc := Array.sub !err_loc 1 (Array.length !err_loc -1);
    done;
    let err = Array.length !err_loc -1 in
    if (err-erase_count)*2 + erase_count > nsym then failwith "trop d'erreur";
    !err_loc;;


let rs_find_error err_loc len_msg =
    let errs = Array.length err_loc -1 in
    let err_pos = ref [||] and result = ref [||] in
    for i = 0 to len_msg -1 do
        let a = gf_poly_eval err_loc (gf_pow 2 i)in 
        if a = 0 then err_pos := Array.append !err_pos [|len_msg-1-i|];
        result := Array.append !result [|a|]
    done;
    if Array.length !err_pos <> errs then err_pos := !result;
    !err_pos;;

let msg3 = Array.copy msg;;
msg3.(0) <- 0;;
(* msg3.(10) <- 7;;
msg3.(20) <- 8;; *)
let synd3 = rs_calcul_syndrome msg3 10;;
let err_loc3 = rs_find_error_locator synd3 10;;
let err_loc31 = Array.make (Array.length err_loc3) 0;;
for i = 0 to Array.length err_loc3 -1 do
    err_loc31.(i) <- err_loc3.(Array.length err_loc3 -1 -i)
done;;
err_loc31, err_loc3;;
let pos3 = rs_find_error err_loc3 (Array.length msg3);;
rs_correction msg3 synd3 [|0|];;