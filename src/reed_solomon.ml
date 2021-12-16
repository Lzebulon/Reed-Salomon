(**Addition in galois field *)
let gf_add x y =  x lxor y;;
(**Substraction in galois field is the same as an addition *)
let gf_sub x y =  x lxor y;;

(**Multiplication in galois field without optimization *)
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

(**Init the exp and log table for optimize multiplication and addition in the galois field *)
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

(** Log table and Exp table for optimize the calcul i the galois field *)
let gf_log, gf_exp = init_table ();;

(** Multiplication opti with log and exp table *)
let gf_mul x y =
    if x = 0 || y = 0 then 0
    else gf_exp.(gf_log.(x) + gf_log.(y));;

(** Division in galois field with the log and exp table for optimization *)
let gf_div x y =
    if y = 0 then failwith "Division by 0" ;
    if x = 0 then 0
    else gf_exp.((gf_log.(x)+255 - gf_log.(y)) mod 255);;

let ( /// ) x y =
    let result = x mod y in
    if result >= 0 then result
    else result + y;;

(** Power optimize with log and exp table *)
let gf_pow x power = gf_exp.( (gf_log.(x) * power ) /// 255 );;

(** Inverse is the same of 1/x *)
let gf_inverse x = gf_exp.(255-gf_log.(x));;

(** Multiplies a polynomial by a scalar *)
let gf_poly_scale p x = 
    let n = Array.length p in
    let r = Array.make n 0 in
    for i = 0 to n-1 do
        r.(i) <- gf_mul p.(i) x
    done;
    r;;

(** Addition of two polynomial *)
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

(** Multiplication of two polynomials *)
let gf_poly_mul p q =
    let np = Array.length p and nq = Array.length q in
    let r = Array.make (np+nq-1)0 in
    for i = 0 to np-1 do
        for j = 0 to nq-1 do
            r.(i+j) <- r.(i+j) lxor (gf_mul p.(i) q.(j))
        done
    done;
    r;;

(** Evaluation of a polynomial [p] in [x] *)
let gf_poly_eval p x =
    let y = ref p.(0) in
    for i = 1 to Array.length p - 1 do
        y := (gf_mul !y x) lxor p.(i)
    done;
    !y;;


(** Generate the generator polynomial *)
let rs_generator_poly n =
    let g = ref [|1|] in
    for i = 0 to n-1 do
        g := gf_poly_mul !g [|1 ; gf_pow 2 i|]
    done;
    !g;;


(** Division of two polynomials *)
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


(** Encode the message *)
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



(** Calcul syndrome of the message receive *)
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



let rs_find_error_locator ?(erase_loc=None) ?(erase_count=0) synd nsym =
    let err_loc, old_loc = if Option.is_some erase_loc then 
                             ref (Array.copy (Option.get erase_loc)), ref (Array.copy (Option.get erase_loc)) 
                            else ref [|1|], ref [|1|] in
    let synd_shift = if Array.length synd > nsym then Array.length synd - nsym else 0    in

    for i = 0 to nsym-erase_count -1 do
        let k = if Option.is_some erase_loc then erase_count + i + synd_shift else i + synd_shift in
        let temp = synd.(k) in
        let delta = ref temp in
        for j = 1 to Array.length !err_loc -1 do
            delta := gf_add !delta (gf_mul !err_loc.(Array.length !err_loc -(j+1)) synd.(k-j));
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
    let err_pos = ref [||] in
    for i = 0 to len_msg -1 do
        if gf_poly_eval err_loc (gf_pow 2 i) = 0 then err_pos := Array.append !err_pos [|len_msg-1-i|];
    done;
    if Array.length !err_pos <> errs then failwith "error in chien search";
    !err_pos;;


let rs_forney_syndrome synd pos nmsg =
    let erase_pos_revers = Array.make (Array.length pos) 0 in
    for i = 0 to Array.length pos -1 do
        erase_pos_revers.(i) <- nmsg - 1 -pos.(i)
    done;

    let fsynd = Array.make (Array.length synd ) 0 in
    for i = 0 to Array.length synd -1 do
        fsynd.(i) <- synd.(i)
    done;
    for i = 0 to Array.length pos -1 do
        let x = gf_pow 2 erase_pos_revers.(i) in
        for j = 0 to Array.length fsynd -2 do
            fsynd.(j) <- (gf_mul fsynd.(j) x) lxor fsynd.(j+1)
        done;
    done;
    fsynd;;

let rs_correct_msg ?(erase_pos=None) msg_in nsym =
    if Array.length msg_in > 255 then failwith "to long";

    let msg_out = Array.copy msg_in in

    let erase_posc = if Option.is_none erase_pos then [||] else Option.get (erase_pos) in
    if Option.is_some erase_pos then 
        for i =0 to Array.length erase_posc - 1 do
        msg_out.(erase_posc.(i)) <- 0;
        done;
    
    if Array.length erase_posc > nsym then failwith "too many error";

    let synd = rs_calcul_syndrome msg_out nsym in
    if synd = Array.make nsym 0 then msg_out
    else begin
    
    let fsynd = rs_forney_syndrome synd erase_posc (Array.length msg_out) in
    let err_loc = rs_find_error_locator ~erase_count:(Array.length erase_posc) fsynd nsym in
    let err_loc1 = Array.make (Array.length err_loc) 0 in
    for i = 0 to Array.length err_loc1 - 1 do
        err_loc1.(i) <- err_loc.(Array.length err_loc -1 -i)
        done;
    let err_pos = rs_find_error err_loc1 (Array.length msg_out) in
    if err_pos = [||] then failwith "position of the error not find";
    let errase_pos_tot = Array.append erase_posc err_pos in

    rs_correction msg_out synd errase_pos_tot end;;

open Printf
open Random


let test n k ?(p=0.) ?(ne=0) ntest seed =
    Random.init seed;
    let sucess = ref 0 in 
    let random_message n = let msg =  Array.make n 0 in
        for i = 0 to n-1 do
            msg.(i) <- Random.int 256
            done;
        msg in
    let add_error msg n = 
        let msge = Array.copy msg in
        if p <> 0. then begin
        for i = 0 to n-1 do
            if Random.float 1. < p then msge.(i) <- Random.int 256
        done; msge end
        else if ne <> 0 then begin
        for i = 0 to ne-1 do
            msge.(Random.int n) <- Random.int 256
        done; msge end
        else failwith "add a proba or a error number in parameters"
        in
    
    let hamming_distance a b = let n = Array.length a in let d = ref 0 in
        for i = 0 to n-1 do
            if a.(i) <> b.(i) then incr d;
            done;
        !d
    in

    for i = 1 to ntest do
        let msg_init = random_message n in
        let encoded_msg = rs_encode_msg msg_init (n-k) in
        let erroned_msg = add_error encoded_msg n in
        try
            let decoded_msg = rs_correct_msg erroned_msg (n-k) in
            if encoded_msg = decoded_msg then incr sucess;
            printf "boucle %d %d %d\n"  i (hamming_distance encoded_msg erroned_msg) (hamming_distance encoded_msg decoded_msg);
        with _ -> ();
        
        done;
        printf "taux de reparation : %d / %d"  !sucess ntest;;

test 200 150 ~p:0.5 100 25;;