open Reed_solomon
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

