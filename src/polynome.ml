module type ANNEAU =
    sig
        type t 
        val zero : t
        val unit : t 
        val sum : t -> t -> t
        val mult : t -> t -> t
        val equal : t -> t -> bool
        val tostring : t -> string
    end ;;

module Int : ANNEAU =
    struct
        type t = int
        let zero = 0
        let unit = 1
        let sum = ( + )
        let mult = ( * )
        let equal = ( = )
        let tostring = string_of_int
    end ;;

module Bool : ANNEAU =
    struct
        type t = bool
        let zero = false
        let unit = true
        let sum = ( || )
        let mult = ( && )
        let equal = ( = )
        let tostring x = if x then "True" else "False"
    end ;;


let rec power f n = 
    let compose f g x = f (g x) in
    if n < 0 then failwith "power"
    else if n = 0 then function x -> x
    else compose f (power f (n-1));;

