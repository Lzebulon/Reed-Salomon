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

module Int : ANNEAU
module Bool : ANNEAU