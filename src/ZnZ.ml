module ZnZ (N: sig val n : int end) : Polynome.ANNEAU =
    struct
        type t = int
        let n = if N.n > 0 then N.n else failwith "n <= 0"
        let zero = 0
        let unit = 1
        let sum x y = ( x + y ) mod n
        let mult x y = ( x * y ) mod n
        let equal = ( = )
        let tostring = string_of_int
    end ;;

module Z7Z = ZnZ (struct let n = 7 end);;
module Z13Z = ZnZ (struct let n = 13 end);;

