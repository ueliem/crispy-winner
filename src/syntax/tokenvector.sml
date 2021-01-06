structure TokenVector : sig
  type item = (int * int) * MTSToken.t
  include MONO_VECTOR where type elem = item
end = struct
  open Vector
  type item = (int * int) * MTSToken.t
  type elem = item
  type vector = item vector
end
