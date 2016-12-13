module apriori_defs;

kind shared3p;
domain pd_shared3p shared3p;

template<domain D>
D uint[[1]] snoc (D uint[[1]] xs, D uint x)
//@ inline;
//@ free ensures size(\result) == size(xs) + 1;
//@ free ensures forall uint i; i < size(xs) ==> assertion<D>(\result[i] == xs[i]);
//@ free ensures assertion(\result[size(xs)] == x);
{
    return cat(xs,{x});
}

//@ lemma Snoc1 <domain D> (D uint[[1]] xs)
//@ requires size(xs) > 0;
//@ ensures assertion<D>(xs == snoc(init(xs),last(xs)))
//@ {}

template<domain D>
D uint[[2]] snoc (D uint[[2]] xs, D uint[[1]] x)
//@ inline;
//@ requires shape(xs)[1] == size(x);
//@ free ensures shape(\result)[0] == shape(xs)[0] + 1;
//@ free ensures shape(\result)[1] == shape(xs)[1];
//@ free ensures forall uint i; i < shape(xs)[0] ==> assertion<D>(\result[i,:] == xs[i,:]);
//@ free ensures assertion<D>(\result[shape(xs)[0],:] == x);
{
    return cat(xs,reshape(x,1,size(x)));
}

// Structures

struct frequent {
    uint [[2]] items;
    pd_shared3p uint [[2]] cache;
}

frequent newfrequent(uint F_size, pd_shared3p uint[[2]] db)
//@ inline;
{
   frequent f;
   uint[[2]] F (0,F_size);
   pd_shared3p uint[[2]] F_cache (0,shape(db)[0]);
   f.items = F;
   f.cache = F_cache;
   return f;
}