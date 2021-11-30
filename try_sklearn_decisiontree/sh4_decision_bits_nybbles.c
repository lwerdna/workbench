// n_nodes: 415
// n_leaves: 208
// max_depth: 15
if(b13 <= 0)
 if(b12 <= 0)
  if(nybble3 <= 10)
   if(b2 <= 0)
    if(b15 <= 0)
     if(b1 <= 0)
      if(nybble1 <= 2)
       if(b14 <= 0)
        if(nybble0 <= 8)
         if(nybble2 <= 0)
          if(b3 <= 0)
           return undef();
          else
           if(b4 <= 0)
            if(nybble1 <= 1)
             return clrt();
            else
             return clrmac();
           else
            return sett();
         else
          return undef();
        else
         if(nybble1 <= 1)
          if(nybble2 <= 0)
           if(b4 <= 0)
            return nop();
           else
            return div0u();
          else
           return undef();
         else
          return movt();
       else
        if(b5 <= 0)
         if(nybble1 <= 0)
          if(b0 <= 0)
           if(b3 <= 0)
            return shll();
           else
            return shll2();
          else
           if(nybble0 <= 5)
            return shlr();
           else
            return shlr2();
         else
          if(b3 <= 0)
           if(b0 <= 0)
            return dt();
           else
            return cmp_pz();
          else
           if(nybble0 <= 8)
            return shll8();
           else
            return shlr8();
        else
         if(b3 <= 0)
          if(b0 <= 0)
           return shal();
          else
           return shar();
         else
          if(b0 <= 0)
           return shll16();
          else
           return shlr16();
      else
       if(nybble2 <= 0)
        if(nybble1 <= 5)
         if(b14 <= 0)
          if(nybble0 <= 4)
           return undef();
          else
           if(nybble0 <= 8)
            if(nybble1 <= 3)
             return ldtlb();
            else
             if(nybble1 <= 4)
              return clrs();
             else
              return sets();
           else
            return undef();
         else
          return undef();
        else
         return undef();
       else
        return undef();
     else
      if(b3 <= 0)
       if(b14 <= 0)
        if(nybble0 <= 2)
         return stc();
        else
         if(b6 <= 0)
          if(b4 <= 0)
           if(b7 <= 0)
            if(nybble1 <= 1)
             return bsrf();
            else
             return braf();
           else
            if(b5 <= 0)
             return pref();
            else
             return ocbp();
          else
           if(nybble1 <= 6)
            return undef();
           else
            if(nybble1 <= 10)
             return ocbi();
            else
             return ocbwb();
         else
          if(b7 <= 0)
           return undef();
          else
           if(nybble1 <= 12)
            return movca_l();
           else
            return undef();
       else
        if(nybble0 <= 2)
         if(nybble1 <= 6)
          if(nybble1 <= 2)
           return sts_l();
          else
           if(nybble1 <= 4)
            if(b5 <= 0)
             return undef();
            else
             return stc_l();
           else
            return sts_l();
         else
          if(nybble1 <= 14)
           return undef();
          else
           return stc_l();
        else
         return stc_l();
      else
       if(nybble1 <= 6)
        if(b0 <= 0)
         if(nybble3 <= 2)
          if(nybble1 <= 2)
           return sts();
          else
           if(nybble1 <= 4)
            if(b5 <= 0)
             return undef();
            else
             return stc();
           else
            return sts();
         else
          if(nybble1 <= 2)
           return lds();
          else
           if(nybble1 <= 4)
            if(b5 <= 0)
             return undef();
            else
             return ldc();
           else
            return lds();
        else
         if(nybble1 <= 2)
          if(nybble3 <= 2)
           if(nybble2 <= 0)
            if(b4 <= 0)
             if(nybble1 <= 1)
              return rts();
             else
              return rte();
            else
             return sleep();
           else
            return undef();
          else
           if(b4 <= 0)
            if(b5 <= 0)
             return jsr();
            else
             return jmp();
           else
            return tas_b();
         else
          return undef();
       else
        if(nybble1 <= 14)
         return undef();
        else
         if(nybble0 <= 10)
          if(b14 <= 0)
           return stc();
          else
           return ldc();
         else
          return undef();
    else
     if(b9 <= 0)
      if(b8 <= 0)
       if(b11 <= 0)
        return mov_b();
       else
        if(nybble2 <= 10)
         return cmp_eq();
        else
         return undef();
      else
       if(b11 <= 0)
        return mov_w();
       else
        if(b10 <= 0)
         return bt();
        else
         return bt_s();
     else
      if(nybble2 <= 14)
       if(nybble2 <= 10)
        return undef();
       else
        if(nybble2 <= 12)
         return bf();
        else
         return undef();
      else
       return bf_s();
   else
    if(nybble3 <= 2)
     if(b0 <= 0)
      if(b1 <= 0)
       return mov_b();
      else
       return mov_l();
     else
      if(b1 <= 0)
       return mov_w();
      else
       if(b3 <= 0)
        return mul_l();
       else
        return mac_l();
    else
     if(nybble0 <= 6)
      if(b15 <= 0)
       if(nybble1 <= 2)
        if(nybble0 <= 5)
         if(b4 <= 0)
          if(b5 <= 0)
           if(b0 <= 0)
            return rotl();
           else
            return rotr();
          else
           if(b0 <= 0)
            return rotcl();
           else
            return rotcr();
         else
          if(b0 <= 0)
           return undef();
          else
           return cmp_pl();
        else
         return lds_l();
       else
        if(nybble0 <= 5)
         return undef();
        else
         if(nybble1 <= 6)
          if(nybble1 <= 4)
           if(b6 <= 0)
            return ldc_l();
           else
            return undef();
          else
           return lds_l();
         else
          if(nybble1 <= 14)
           return undef();
          else
           return ldc_l();
      else
       if(b9 <= 0)
        if(b8 <= 0)
         if(b11 <= 0)
          return mov_b();
         else
          if(b10 <= 0)
           return cmp_eq();
          else
           return undef();
        else
         if(nybble2 <= 7)
          return mov_w();
         else
          if(nybble2 <= 11)
           return bt();
          else
           return bt_s();
       else
        if(nybble2 <= 14)
         if(nybble2 <= 10)
          return undef();
         else
          if(b10 <= 0)
           return bf();
          else
           return undef();
        else
         return bf_s();
     else
      if(nybble3 <= 6)
       if(b1 <= 0)
        if(b0 <= 0)
         return shad();
        else
         return shld();
       else
        if(nybble0 <= 10)
         return ldc_l();
        else
         if(b0 <= 0)
          return ldc();
         else
          return mac_w();
      else
       if(b9 <= 0)
        if(b8 <= 0)
         if(nybble2 <= 6)
          return mov_b();
         else
          if(nybble2 <= 10)
           return cmp_eq();
          else
           return undef();
        else
         if(b11 <= 0)
          return mov_w();
         else
          if(nybble2 <= 11)
           return bt();
          else
           return bt_s();
       else
        if(nybble2 <= 14)
         if(nybble2 <= 10)
          return undef();
         else
          if(b8 <= 0)
           return undef();
          else
           return bf();
        else
         return bf_s();
  else
   if(nybble2 <= 6)
    if(b9 <= 0)
     if(b8 <= 0)
      return mov_b();
     else
      return mov_w();
    else
     if(b8 <= 0)
      return mov_l();
     else
      return trapa();
   else
    if(b9 <= 0)
     if(b10 <= 0)
      if(nybble2 <= 8)
       return tst();
      else
       return and();
     else
      if(nybble2 <= 12)
       return tst_b();
      else
       return and_b();
    else
     if(b8 <= 0)
      if(b10 <= 0)
       return xor();
      else
       return xor_b();
     else
      if(b11 <= 0)
       return mova();
      else
       if(nybble2 <= 13)
        return or();
       else
        return or_b();
 else
  if(b15 <= 0)
   return mov_l();
  else
   if(nybble3 <= 11)
    return mov_w();
   else
    return mov_l();
else
 if(nybble3 <= 10)
  if(nybble3 <= 8)
   if(nybble3 <= 6)
    if(nybble0 <= 6)
     if(b0 <= 0)
      if(b1 <= 0)
       if(b12 <= 0)
        return mov_b();
       else
        if(nybble0 <= 2)
         return cmp_eq();
        else
         return div1();
      else
       if(b12 <= 0)
        return mov_l();
       else
        if(nybble0 <= 4)
         return cmp_hs();
        else
         return cmp_hi();
     else
      if(b12 <= 0)
       if(b1 <= 0)
        return mov_w();
       else
        if(b14 <= 0)
         return undef();
        else
         return mov();
      else
       if(b1 <= 0)
        if(b2 <= 0)
         return undef();
        else
         return dmulu_l();
       else
        return cmp_ge();
    else
     if(b3 <= 0)
      if(nybble3 <= 2)
       return div0s();
      else
       if(b12 <= 0)
        return not();
       else
        return cmp_gt();
     else
      if(b0 <= 0)
       if(nybble0 <= 9)
        if(b14 <= 0)
         if(nybble3 <= 2)
          return tst();
         else
          return sub();
        else
         return swap_b();
       else
        if(b2 <= 0)
         if(b12 <= 0)
          if(b14 <= 0)
           return xor();
          else
           return negc();
         else
          return subc();
        else
         if(b14 <= 0)
          if(nybble0 <= 13)
           if(b12 <= 0)
            return cmp_str();
           else
            return add();
          else
           if(nybble3 <= 2)
            return mulu_w();
           else
            return addc();
         else
          if(nybble0 <= 13)
           return extu_b();
          else
           return exts_b();
      else
       if(nybble3 <= 2)
        if(nybble0 <= 10)
         return and();
        else
         if(b2 <= 0)
          return or();
         else
          if(nybble0 <= 14)
           return xtrct();
          else
           return muls_w();
       else
        if(b14 <= 0)
         if(b2 <= 0)
          if(b1 <= 0)
           return undef();
          else
           return subv();
         else
          if(nybble0 <= 14)
           return dmuls_l();
          else
           return addv();
        else
         if(b2 <= 0)
          if(b1 <= 0)
           return swap_w();
          else
           return neg();
         else
          if(nybble0 <= 14)
           return extu_w();
          else
           return exts_w();
   else
    return add();
  else
   return bra();
 else
  if(b12 <= 0)
   return mov();
  else
   if(nybble3 <= 13)
    return bsr();
   else
    if(nybble0 <= 5)
     if(b1 <= 0)
      if(nybble0 <= 0)
       return fadd();
      else
       if(nybble0 <= 2)
        return fsub();
       else
        if(b0 <= 0)
         return fcmp_eq();
        else
         return fcmp_gt();
     else
      if(b0 <= 0)
       return fmul();
      else
       return fdiv();
    else
     if(nybble0 <= 12)
      return fmov();
     else
      if(b0 <= 0)
       return fmac();
      else
       if(nybble0 <= 14)
        if(nybble1 <= 9)
         if(b7 <= 0)
          if(nybble1 <= 0)
           return fsts();
          else
           if(b5 <= 0)
            if(b4 <= 0)
             return fneg();
            else
             if(b6 <= 0)
              return flds();
             else
              return fabs();
           else
            if(b6 <= 0)
             if(nybble1 <= 2)
              return float();
             else
              return ftrc();
            else
             if(nybble1 <= 6)
              return fsqrt();
             else
              return fsrra();
         else
          if(nybble1 <= 8)
           return fldi0();
          else
           return fldi1();
        else
         if(nybble1 <= 13)
          if(b8 <= 0)
           if(b5 <= 0)
            return undef();
           else
            if(nybble1 <= 10)
             return fcnvsd();
            else
             return fcnvds();
          else
           return undef();
         else
          if(b4 <= 0)
           return fipr();
          else
           if(b8 <= 0)
            return fsca();
           else
            if(b9 <= 0)
             return ftrv();
            else
             if(b10 <= 0)
              if(b11 <= 0)
               return fschg();
              else
               return frchg();
             else
              return undef();
       else
        return undef();
