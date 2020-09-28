export function $sieve(w %n, l %ptr0){
@start2
 ##extsb
    %cond = w csgtw %n,0
    jnz %cond, @zero, @loop2end
@zero
    storeb 0, %ptr0
    %cond = w csgtw %n,1
    jnz %cond, @one, @loop2end
@one
    %ptr = l add %ptr0, 1
    storeb 0, %ptr    
    %ptr = l add %ptr0,2

    %k = l add 2,0
@loophead
    %cond = w csltw %k,%n
    jnz %cond, @loopbody, @loopend
@loopbody    
    storeb 1, %ptr
    %ptr = l add %ptr,1
    %k = l add %k,1
    jmp @loophead
@loopend

    %i = l add 2,0
@loop2head
    %cond = w csltw %i,%n
    jnz %cond, @loop2body, @loop2end
@loop2body
    %ptr = l add %ptr0, %i
    %cond = w loadub %ptr
    jnz %cond, @loop3, @loop3end
@loop3
    #%t =w call $printf(l $fmt, w %i)
    %j = l mul %i,%i
    @loop3head
        %cond = w csltw %j,%n
        jnz %cond, @loop3body, @loop3end
    @loop3body
        %ptr = l add %ptr0, %j
        storeb 0, %ptr
        %j = l add %j,%i
        jmp @loop3head
    @loop3end

    %i = l add %i,1
    jmp @loop2head
@loop2end
    ret
}


