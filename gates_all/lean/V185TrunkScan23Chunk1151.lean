import V185TrunkScan23Chunk1150

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6817495 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_6817495 : Nat := 118140960795 + 6817495 * 2 ^ 59
def prefixEnd_6817495 : Nat := 4983230072969 + 3 ^ 40 * 6817495 * 2
def baseEnd_6817495 : Nat := 3500651794623909253159417

theorem tailTrace_6817495 : CollatzResearch.WordTrace tailWord_6817495 prefixEnd_6817495 3500651794623909253159417 := by
  unfold tailWord_6817495
  simp only [CollatzResearch.WordTrace]
  refine ⟨248654470436387425293629939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165769646957591616862419959 248654470436387425293629939)
  ·
    refine ⟨372981705654581137940444909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248654470436387425293629939 372981705654581137940444909)
    ·
      refine ⟨139868139620467926727666841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372981705654581137940444909 139868139620467926727666841)
      ·
        refine ⟨104901104715350945045750131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139868139620467926727666841 104901104715350945045750131)
        ·
          refine ⟨157351657073026417568625197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104901104715350945045750131 157351657073026417568625197)
          ·
            refine ⟨59006871402384906588234449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157351657073026417568625197 59006871402384906588234449)
            ·
              refine ⟨44255153551788679941175837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59006871402384906588234449 44255153551788679941175837)
              ·
                refine ⟨16595682581920754977940939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44255153551788679941175837 16595682581920754977940939)
                ·
                  refine ⟨24893523872881132466911409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16595682581920754977940939 24893523872881132466911409)
                  ·
                    refine ⟨18670142904660849350183557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24893523872881132466911409 18670142904660849350183557)
                    ·
                      refine ⟨3500651794623909253159417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18670142904660849350183557 3500651794623909253159417)
                      ·
                        rfl

theorem cell23_6817495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_6817495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817495 prefixEnd_6817495 := by exact prefixLift 6817495
  have htrace : WordTrace (prefixWord ++ tailWord_6817495) baseStart_6817495 baseEnd_6817495 := by
    simpa [prefixWord, tailWord_6817495, baseEnd_6817495] using wordTrace_append hprefix tailTrace_6817495
  have hstable : (prefixWord ++ tailWord_6817495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817495).length < 2 ^ (prefixWord ++ tailWord_6817495).sum := by decide
  have hdescent : baseEnd_6817495 < baseStart_6817495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817512 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6817512 : Nat := 118140960795 + 6817512 * 2 ^ 59
def prefixEnd_6817512 : Nat := 4983230072969 + 3 ^ 40 * 6817512 * 2
def baseEnd_6817512 : Nat := 3500660523795035686646839

theorem tailTrace_6817512 : CollatzResearch.WordTrace tailWord_6817512 prefixEnd_6817512 3500660523795035686646839 := by
  unfold tailWord_6817512
  simp only [CollatzResearch.WordTrace]
  refine ⟨124327545238662918598499395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165770060318217224797999193 124327545238662918598499395)
  ·
    refine ⟨186491317857994377897749093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124327545238662918598499395 186491317857994377897749093)
    ·
      refine ⟨34967122098373945855827955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186491317857994377897749093 34967122098373945855827955)
      ·
        refine ⟨52450683147560918783741933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34967122098373945855827955 52450683147560918783741933)
        ·
          refine ⟨19669006180335344543903225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52450683147560918783741933 19669006180335344543903225)
          ·
            refine ⟨14751754635251508407927419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19669006180335344543903225 14751754635251508407927419)
            ·
              refine ⟨22127631952877262611891129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14751754635251508407927419 22127631952877262611891129)
              ·
                refine ⟨16595723964657946958918347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22127631952877262611891129 16595723964657946958918347)
                ·
                  refine ⟨24893585946986920438377521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16595723964657946958918347 24893585946986920438377521)
                  ·
                    refine ⟨18670189460240190328783141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24893585946986920438377521 18670189460240190328783141)
                    ·
                      refine ⟨3500660523795035686646839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18670189460240190328783141 3500660523795035686646839)
                      ·
                        rfl

theorem cell23_6817512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6817512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817512 prefixEnd_6817512 := by exact prefixLift 6817512
  have htrace : WordTrace (prefixWord ++ tailWord_6817512) baseStart_6817512 baseEnd_6817512 := by
    simpa [prefixWord, tailWord_6817512, baseEnd_6817512] using wordTrace_append hprefix tailTrace_6817512
  have hstable : (prefixWord ++ tailWord_6817512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817512).length < 2 ^ (prefixWord ++ tailWord_6817512).sum := by decide
  have hdescent : baseEnd_6817512 < baseStart_6817512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817515 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 3]
def baseStart_6817515 : Nat := 118140960795 + 6817515 * 2 ^ 59
def prefixEnd_6817515 : Nat := 4983230072969 + 3 ^ 40 * 6817515 * 2
def baseEnd_6817515 : Nat := 3500662064236999174909325

theorem tailTrace_6817515 : CollatzResearch.WordTrace tailWord_6817515 prefixEnd_6817515 3500662064236999174909325 := by
  unfold tailWord_6817515
  simp only [CollatzResearch.WordTrace]
  refine ⟨248655199896314968709357999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165770133264209979139571999 248655199896314968709357999)
  ·
    refine ⟨372982799844472453064036999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248655199896314968709357999 372982799844472453064036999)
    ·
      refine ⟨559474199766708679596055499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372982799844472453064036999 559474199766708679596055499)
      ·
        refine ⟨839211299650063019394083249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559474199766708679596055499 839211299650063019394083249)
        ·
          refine ⟨629408474737547264545562437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839211299650063019394083249 629408474737547264545562437)
          ·
            refine ⟨118014089013290112102292957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 629408474737547264545562437 118014089013290112102292957)
            ·
              refine ⟨44255283379983792038359859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118014089013290112102292957 44255283379983792038359859)
              ·
                refine ⟨66382925069975688057539789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44255283379983792038359859 66382925069975688057539789)
                ·
                  refine ⟨24893596901240883021577421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66382925069975688057539789 24893596901240883021577421)
                  ·
                    refine ⟨9335098837965331133091533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24893596901240883021577421 9335098837965331133091533)
                    ·
                      refine ⟨3500662064236999174909325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9335098837965331133091533 3500662064236999174909325)
                      ·
                        rfl

theorem cell23_6817515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 3].length) (baseStart_6817515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817515 prefixEnd_6817515 := by exact prefixLift 6817515
  have htrace : WordTrace (prefixWord ++ tailWord_6817515) baseStart_6817515 baseEnd_6817515 := by
    simpa [prefixWord, tailWord_6817515, baseEnd_6817515] using wordTrace_append hprefix tailTrace_6817515
  have hstable : (prefixWord ++ tailWord_6817515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817515).length < 2 ^ (prefixWord ++ tailWord_6817515).sum := by decide
  have hdescent : baseEnd_6817515 < baseStart_6817515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817519 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 1, 2, 3]
def baseStart_6817519 : Nat := 118140960795 + 6817519 * 2 ^ 59
def prefixEnd_6817519 : Nat := 4983230072969 + 3 ^ 40 * 6817519 * 2
def baseEnd_6817519 : Nat := 3500664118159617159259307

theorem tailTrace_6817519 : CollatzResearch.WordTrace tailWord_6817519 prefixEnd_6817519 3500664118159617159259307 := by
  unfold tailWord_6817519
  simp only [CollatzResearch.WordTrace]
  refine ⟨248655345788300477392503611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165770230525533651595002407 248655345788300477392503611)
  ·
    refine ⟨372983018682450716088755417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248655345788300477392503611 372983018682450716088755417)
    ·
      refine ⟨279737264011838037066566563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372983018682450716088755417 279737264011838037066566563)
      ·
        refine ⟨419605896017757055599849845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279737264011838037066566563 419605896017757055599849845)
        ·
          refine ⟨39338052751664723962485923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 419605896017757055599849845 39338052751664723962485923)
          ·
            refine ⟨59007079127497085943728885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39338052751664723962485923 59007079127497085943728885)
            ·
              refine ⟨5531913668202851807224583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59007079127497085943728885 5531913668202851807224583)
              ·
                refine ⟨8297870502304277710836875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5531913668202851807224583 8297870502304277710836875)
                ·
                  refine ⟨12446805753456416566255313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8297870502304277710836875 12446805753456416566255313)
                  ·
                    refine ⟨9335104315092312424691485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12446805753456416566255313 9335104315092312424691485)
                    ·
                      refine ⟨3500664118159617159259307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9335104315092312424691485 3500664118159617159259307)
                      ·
                        rfl

theorem cell23_6817519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 1, 2, 3].length) (baseStart_6817519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817519 prefixEnd_6817519 := by exact prefixLift 6817519
  have htrace : WordTrace (prefixWord ++ tailWord_6817519) baseStart_6817519 baseEnd_6817519 := by
    simpa [prefixWord, tailWord_6817519, baseEnd_6817519] using wordTrace_append hprefix tailTrace_6817519
  have hstable : (prefixWord ++ tailWord_6817519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817519).length < 2 ^ (prefixWord ++ tailWord_6817519).sum := by decide
  have hdescent : baseEnd_6817519 < baseStart_6817519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817559 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 3, 3, 2]
def baseStart_6817559 : Nat := 118140960795 + 6817559 * 2 ^ 59
def prefixEnd_6817559 : Nat := 4983230072969 + 3 ^ 40 * 6817559 * 2
def baseEnd_6817559 : Nat := 3500684657385797002759123

theorem tailTrace_6817559 : CollatzResearch.WordTrace tailWord_6817559 prefixEnd_6817559 3500684657385797002759123 := by
  unfold tailWord_6817559
  simp only [CollatzResearch.WordTrace]
  refine ⟨248656804708155564223959731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165771203138770376149306487 248656804708155564223959731)
  ·
    refine ⟨372985207062233346335939597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248656804708155564223959731 372985207062233346335939597)
    ·
      refine ⟨139869452648337504875977349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372985207062233346335939597 139869452648337504875977349)
      ·
        refine ⟨26225522371563282164245753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139869452648337504875977349 26225522371563282164245753)
        ·
          refine ⟨19669141778672461623184315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26225522371563282164245753 19669141778672461623184315)
          ·
            refine ⟨29503712668008692434776473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19669141778672461623184315 29503712668008692434776473)
            ·
              refine ⟨22127784501006519326082355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29503712668008692434776473 22127784501006519326082355)
              ·
                refine ⟨33191676751509778989123533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22127784501006519326082355 33191676751509778989123533)
                ·
                  refine ⟨12446878781816167120921325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33191676751509778989123533 12446878781816167120921325)
                  ·
                    refine ⟨4667579543181062670345497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12446878781816167120921325 4667579543181062670345497)
                    ·
                      refine ⟨3500684657385797002759123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667579543181062670345497 3500684657385797002759123)
                      ·
                        rfl

theorem cell23_6817559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_6817559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817559 prefixEnd_6817559 := by exact prefixLift 6817559
  have htrace : WordTrace (prefixWord ++ tailWord_6817559) baseStart_6817559 baseEnd_6817559 := by
    simpa [prefixWord, tailWord_6817559, baseEnd_6817559] using wordTrace_append hprefix tailTrace_6817559
  have hstable : (prefixWord ++ tailWord_6817559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817559).length < 2 ^ (prefixWord ++ tailWord_6817559).sum := by decide
  have hdescent : baseEnd_6817559 < baseStart_6817559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817576 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_6817576 : Nat := 118140960795 + 6817576 * 2 ^ 59
def prefixEnd_6817576 : Nat := 4983230072969 + 3 ^ 40 * 6817576 * 2
def baseEnd_6817576 : Nat := 3500693386556923436246545

theorem tailTrace_6817576 : CollatzResearch.WordTrace tailWord_6817576 prefixEnd_6817576 3500693386556923436246545 := by
  unfold tailWord_6817576
  simp only [CollatzResearch.WordTrace]
  refine ⟨124328712374546988063664291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165771616499395984084885721 124328712374546988063664291)
  ·
    refine ⟨186493068561820482095496437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124328712374546988063664291 186493068561820482095496437)
    ·
      refine ⟨17483725177670670196452791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186493068561820482095496437 17483725177670670196452791)
      ·
        refine ⟨26225587766506005294679187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17483725177670670196452791 26225587766506005294679187)
        ·
          refine ⟨39338381649759007942018781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26225587766506005294679187 39338381649759007942018781)
          ·
            refine ⟨14751893118659627978257043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39338381649759007942018781 14751893118659627978257043)
            ·
              refine ⟨22127839677989441967385565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14751893118659627978257043 22127839677989441967385565)
              ·
                refine ⟨8297939879246040737769587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22127839677989441967385565 8297939879246040737769587)
                ·
                  refine ⟨12446909818869061106654381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8297939879246040737769587 12446909818869061106654381)
                  ·
                    refine ⟨4667591182075897914995393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12446909818869061106654381 4667591182075897914995393)
                    ·
                      refine ⟨3500693386556923436246545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667591182075897914995393 3500693386556923436246545)
                      ·
                        rfl

theorem cell23_6817576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_6817576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817576 prefixEnd_6817576 := by exact prefixLift 6817576
  have htrace : WordTrace (prefixWord ++ tailWord_6817576) baseStart_6817576 baseEnd_6817576 := by
    simpa [prefixWord, tailWord_6817576, baseEnd_6817576] using wordTrace_append hprefix tailTrace_6817576
  have hstable : (prefixWord ++ tailWord_6817576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817576).length < 2 ^ (prefixWord ++ tailWord_6817576).sum := by decide
  have hdescent : baseEnd_6817576 < baseStart_6817576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817625 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 1, 7]
def baseStart_6817625 : Nat := 118140960795 + 6817625 * 2 ^ 59
def prefixEnd_6817625 : Nat := 4983230072969 + 3 ^ 40 * 6817625 * 2
def baseEnd_6817625 : Nat := 1166906182369664581511273

theorem tailTrace_6817625 : CollatzResearch.WordTrace tailWord_6817625 prefixEnd_6817625 1166906182369664581511273 := by
  unfold tailWord_6817625
  simp only [CollatzResearch.WordTrace]
  refine ⟨248659211925916457495862329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165772807950610971663908219 248659211925916457495862329)
  ·
    refine ⟨186494408944437343121896747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248659211925916457495862329 186494408944437343121896747)
    ·
      refine ⟨279741613416656014682845121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186494408944437343121896747 279741613416656014682845121)
      ·
        refine ⟨209806210062492011012133841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279741613416656014682845121 209806210062492011012133841)
        ·
          refine ⟨157354657546869008259100381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209806210062492011012133841 157354657546869008259100381)
          ·
            refine ⟨59007996580075878097162643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157354657546869008259100381 59007996580075878097162643)
            ·
              refine ⟨88511994870113817145743965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59007996580075878097162643 88511994870113817145743965)
              ·
                refine ⟨33191998076292681429653987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88511994870113817145743965 33191998076292681429653987)
                ·
                  refine ⟨49787997114439022144480981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33191998076292681429653987 49787997114439022144480981)
                  ·
                    refine ⟨1166906182369664581511273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49787997114439022144480981 1166906182369664581511273)
                    ·
                      rfl

theorem cell23_6817625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_6817625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817625 prefixEnd_6817625 := by exact prefixLift 6817625
  have htrace : WordTrace (prefixWord ++ tailWord_6817625) baseStart_6817625 baseEnd_6817625 := by
    simpa [prefixWord, tailWord_6817625, baseEnd_6817625] using wordTrace_append hprefix tailTrace_6817625
  have hstable : (prefixWord ++ tailWord_6817625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817625).length < 2 ^ (prefixWord ++ tailWord_6817625).sum := by decide
  have hdescent : baseEnd_6817625 < baseStart_6817625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817675 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 6]
def baseStart_6817675 : Nat := 118140960795 + 6817675 * 2 ^ 59
def prefixEnd_6817675 : Nat := 4983230072969 + 3 ^ 40 * 6817675 * 2
def baseEnd_6817675 : Nat := 3500744221141718548908589

theorem tailTrace_6817675 : CollatzResearch.WordTrace tailWord_6817675 prefixEnd_6817675 3500744221141718548908589 := by
  unfold tailWord_6817675
  simp only [CollatzResearch.WordTrace]
  refine ⟨248661035575735316035182479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165774023717156877356788319 248661035575735316035182479)
  ·
    refine ⟨372991553363602974052773719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248661035575735316035182479 372991553363602974052773719)
    ·
      refine ⟨559487330045404461079160579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372991553363602974052773719 559487330045404461079160579)
      ·
        refine ⟨839230995068106691618740869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559487330045404461079160579 839230995068106691618740869)
        ·
          refine ⟨157355811575270004678513913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 839230995068106691618740869 157355811575270004678513913)
          ·
            refine ⟨118016858681452503508885435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157355811575270004678513913 118016858681452503508885435)
            ·
              refine ⟨177025288022178755263328153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118016858681452503508885435 177025288022178755263328153)
              ·
                refine ⟨132768966016634066447496115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177025288022178755263328153 132768966016634066447496115)
                ·
                  refine ⟨199153449024951099671244173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132768966016634066447496115 199153449024951099671244173)
                  ·
                    refine ⟨74682543384356662376716565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199153449024951099671244173 74682543384356662376716565)
                    ·
                      refine ⟨3500744221141718548908589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74682543384356662376716565 3500744221141718548908589)
                      ·
                        rfl

theorem cell23_6817675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_6817675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817675 prefixEnd_6817675 := by exact prefixLift 6817675
  have htrace : WordTrace (prefixWord ++ tailWord_6817675) baseStart_6817675 baseEnd_6817675 := by
    simpa [prefixWord, tailWord_6817675, baseEnd_6817675] using wordTrace_append hprefix tailTrace_6817675
  have hstable : (prefixWord ++ tailWord_6817675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817675).length < 2 ^ (prefixWord ++ tailWord_6817675).sum := by decide
  have hdescent : baseEnd_6817675 < baseStart_6817675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817739 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 1, 5, 2]
def baseStart_6817739 : Nat := 118140960795 + 6817739 * 2 ^ 59
def prefixEnd_6817739 : Nat := 4983230072969 + 3 ^ 40 * 6817739 * 2
def baseEnd_6817739 : Nat := 3500777083903606298508295

theorem tailTrace_6817739 : CollatzResearch.WordTrace tailWord_6817739 prefixEnd_6817739 3500777083903606298508295 := by
  unfold tailWord_6817739
  simp only [CollatzResearch.WordTrace]
  refine ⟨248663369847503454965512271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165775579898335636643674847 248663369847503454965512271)
  ·
    refine ⟨372995054771255182448268407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248663369847503454965512271 372995054771255182448268407)
    ·
      refine ⟨559492582156882773672402611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372995054771255182448268407 559492582156882773672402611)
      ·
        refine ⟨839238873235324160508603917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559492582156882773672402611 839238873235324160508603917)
        ·
          refine ⟨314714577463246560190726469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 839238873235324160508603917 314714577463246560190726469)
          ·
            refine ⟨59008983274358730035761213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 314714577463246560190726469 59008983274358730035761213)
            ·
              refine ⟨22128368727884523763410455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59008983274358730035761213 22128368727884523763410455)
              ·
                refine ⟨33192553091826785645115683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22128368727884523763410455 33192553091826785645115683)
                ·
                  refine ⟨49788829637740178467673525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33192553091826785645115683 49788829637740178467673525)
                  ·
                    refine ⟨4667702778538141731344393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49788829637740178467673525 4667702778538141731344393)
                    ·
                      refine ⟨3500777083903606298508295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667702778538141731344393 3500777083903606298508295)
                      ·
                        rfl

theorem cell23_6817739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 5, 2].length) (baseStart_6817739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817739 prefixEnd_6817739 := by exact prefixLift 6817739
  have htrace : WordTrace (prefixWord ++ tailWord_6817739) baseStart_6817739 baseEnd_6817739 := by
    simpa [prefixWord, tailWord_6817739, baseEnd_6817739] using wordTrace_append hprefix tailTrace_6817739
  have hstable : (prefixWord ++ tailWord_6817739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817739).length < 2 ^ (prefixWord ++ tailWord_6817739).sum := by decide
  have hdescent : baseEnd_6817739 < baseStart_6817739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817763 : List Nat := [1, 1, 1, 6, 1, 2, 2, 4, 1, 1, 3]
def baseStart_6817763 : Nat := 118140960795 + 6817763 * 2 ^ 59
def prefixEnd_6817763 : Nat := 4983230072969 + 3 ^ 40 * 6817763 * 2
def baseEnd_6817763 : Nat := 3500789407439314204608185

theorem tailTrace_6817763 : CollatzResearch.WordTrace tailWord_6817763 prefixEnd_6817763 3500789407439314204608185 := by
  unfold tailWord_6817763
  simp only [CollatzResearch.WordTrace]
  refine ⟨248664245199416507064385943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165776163466277671376257295 248664245199416507064385943)
  ·
    refine ⟨372996367799124760596578915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248664245199416507064385943 372996367799124760596578915)
    ·
      refine ⟨559494551698687140894868373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372996367799124760596578915 559494551698687140894868373)
      ·
        refine ⟨26226307110875959729446955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 559494551698687140894868373 26226307110875959729446955)
        ·
          refine ⟨39339460666313939594170433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26226307110875959729446955 39339460666313939594170433)
          ·
            refine ⟨29504595499735454695627825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39339460666313939594170433 29504595499735454695627825)
            ·
              refine ⟨22128446624801591021720869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29504595499735454695627825 22128446624801591021720869)
              ·
                refine ⟨4149083742150298316572663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22128446624801591021720869 4149083742150298316572663)
                ·
                  refine ⟨6223625613225447474858995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4149083742150298316572663 6223625613225447474858995)
                  ·
                    refine ⟨9335438419838171212288493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6223625613225447474858995 9335438419838171212288493)
                    ·
                      refine ⟨3500789407439314204608185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9335438419838171212288493 3500789407439314204608185)
                      ·
                        rfl

theorem cell23_6817763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_6817763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817763 prefixEnd_6817763 := by exact prefixLift 6817763
  have htrace : WordTrace (prefixWord ++ tailWord_6817763) baseStart_6817763 baseEnd_6817763 := by
    simpa [prefixWord, tailWord_6817763, baseEnd_6817763] using wordTrace_append hprefix tailTrace_6817763
  have hstable : (prefixWord ++ tailWord_6817763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817763).length < 2 ^ (prefixWord ++ tailWord_6817763).sum := by decide
  have hdescent : baseEnd_6817763 < baseStart_6817763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817779 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 2, 4]
def baseStart_6817779 : Nat := 118140960795 + 6817779 * 2 ^ 59
def prefixEnd_6817779 : Nat := 4983230072969 + 3 ^ 40 * 6817779 * 2
def baseEnd_6817779 : Nat := 1166932541043262047336037

theorem tailTrace_6817779 : CollatzResearch.WordTrace tailWord_6817779 prefixEnd_6817779 1166932541043262047336037 := by
  unfold tailWord_6817779
  simp only [CollatzResearch.WordTrace]
  refine ⟨248664828767358541796968391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165776552511572361197978927 248664828767358541796968391)
  ·
    refine ⟨372997243151037812695452587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248664828767358541796968391 372997243151037812695452587)
    ·
      refine ⟨559495864726556719043178881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372997243151037812695452587 559495864726556719043178881)
      ·
        refine ⟨419621898544917539282384161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559495864726556719043178881 419621898544917539282384161)
        ·
          refine ⟨314716423908688154461788121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419621898544917539282384161 314716423908688154461788121)
          ·
            refine ⟨236037317931516115846341091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314716423908688154461788121 236037317931516115846341091)
            ·
              refine ⟨354055976897274173769511637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236037317931516115846341091 354055976897274173769511637)
              ·
                refine ⟨8298186958529863447722929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 354055976897274173769511637 8298186958529863447722929)
                ·
                  refine ⟨6223640218897397585792197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8298186958529863447722929 6223640218897397585792197)
                  ·
                    refine ⟨1166932541043262047336037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6223640218897397585792197 1166932541043262047336037)
                    ·
                      rfl

theorem cell23_6817779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 4].length) (baseStart_6817779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817779 prefixEnd_6817779 := by exact prefixLift 6817779
  have htrace : WordTrace (prefixWord ++ tailWord_6817779) baseStart_6817779 baseEnd_6817779 := by
    simpa [prefixWord, tailWord_6817779, baseEnd_6817779] using wordTrace_append hprefix tailTrace_6817779
  have hstable : (prefixWord ++ tailWord_6817779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817779).length < 2 ^ (prefixWord ++ tailWord_6817779).sum := by decide
  have hdescent : baseEnd_6817779 < baseStart_6817779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817789 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_6817789 : Nat := 118140960795 + 6817789 * 2 ^ 59
def prefixEnd_6817789 : Nat := 4983230072969 + 3 ^ 40 * 6817789 * 2
def baseEnd_6817789 : Nat := 3500802757936331102883065

theorem tailTrace_6817789 : CollatzResearch.WordTrace tailWord_6817789 prefixEnd_6817789 3500802757936331102883065 := by
  unfold tailWord_6817789
  simp only [CollatzResearch.WordTrace]
  refine ⟨248665193497322313504832421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165776795664881542336554947 248665193497322313504832421)
  ·
    refine ⟨46624723780747933782156079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248665193497322313504832421 46624723780747933782156079)
    ·
      refine ⟨69937085671121900673234119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46624723780747933782156079 69937085671121900673234119)
      ·
        refine ⟨104905628506682851009851179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69937085671121900673234119 104905628506682851009851179)
        ·
          refine ⟨157358442760024276514776769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104905628506682851009851179 157358442760024276514776769)
          ·
            refine ⟨118018832070018207386082577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157358442760024276514776769 118018832070018207386082577)
            ·
              refine ⟨88514124052513655539561933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118018832070018207386082577 88514124052513655539561933)
              ·
                refine ⟨33192796519692620827335725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88514124052513655539561933 33192796519692620827335725)
                ·
                  refine ⟨12447298694884732810250897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33192796519692620827335725 12447298694884732810250897)
                  ·
                    refine ⟨9335474021163549607688173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12447298694884732810250897 9335474021163549607688173)
                    ·
                      refine ⟨3500802757936331102883065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9335474021163549607688173 3500802757936331102883065)
                      ·
                        rfl

theorem cell23_6817789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_6817789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817789 prefixEnd_6817789 := by exact prefixLift 6817789
  have htrace : WordTrace (prefixWord ++ tailWord_6817789) baseStart_6817789 baseEnd_6817789 := by
    simpa [prefixWord, tailWord_6817789, baseEnd_6817789] using wordTrace_append hprefix tailTrace_6817789
  have hstable : (prefixWord ++ tailWord_6817789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817789).length < 2 ^ (prefixWord ++ tailWord_6817789).sum := by decide
  have hdescent : baseEnd_6817789 < baseStart_6817789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817806 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_6817806 : Nat := 118140960795 + 6817806 * 2 ^ 59
def prefixEnd_6817806 : Nat := 4983230072969 + 3 ^ 40 * 6817806 * 2
def baseEnd_6817806 : Nat := 3500811487107457536370487

theorem tailTrace_6817806 : CollatzResearch.WordTrace tailWord_6817806 prefixEnd_6817806 3500811487107457536370487 := by
  unfold tailWord_6817806
  simp only [CollatzResearch.WordTrace]
  refine ⟨31083226692282590676025159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165777209025507150272134181 31083226692282590676025159)
  ·
    refine ⟨46624840038423886014037739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31083226692282590676025159 46624840038423886014037739)
    ·
      refine ⟨69937260057635829021056609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46624840038423886014037739 69937260057635829021056609)
      ·
        refine ⟨52452945043226871765792457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69937260057635829021056609 52452945043226871765792457)
        ·
          refine ⟨39339708782420153824344343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52452945043226871765792457 39339708782420153824344343)
          ·
            refine ⟨59009563173630230736516515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39339708782420153824344343 59009563173630230736516515)
            ·
              refine ⟨88514344760445346104774773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59009563173630230736516515 88514344760445346104774773)
              ·
                refine ⟨8298219821291751197322635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88514344760445346104774773 8298219821291751197322635)
                ·
                  refine ⟨12447329731937626795983953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8298219821291751197322635 12447329731937626795983953)
                  ·
                    refine ⟨9335497298953220096987965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12447329731937626795983953 9335497298953220096987965)
                    ·
                      refine ⟨3500811487107457536370487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9335497298953220096987965 3500811487107457536370487)
                      ·
                        rfl

theorem cell23_6817806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_6817806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817806 prefixEnd_6817806 := by exact prefixLift 6817806
  have htrace : WordTrace (prefixWord ++ tailWord_6817806) baseStart_6817806 baseEnd_6817806 := by
    simpa [prefixWord, tailWord_6817806, baseEnd_6817806] using wordTrace_append hprefix tailTrace_6817806
  have hstable : (prefixWord ++ tailWord_6817806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817806).length < 2 ^ (prefixWord ++ tailWord_6817806).sum := by decide
  have hdescent : baseEnd_6817806 < baseStart_6817806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817820 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_6817820 : Nat := 118140960795 + 6817820 * 2 ^ 59
def prefixEnd_6817820 : Nat := 4983230072969 + 3 ^ 40 * 6817820 * 2
def baseEnd_6817820 : Nat := 3500818675836620481595423

theorem tailTrace_6817820 : CollatzResearch.WordTrace tailWord_6817820 prefixEnd_6817820 3500818675836620481595423 := by
  unfold tailWord_6817820
  simp only [CollatzResearch.WordTrace]
  refine ⟨124333162080105002899605457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165777549440140003866140609 124333162080105002899605457)
  ·
    refine ⟨93249871560078752174704093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124333162080105002899605457 93249871560078752174704093)
    ·
      refine ⟨34968701835029532065514035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93249871560078752174704093 34968701835029532065514035)
      ·
        refine ⟨52453052752544298098271053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34968701835029532065514035 52453052752544298098271053)
        ·
          refine ⟨19669894782204111786851645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52453052752544298098271053 19669894782204111786851645)
          ·
            refine ⟨7376210543326541920069367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19669894782204111786851645 7376210543326541920069367)
            ·
              refine ⟨11064315814989812880104051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7376210543326541920069367 11064315814989812880104051)
              ·
                refine ⟨16596473722484719320156077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11064315814989812880104051 16596473722484719320156077)
                ·
                  refine ⟨6223677645931769745058529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16596473722484719320156077 6223677645931769745058529)
                  ·
                    refine ⟨4667758234448827308793897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6223677645931769745058529 4667758234448827308793897)
                    ·
                      refine ⟨3500818675836620481595423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667758234448827308793897 3500818675836620481595423)
                      ·
                        rfl

theorem cell23_6817820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_6817820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817820 prefixEnd_6817820 := by exact prefixLift 6817820
  have htrace : WordTrace (prefixWord ++ tailWord_6817820) baseStart_6817820 baseEnd_6817820 := by
    simpa [prefixWord, tailWord_6817820, baseEnd_6817820] using wordTrace_append hprefix tailTrace_6817820
  have hstable : (prefixWord ++ tailWord_6817820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817820).length < 2 ^ (prefixWord ++ tailWord_6817820).sum := by decide
  have hdescent : baseEnd_6817820 < baseStart_6817820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817872 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_6817872 : Nat := 118140960795 + 6817872 * 2 ^ 59
def prefixEnd_6817872 : Nat := 4983230072969 + 3 ^ 40 * 6817872 * 2
def baseEnd_6817872 : Nat := 3500845376830654278145183

theorem tailTrace_6817872 : CollatzResearch.WordTrace tailWord_6817872 prefixEnd_6817872 3500845376830654278145183 := by
  unfold tailWord_6817872
  simp only [CollatzResearch.WordTrace]
  refine ⟨124334110378010809340051935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165778813837347745786735913 124334110378010809340051935)
  ·
    refine ⟨186501165567016214010077903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124334110378010809340051935 186501165567016214010077903)
    ·
      refine ⟨279751748350524321015116855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186501165567016214010077903 279751748350524321015116855)
      ·
        refine ⟨419627622525786481522675283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279751748350524321015116855 419627622525786481522675283)
        ·
          refine ⟨629441433788679722284012925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419627622525786481522675283 629441433788679722284012925)
          ·
            refine ⟨236040537670754895856504847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 629441433788679722284012925 236040537670754895856504847)
            ·
              refine ⟨354060806506132343784757271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236040537670754895856504847 354060806506132343784757271)
              ·
                refine ⟨531091209759198515677135907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354060806506132343784757271 531091209759198515677135907)
                ·
                  refine ⟨796636814638797773515703861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531091209759198515677135907 796636814638797773515703861)
                  ·
                    refine ⟨74684701372387291267097237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 796636814638797773515703861 74684701372387291267097237)
                    ·
                      refine ⟨3500845376830654278145183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74684701372387291267097237 3500845376830654278145183)
                      ·
                        rfl

theorem cell23_6817872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_6817872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817872 prefixEnd_6817872 := by exact prefixLift 6817872
  have htrace : WordTrace (prefixWord ++ tailWord_6817872) baseStart_6817872 baseEnd_6817872 := by
    simpa [prefixWord, tailWord_6817872, baseEnd_6817872] using wordTrace_append hprefix tailTrace_6817872
  have hstable : (prefixWord ++ tailWord_6817872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817872).length < 2 ^ (prefixWord ++ tailWord_6817872).sum := by decide
  have hdescent : baseEnd_6817872 < baseStart_6817872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817876 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_6817876 : Nat := 118140960795 + 6817876 * 2 ^ 59
def prefixEnd_6817876 : Nat := 4983230072969 + 3 ^ 40 * 6817876 * 2
def baseEnd_6817876 : Nat := 3500847430753272262495165

theorem tailTrace_6817876 : CollatzResearch.WordTrace tailWord_6817876 prefixEnd_6817876 3500847430753272262495165 := by
  unfold tailWord_6817876
  simp only [CollatzResearch.WordTrace]
  refine ⟨124334183324003563681624741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165778911098671418242166321 124334183324003563681624741)
  ·
    refine ⟨23312659373250668190304639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124334183324003563681624741 23312659373250668190304639)
    ·
      refine ⟨34968989059876002285456959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23312659373250668190304639 34968989059876002285456959)
      ·
        refine ⟨52453483589814003428185439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34968989059876002285456959 52453483589814003428185439)
        ·
          refine ⟨78680225384721005142278159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52453483589814003428185439 78680225384721005142278159)
          ·
            refine ⟨118020338077081507713417239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78680225384721005142278159 118020338077081507713417239)
            ·
              refine ⟨177030507115622261570125859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118020338077081507713417239 177030507115622261570125859)
              ·
                refine ⟨265545760673433392355188789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177030507115622261570125859 265545760673433392355188789)
                ·
                  refine ⟨24894915063134380533298949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 265545760673433392355188789 24894915063134380533298949)
                  ·
                    refine ⟨4667796574337696349993553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24894915063134380533298949 4667796574337696349993553)
                    ·
                      refine ⟨3500847430753272262495165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667796574337696349993553 3500847430753272262495165)
                      ·
                        rfl

theorem cell23_6817876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_6817876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817876 prefixEnd_6817876 := by exact prefixLift 6817876
  have htrace : WordTrace (prefixWord ++ tailWord_6817876) baseStart_6817876 baseEnd_6817876 := by
    simpa [prefixWord, tailWord_6817876, baseEnd_6817876] using wordTrace_append hprefix tailTrace_6817876
  have hstable : (prefixWord ++ tailWord_6817876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817876).length < 2 ^ (prefixWord ++ tailWord_6817876).sum := by decide
  have hdescent : baseEnd_6817876 < baseStart_6817876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817879 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 3]
def baseStart_6817879 : Nat := 118140960795 + 6817879 * 2 ^ 59
def prefixEnd_6817879 : Nat := 4983230072969 + 3 ^ 40 * 6817879 * 2
def baseEnd_6817879 : Nat := 3500848971195235750757651

theorem tailTrace_6817879 : CollatzResearch.WordTrace tailWord_6817879 prefixEnd_6817879 3500848971195235750757651 := by
  unfold tailWord_6817879
  simp only [CollatzResearch.WordTrace]
  refine ⟨248668476066996258875608691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165778984044664172583739127 248668476066996258875608691)
  ·
    refine ⟨373002714100494388313413037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248668476066996258875608691 373002714100494388313413037)
    ·
      refine ⟨139876017787685395617529889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373002714100494388313413037 139876017787685395617529889)
      ·
        refine ⟨104907013340764046713147417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139876017787685395617529889 104907013340764046713147417)
        ·
          refine ⟨78680260005573035034860563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104907013340764046713147417 78680260005573035034860563)
          ·
            refine ⟨118020390008359552552290845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78680260005573035034860563 118020390008359552552290845)
            ·
              refine ⟨44257646253134832207109067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118020390008359552552290845 44257646253134832207109067)
              ·
                refine ⟨66386469379702248310663601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44257646253134832207109067 66386469379702248310663601)
                ·
                  refine ⟨49789852034776686232997701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66386469379702248310663601 49789852034776686232997701)
                  ·
                    refine ⟨9335597256520628668687069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49789852034776686232997701 9335597256520628668687069)
                    ·
                      refine ⟨3500848971195235750757651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9335597256520628668687069 3500848971195235750757651)
                      ·
                        rfl

theorem cell23_6817879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_6817879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817879 prefixEnd_6817879 := by exact prefixLift 6817879
  have htrace : WordTrace (prefixWord ++ tailWord_6817879) baseStart_6817879 baseEnd_6817879 := by
    simpa [prefixWord, tailWord_6817879, baseEnd_6817879] using wordTrace_append hprefix tailTrace_6817879
  have hstable : (prefixWord ++ tailWord_6817879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817879).length < 2 ^ (prefixWord ++ tailWord_6817879).sum := by decide
  have hdescent : baseEnd_6817879 < baseStart_6817879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817893 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 1, 4, 2]
def baseStart_6817893 : Nat := 118140960795 + 6817893 * 2 ^ 59
def prefixEnd_6817893 : Nat := 4983230072969 + 3 ^ 40 * 6817893 * 2
def baseEnd_6817893 : Nat := 3500856159924398695982587

theorem tailTrace_6817893 : CollatzResearch.WordTrace tailWord_6817893 prefixEnd_6817893 3500856159924398695982587 := by
  unfold tailWord_6817893
  simp only [CollatzResearch.WordTrace]
  refine ⟨248668986688945539266618333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165779324459297026177745555 248668986688945539266618333)
  ·
    refine ⟨93250870008354577224981875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248668986688945539266618333 93250870008354577224981875)
    ·
      refine ⟨139876305012531865837472813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93250870008354577224981875 139876305012531865837472813)
      ·
        refine ⟨52453614379699449689052305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139876305012531865837472813 52453614379699449689052305)
        ·
          refine ⟨39340210784774587266789229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52453614379699449689052305 39340210784774587266789229)
          ·
            refine ⟨14752579044290470225045961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39340210784774587266789229 14752579044290470225045961)
            ·
              refine ⟨11064434283217852668784471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14752579044290470225045961 11064434283217852668784471)
              ·
                refine ⟨16596651424826779003176707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11064434283217852668784471 16596651424826779003176707)
                ·
                  refine ⟨24894977137240168504765061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16596651424826779003176707 24894977137240168504765061)
                  ·
                    refine ⟨4667808213232531594643449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24894977137240168504765061 4667808213232531594643449)
                    ·
                      refine ⟨3500856159924398695982587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667808213232531594643449 3500856159924398695982587)
                      ·
                        rfl

theorem cell23_6817893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_6817893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817893 prefixEnd_6817893 := by exact prefixLift 6817893
  have htrace : WordTrace (prefixWord ++ tailWord_6817893) baseStart_6817893 baseEnd_6817893 := by
    simpa [prefixWord, tailWord_6817893, baseEnd_6817893] using wordTrace_append hprefix tailTrace_6817893
  have hstable : (prefixWord ++ tailWord_6817893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817893).length < 2 ^ (prefixWord ++ tailWord_6817893).sum := by decide
  have hdescent : baseEnd_6817893 < baseStart_6817893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817916 : List Nat := [2, 2, 2, 1, 1, 4, 1, 5, 5]
def baseStart_6817916 : Nat := 118140960795 + 6817916 * 2 ^ 59
def prefixEnd_6817916 : Nat := 4983230072969 + 3 ^ 40 * 6817916 * 2
def baseEnd_6817916 : Nat := 388985329997716900666109

theorem tailTrace_6817916 : CollatzResearch.WordTrace tailWord_6817916 prefixEnd_6817916 388985329997716900666109 := by
  unfold tailWord_6817916
  simp only [CollatzResearch.WordTrace]
  refine ⟨124334912783931107097352801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165779883711908142796470401 124334912783931107097352801)
  ·
    refine ⟨93251184587948330323014601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124334912783931107097352801 93251184587948330323014601)
    ·
      refine ⟨69938388440961247742260951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93251184587948330323014601 69938388440961247742260951)
      ·
        refine ⟨104907582661441871613391427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69938388440961247742260951 104907582661441871613391427)
        ·
          refine ⟨157361373992162807420087141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104907582661441871613391427 157361373992162807420087141)
          ·
            refine ⟨29505257623530526391266339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157361373992162807420087141 29505257623530526391266339)
            ·
              refine ⟨44257886435295789586899509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29505257623530526391266339 44257886435295789586899509)
              ·
                refine ⟨4149176853308980273771829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44257886435295789586899509 4149176853308980273771829)
                ·
                  refine ⟨388985329997716900666109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4149176853308980273771829 388985329997716900666109)
                  ·
                    rfl

theorem cell23_6817916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_6817916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817916 prefixEnd_6817916 := by exact prefixLift 6817916
  have htrace : WordTrace (prefixWord ++ tailWord_6817916) baseStart_6817916 baseEnd_6817916 := by
    simpa [prefixWord, tailWord_6817916, baseEnd_6817916] using wordTrace_append hprefix tailTrace_6817916
  have hstable : (prefixWord ++ tailWord_6817916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817916).length < 2 ^ (prefixWord ++ tailWord_6817916).sum := by decide
  have hdescent : baseEnd_6817916 < baseStart_6817916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817929 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 4, 5]
def baseStart_6817929 : Nat := 118140960795 + 6817929 * 2 ^ 59
def prefixEnd_6817929 : Nat := 4983230072969 + 3 ^ 40 * 6817929 * 2
def baseEnd_6817929 : Nat := 1166958215075986851710807

theorem tailTrace_6817929 : CollatzResearch.WordTrace tailWord_6817929 prefixEnd_6817929 1166958215075986851710807 := by
  unfold tailWord_6817929
  simp only [CollatzResearch.WordTrace]
  refine ⟨248670299716815117414928841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165780199811210078276619227 248670299716815117414928841)
  ·
    refine ⟨186502724787611338061196631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248670299716815117414928841 186502724787611338061196631)
    ·
      refine ⟨279754087181417007091794947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186502724787611338061196631 279754087181417007091794947)
      ·
        refine ⟨419631130772125510637692421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279754087181417007091794947 419631130772125510637692421)
        ·
          refine ⟨78680837019773533244567329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 419631130772125510637692421 78680837019773533244567329)
          ·
            refine ⟨59010627764830149933425497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78680837019773533244567329 59010627764830149933425497)
            ·
              refine ⟨44257970823622612450069123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59010627764830149933425497 44257970823622612450069123)
              ·
                refine ⟨66386956235433918675103685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44257970823622612450069123 66386956235433918675103685)
                ·
                  refine ⟨12447554294143859751581941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66386956235433918675103685 12447554294143859751581941)
                  ·
                    refine ⟨1166958215075986851710807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12447554294143859751581941 1166958215075986851710807)
                    ·
                      rfl

theorem cell23_6817929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_6817929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817929 prefixEnd_6817929 := by exact prefixLift 6817929
  have htrace : WordTrace (prefixWord ++ tailWord_6817929) baseStart_6817929 baseEnd_6817929 := by
    simpa [prefixWord, tailWord_6817929, baseEnd_6817929] using wordTrace_append hprefix tailTrace_6817929
  have hstable : (prefixWord ++ tailWord_6817929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817929).length < 2 ^ (prefixWord ++ tailWord_6817929).sum := by decide
  have hdescent : baseEnd_6817929 < baseStart_6817929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817989 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 8]
def baseStart_6817989 : Nat := 118140960795 + 6817989 * 2 ^ 59
def prefixEnd_6817989 : Nat := 4983230072969 + 3 ^ 40 * 6817989 * 2
def baseEnd_6817989 : Nat := 388989494896358924486905

theorem tailTrace_6817989 : CollatzResearch.WordTrace tailWord_6817989 prefixEnd_6817989 388989494896358924486905 := by
  unfold tailWord_6817989
  simp only [CollatzResearch.WordTrace]
  refine ⟨248672488096597747662113021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165781658731065165108075347 248672488096597747662113021)
  ·
    refine ⟨93252183036224155373292383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248672488096597747662113021 93252183036224155373292383)
    ·
      refine ⟨139878274554336233059938575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93252183036224155373292383 139878274554336233059938575)
      ·
        refine ⟨209817411831504349589907863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139878274554336233059938575 209817411831504349589907863)
        ·
          refine ⟨314726117747256524384861795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209817411831504349589907863 314726117747256524384861795)
          ·
            refine ⟨472089176620884786577292693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314726117747256524384861795 472089176620884786577292693)
            ·
              refine ⟨22129180154103974370810595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 472089176620884786577292693 22129180154103974370810595)
              ·
                refine ⟨33193770231155961556215893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22129180154103974370810595 33193770231155961556215893)
                ·
                  refine ⟨388989494896358924486905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33193770231155961556215893 388989494896358924486905)
                  ·
                    rfl

theorem cell23_6817989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_6817989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817989 prefixEnd_6817989 := by exact prefixLift 6817989
  have htrace : WordTrace (prefixWord ++ tailWord_6817989) baseStart_6817989 baseEnd_6817989 := by
    simpa [prefixWord, tailWord_6817989, baseEnd_6817989] using wordTrace_append hprefix tailTrace_6817989
  have hstable : (prefixWord ++ tailWord_6817989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817989).length < 2 ^ (prefixWord ++ tailWord_6817989).sum := by decide
  have hdescent : baseEnd_6817989 < baseStart_6817989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818009 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_6818009 : Nat := 118140960795 + 6818009 * 2 ^ 59
def prefixEnd_6818009 : Nat := 4983230072969 + 3 ^ 40 * 6818009 * 2
def baseEnd_6818009 : Nat := 3500915723680320242132053

theorem tailTrace_6818009 : CollatzResearch.WordTrace tailWord_6818009 prefixEnd_6818009 3500915723680320242132053 := by
  unfold tailWord_6818009
  simp only [CollatzResearch.WordTrace]
  refine ⟨248673217556525291077841081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165782145037683527385227387 248673217556525291077841081)
  ·
    refine ⟨186504913167393968308380811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248673217556525291077841081 186504913167393968308380811)
    ·
      refine ⟨279757369751090952462571217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186504913167393968308380811 279757369751090952462571217)
      ·
        refine ⟨209818027313318214346928413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279757369751090952462571217 209818027313318214346928413)
        ·
          refine ⟨78681760242494330380098155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209818027313318214346928413 78681760242494330380098155)
          ·
            refine ⟨118022640363741495570147233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78681760242494330380098155 118022640363741495570147233)
            ·
              refine ⟨88516980272806121677610425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118022640363741495570147233 88516980272806121677610425)
              ·
                refine ⟨66387735204604591258207819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88516980272806121677610425 66387735204604591258207819)
                ·
                  refine ⟨99581602806906886887311729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66387735204604591258207819 99581602806906886887311729)
                  ·
                    refine ⟨74686202105180165165483797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99581602806906886887311729 74686202105180165165483797)
                    ·
                      refine ⟨3500915723680320242132053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74686202105180165165483797 3500915723680320242132053)
                      ·
                        rfl

theorem cell23_6818009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_6818009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818009 prefixEnd_6818009 := by exact prefixLift 6818009
  have htrace : WordTrace (prefixWord ++ tailWord_6818009) baseStart_6818009 baseEnd_6818009 := by
    simpa [prefixWord, tailWord_6818009, baseEnd_6818009] using wordTrace_append hprefix tailTrace_6818009
  have hstable : (prefixWord ++ tailWord_6818009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818009).length < 2 ^ (prefixWord ++ tailWord_6818009).sum := by decide
  have hdescent : baseEnd_6818009 < baseStart_6818009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818100 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_6818100 : Nat := 118140960795 + 6818100 * 2 ^ 59
def prefixEnd_6818100 : Nat := 4983230072969 + 3 ^ 40 * 6818100 * 2
def baseEnd_6818100 : Nat := 1166987483473293128698045

theorem tailTrace_6818100 : CollatzResearch.WordTrace tailWord_6818100 prefixEnd_6818100 1166987483473293128698045 := by
  unfold tailWord_6818100
  simp only [CollatzResearch.WordTrace]
  refine ⟨124338268299597806809701877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165784357732797075746269169 124338268299597806809701877)
  ·
    refine ⟨11656712653087294388409551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124338268299597806809701877 11656712653087294388409551)
    ·
      refine ⟨17485068979630941582614327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11656712653087294388409551 17485068979630941582614327)
      ·
        refine ⟨26227603469446412373921491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17485068979630941582614327 26227603469446412373921491)
        ·
          refine ⟨39341405204169618560882237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26227603469446412373921491 39341405204169618560882237)
          ·
            refine ⟨14753026951563606960330839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39341405204169618560882237 14753026951563606960330839)
            ·
              refine ⟨22129540427345410440496259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14753026951563606960330839 22129540427345410440496259)
              ·
                refine ⟨33194310641018115660744389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22129540427345410440496259 33194310641018115660744389)
                ·
                  refine ⟨6223933245190896686389573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33194310641018115660744389 6223933245190896686389573)
                  ·
                    refine ⟨1166987483473293128698045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6223933245190896686389573 1166987483473293128698045)
                    ·
                      rfl

theorem cell23_6818100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_6818100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818100 prefixEnd_6818100 := by exact prefixLift 6818100
  have htrace : WordTrace (prefixWord ++ tailWord_6818100) baseStart_6818100 baseEnd_6818100 := by
    simpa [prefixWord, tailWord_6818100, baseEnd_6818100] using wordTrace_append hprefix tailTrace_6818100
  have hstable : (prefixWord ++ tailWord_6818100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818100).length < 2 ^ (prefixWord ++ tailWord_6818100).sum := by decide
  have hdescent : baseEnd_6818100 < baseStart_6818100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818163 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 3, 4, 2]
def baseStart_6818163 : Nat := 118140960795 + 6818163 * 2 ^ 59
def prefixEnd_6818163 : Nat := 4983230072969 + 3 ^ 40 * 6818163 * 2
def baseEnd_6818163 : Nat := 3500994799701112639606345

theorem tailTrace_6818163 : CollatzResearch.WordTrace tailWord_6818163 prefixEnd_6818163 3500994799701112639606345 := by
  unfold tailWord_6818163
  simp only [CollatzResearch.WordTrace]
  refine ⟨248678834397967375378947143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165785889598644916919298095 248678834397967375378947143)
  ·
    refine ⟨373018251596951063068420715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248678834397967375378947143 373018251596951063068420715)
    ·
      refine ⟨559527377395426594602631073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373018251596951063068420715 559527377395426594602631073)
      ·
        refine ⟨419645533046569945951973305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559527377395426594602631073 419645533046569945951973305)
        ·
          refine ⟨314734149784927459463979979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419645533046569945951973305 314734149784927459463979979)
          ·
            refine ⟨472101224677391189195969969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314734149784927459463979979 472101224677391189195969969)
            ·
              refine ⟨354075918508043391896977477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472101224677391189195969969 354075918508043391896977477)
              ·
                refine ⟨66389234720258135980683277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354075918508043391896977477 66389234720258135980683277)
                ·
                  refine ⟨24895963020096800992756229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66389234720258135980683277 24895963020096800992756229)
                  ·
                    refine ⟨4667993066268150186141793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24895963020096800992756229 4667993066268150186141793)
                    ·
                      refine ⟨3500994799701112639606345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667993066268150186141793 3500994799701112639606345)
                      ·
                        rfl

theorem cell23_6818163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 4, 2].length) (baseStart_6818163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818163 prefixEnd_6818163 := by exact prefixLift 6818163
  have htrace : WordTrace (prefixWord ++ tailWord_6818163) baseStart_6818163 baseEnd_6818163 := by
    simpa [prefixWord, tailWord_6818163, baseEnd_6818163] using wordTrace_append hprefix tailTrace_6818163
  have hstable : (prefixWord ++ tailWord_6818163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818163).length < 2 ^ (prefixWord ++ tailWord_6818163).sum := by decide
  have hdescent : baseEnd_6818163 < baseStart_6818163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818180 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_6818180 : Nat := 118140960795 + 6818180 * 2 ^ 59
def prefixEnd_6818180 : Nat := 4983230072969 + 3 ^ 40 * 6818180 * 2
def baseEnd_6818180 : Nat := 3501003528872239073093767

theorem tailTrace_6818180 : CollatzResearch.WordTrace tailWord_6818180 prefixEnd_6818180 3501003528872239073093767 := by
  unfold tailWord_6818180
  simp only [CollatzResearch.WordTrace]
  refine ⟨124339727219452893641157997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165786302959270524854877329 124339727219452893641157997)
  ·
    refine ⟨46627397707294835115434249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124339727219452893641157997 46627397707294835115434249)
    ·
      refine ⟨34970548280471126336575687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46627397707294835115434249 34970548280471126336575687)
      ·
        refine ⟨52455822420706689504863531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34970548280471126336575687 52455822420706689504863531)
        ·
          refine ⟨78683733631060034257295297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52455822420706689504863531 78683733631060034257295297)
          ·
            refine ⟨59012800223295025692971473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78683733631060034257295297 59012800223295025692971473)
            ·
              refine ⟨44259600167471269269728605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59012800223295025692971473 44259600167471269269728605)
              ·
                refine ⟨16597350062801725976148227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44259600167471269269728605 16597350062801725976148227)
                ·
                  refine ⟨24896025094202588964222341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16597350062801725976148227 24896025094202588964222341)
                  ·
                    refine ⟨4668004705162985430791689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24896025094202588964222341 4668004705162985430791689)
                    ·
                      refine ⟨3501003528872239073093767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668004705162985430791689 3501003528872239073093767)
                      ·
                        rfl

theorem cell23_6818180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_6818180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818180 prefixEnd_6818180 := by exact prefixLift 6818180
  have htrace : WordTrace (prefixWord ++ tailWord_6818180) baseStart_6818180 baseEnd_6818180 := by
    simpa [prefixWord, tailWord_6818180, baseEnd_6818180] using wordTrace_append hprefix tailTrace_6818180
  have hstable : (prefixWord ++ tailWord_6818180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818180).length < 2 ^ (prefixWord ++ tailWord_6818180).sum := by decide
  have hdescent : baseEnd_6818180 < baseStart_6818180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818213 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 2, 3, 3]
def baseStart_6818213 : Nat := 118140960795 + 6818213 * 2 ^ 59
def prefixEnd_6818213 : Nat := 4983230072969 + 3 ^ 40 * 6818213 * 2
def baseEnd_6818213 : Nat := 3501020473733837443981115

theorem tailTrace_6818213 : CollatzResearch.WordTrace tailWord_6818213 prefixEnd_6818213 3501020473733837443981115 := by
  unfold tailWord_6818213
  simp only [CollatzResearch.WordTrace]
  refine ⟨248680658047786233918267293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165787105365190822612178195 248680658047786233918267293)
  ·
    refine ⟨93255246767919837719350235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248680658047786233918267293 93255246767919837719350235)
    ·
      refine ⟨139882870151879756579025353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93255246767919837719350235 139882870151879756579025353)
      ·
        refine ⟨104912152613909817434269015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139882870151879756579025353 104912152613909817434269015)
        ·
          refine ⟨157368228920864726151403523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104912152613909817434269015 157368228920864726151403523)
          ·
            refine ⟨236052343381297089227105285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157368228920864726151403523 236052343381297089227105285)
            ·
              refine ⟨44259814383993204230082241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236052343381297089227105285 44259814383993204230082241)
              ·
                refine ⟨33194860787994903172561681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44259814383993204230082241 33194860787994903172561681)
                ·
                  refine ⟨24896145590996177379421261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33194860787994903172561681 24896145590996177379421261)
                  ·
                    refine ⟨9336054596623566517282973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24896145590996177379421261 9336054596623566517282973)
                    ·
                      refine ⟨3501020473733837443981115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9336054596623566517282973 3501020473733837443981115)
                      ·
                        rfl

theorem cell23_6818213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_6818213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818213 prefixEnd_6818213 := by exact prefixLift 6818213
  have htrace : WordTrace (prefixWord ++ tailWord_6818213) baseStart_6818213 baseEnd_6818213 := by
    simpa [prefixWord, tailWord_6818213, baseEnd_6818213] using wordTrace_append hprefix tailTrace_6818213
  have hstable : (prefixWord ++ tailWord_6818213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818213).length < 2 ^ (prefixWord ++ tailWord_6818213).sum := by decide
  have hdescent : baseEnd_6818213 < baseStart_6818213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818256 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_6818256 : Nat := 118140960795 + 6818256 * 2 ^ 59
def prefixEnd_6818256 : Nat := 4983230072969 + 3 ^ 40 * 6818256 * 2
def baseEnd_6818256 : Nat := 3501042553401980775743417

theorem tailTrace_6818256 : CollatzResearch.WordTrace tailWord_6818256 prefixEnd_6818256 3501042553401980775743417 := by
  unfold tailWord_6818256
  simp only [CollatzResearch.WordTrace]
  refine ⟨124341113193315226131041311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165788150924420301508055081 124341113193315226131041311)
  ·
    refine ⟨186511669789972839196561967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124341113193315226131041311 186511669789972839196561967)
    ·
      refine ⟨279767504684959258794842951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186511669789972839196561967 279767504684959258794842951)
      ·
        refine ⟨419651257027438888192264427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279767504684959258794842951 419651257027438888192264427)
        ·
          refine ⟨629476885541158332288396641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419651257027438888192264427 629476885541158332288396641)
          ·
            refine ⟨472107664155868749216297481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629476885541158332288396641 472107664155868749216297481)
            ·
              refine ⟨354080748116901561912223111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472107664155868749216297481 354080748116901561912223111)
              ·
                refine ⟨531121122175352342868334667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354080748116901561912223111 531121122175352342868334667)
                ·
                  refine ⟨796681683263028514302502001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531121122175352342868334667 796681683263028514302502001)
                  ·
                    refine ⟨597511262447271385726876501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 796681683263028514302502001 597511262447271385726876501)
                    ·
                      refine ⟨3501042553401980775743417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 597511262447271385726876501 3501042553401980775743417)
                      ·
                        rfl

theorem cell23_6818256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_6818256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818256 prefixEnd_6818256 := by exact prefixLift 6818256
  have htrace : WordTrace (prefixWord ++ tailWord_6818256) baseStart_6818256 baseEnd_6818256 := by
    simpa [prefixWord, tailWord_6818256, baseEnd_6818256] using wordTrace_append hprefix tailTrace_6818256
  have hstable : (prefixWord ++ tailWord_6818256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818256).length < 2 ^ (prefixWord ++ tailWord_6818256).sum := by decide
  have hdescent : baseEnd_6818256 < baseStart_6818256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818280 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 3, 4]
def baseStart_6818280 : Nat := 118140960795 + 6818280 * 2 ^ 59
def prefixEnd_6818280 : Nat := 4983230072969 + 3 ^ 40 * 6818280 * 2
def baseEnd_6818280 : Nat := 1167018292312562893947769

theorem tailTrace_6818280 : CollatzResearch.WordTrace tailWord_6818280 prefixEnd_6818280 1167018292312562893947769 := by
  unfold tailWord_6818280
  simp only [CollatzResearch.WordTrace]
  refine ⟨124341550869271752180478147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165788734492362336240637529 124341550869271752180478147)
  ·
    refine ⟨186512326303907628270717221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124341550869271752180478147 186512326303907628270717221)
    ·
      refine ⟨34971061181982680300759479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186512326303907628270717221 34971061181982680300759479)
      ·
        refine ⟨52456591772974020451139219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34971061181982680300759479 52456591772974020451139219)
        ·
          refine ⟨78684887659461030676708829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52456591772974020451139219 78684887659461030676708829)
          ·
            refine ⟨29506832872297886503765811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78684887659461030676708829 29506832872297886503765811)
            ·
              refine ⟨44260249308446829755648717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29506832872297886503765811 44260249308446829755648717)
              ·
                refine ⟨16597593490667561158368269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44260249308446829755648717 16597593490667561158368269)
                ·
                  refine ⟨6224097559000335434388101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16597593490667561158368269 6224097559000335434388101)
                  ·
                    refine ⟨1167018292312562893947769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6224097559000335434388101 1167018292312562893947769)
                    ·
                      rfl

theorem cell23_6818280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_6818280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818280 prefixEnd_6818280 := by exact prefixLift 6818280
  have htrace : WordTrace (prefixWord ++ tailWord_6818280) baseStart_6818280 baseEnd_6818280 := by
    simpa [prefixWord, tailWord_6818280, baseEnd_6818280] using wordTrace_append hprefix tailTrace_6818280
  have hstable : (prefixWord ++ tailWord_6818280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818280).length < 2 ^ (prefixWord ++ tailWord_6818280).sum := by decide
  have hdescent : baseEnd_6818280 < baseStart_6818280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818303 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 3]
def baseStart_6818303 : Nat := 118140960795 + 6818303 * 2 ^ 59
def prefixEnd_6818303 : Nat := 4983230072969 + 3 ^ 40 * 6818303 * 2
def baseEnd_6818303 : Nat := 3501066686992742091855701

theorem tailTrace_6818303 : CollatzResearch.WordTrace tailWord_6818303 prefixEnd_6818303 3501066686992742091855701 := by
  unfold tailWord_6818303
  simp only [CollatzResearch.WordTrace]
  refine ⟨248683940617460179289043563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165789293744973452859362375 248683940617460179289043563)
  ·
    refine ⟨373025910926190268933565345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248683940617460179289043563 373025910926190268933565345)
    ·
      refine ⟨279769433194642701700174009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373025910926190268933565345 279769433194642701700174009)
      ·
        refine ⟨209827074895982026275130507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279769433194642701700174009 209827074895982026275130507)
        ·
          refine ⟨314740612343973039412695761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209827074895982026275130507 314740612343973039412695761)
          ·
            refine ⟨236055459257979779559521821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314740612343973039412695761 236055459257979779559521821)
            ·
              refine ⟨88520797221742417334820683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236055459257979779559521821 88520797221742417334820683)
              ·
                refine ⟨132781195832613626002231025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88520797221742417334820683 132781195832613626002231025)
                ·
                  refine ⟨99585896874460219501673269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132781195832613626002231025 99585896874460219501673269)
                  ·
                    refine ⟨9336177831980645578281869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99585896874460219501673269 9336177831980645578281869)
                    ·
                      refine ⟨3501066686992742091855701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9336177831980645578281869 3501066686992742091855701)
                      ·
                        rfl

theorem cell23_6818303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_6818303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818303 prefixEnd_6818303 := by exact prefixLift 6818303
  have htrace : WordTrace (prefixWord ++ tailWord_6818303) baseStart_6818303 baseEnd_6818303 := by
    simpa [prefixWord, tailWord_6818303, baseEnd_6818303] using wordTrace_append hprefix tailTrace_6818303
  have hstable : (prefixWord ++ tailWord_6818303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818303).length < 2 ^ (prefixWord ++ tailWord_6818303).sum := by decide
  have hdescent : baseEnd_6818303 < baseStart_6818303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818324 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_6818324 : Nat := 118140960795 + 6818324 * 2 ^ 59
def prefixEnd_6818324 : Nat := 4983230072969 + 3 ^ 40 * 6818324 * 2
def baseEnd_6818324 : Nat := 3501077470086486509693105

theorem tailTrace_6818324 : CollatzResearch.WordTrace tailWord_6818324 prefixEnd_6818324 3501077470086486509693105 := by
  unfold tailWord_6818324
  simp only [CollatzResearch.WordTrace]
  refine ⟨124342353275192049937779013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165789804366922733250372017 124342353275192049937779013)
  ·
    refine ⟨23314191239098509363333565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124342353275192049937779013 23314191239098509363333565)
    ·
      refine ⟨8742821714661941011250087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23314191239098509363333565 8742821714661941011250087)
      ·
        refine ⟨13114232571992911516875131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8742821714661941011250087 13114232571992911516875131)
        ·
          refine ⟨19671348857989367275312697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13114232571992911516875131 19671348857989367275312697)
          ·
            refine ⟨14753511643492025456484523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19671348857989367275312697 14753511643492025456484523)
            ·
              refine ⟨22130267465238038184726785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14753511643492025456484523 22130267465238038184726785)
              ·
                refine ⟨16597700598928528638545089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22130267465238038184726785 16597700598928528638545089)
                ·
                  refine ⟨12448275449196396478908817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16597700598928528638545089 12448275449196396478908817)
                  ·
                    refine ⟨9336206586897297359181613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12448275449196396478908817 9336206586897297359181613)
                    ·
                      refine ⟨3501077470086486509693105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9336206586897297359181613 3501077470086486509693105)
                      ·
                        rfl

theorem cell23_6818324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_6818324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818324 prefixEnd_6818324 := by exact prefixLift 6818324
  have htrace : WordTrace (prefixWord ++ tailWord_6818324) baseStart_6818324 baseEnd_6818324 := by
    simpa [prefixWord, tailWord_6818324, baseEnd_6818324] using wordTrace_append hprefix tailTrace_6818324
  have hstable : (prefixWord ++ tailWord_6818324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818324).length < 2 ^ (prefixWord ++ tailWord_6818324).sum := by decide
  have hdescent : baseEnd_6818324 < baseStart_6818324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818344 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 6]
def baseStart_6818344 : Nat := 118140960795 + 6818344 * 2 ^ 59
def prefixEnd_6818344 : Nat := 4983230072969 + 3 ^ 40 * 6818344 * 2
def baseEnd_6818344 : Nat := 389009748855508492382557

theorem tailTrace_6818344 : CollatzResearch.WordTrace tailWord_6818344 prefixEnd_6818344 389009748855508492382557 := by
  unfold tailWord_6818344
  simp only [CollatzResearch.WordTrace]
  refine ⟨124342718005155821645643043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165790290673541095527524057 124342718005155821645643043)
  ·
    refine ⟨186514077007733732468464565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124342718005155821645643043 186514077007733732468464565)
    ·
      refine ⟨17485694719475037418918553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186514077007733732468464565 17485694719475037418918553)
      ·
        refine ⟨13114271039606278064188915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17485694719475037418918553 13114271039606278064188915)
        ·
          refine ⟨19671406559409417096283373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13114271039606278064188915 19671406559409417096283373)
          ·
            refine ⟨7376777459778531411106265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19671406559409417096283373 7376777459778531411106265)
            ·
              refine ⟨5532583094833898558329699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7376777459778531411106265 5532583094833898558329699)
              ·
                refine ⟨8298874642250847837494549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5532583094833898558329699 8298874642250847837494549)
                ·
                  refine ⟨389009748855508492382557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8298874642250847837494549 389009748855508492382557)
                  ·
                    rfl

theorem cell23_6818344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 6].length) (baseStart_6818344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818344 prefixEnd_6818344 := by exact prefixLift 6818344
  have htrace : WordTrace (prefixWord ++ tailWord_6818344) baseStart_6818344 baseEnd_6818344 := by
    simpa [prefixWord, tailWord_6818344, baseEnd_6818344] using wordTrace_append hprefix tailTrace_6818344
  have hstable : (prefixWord ++ tailWord_6818344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818344).length < 2 ^ (prefixWord ++ tailWord_6818344).sum := by decide
  have hdescent : baseEnd_6818344 < baseStart_6818344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818360 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_6818360 : Nat := 118140960795 + 6818360 * 2 ^ 59
def prefixEnd_6818360 : Nat := 4983230072969 + 3 ^ 40 * 6818360 * 2
def baseEnd_6818360 : Nat := 3501095955390048368842939

theorem tailTrace_6818360 : CollatzResearch.WordTrace tailWord_6818360 prefixEnd_6818360 3501095955390048368842939 := by
  unfold tailWord_6818360
  simp only [CollatzResearch.WordTrace]
  refine ⟨124343009789126839011934267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165790679718835785349245689 124343009789126839011934267)
  ·
    refine ⟨186514514683690258517901401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124343009789126839011934267 186514514683690258517901401)
    ·
      refine ⟨139885886012767693888426051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186514514683690258517901401 139885886012767693888426051)
      ·
        refine ⟨209828829019151540832639077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139885886012767693888426051 209828829019151540832639077)
        ·
          refine ⟨39342905441090913906119827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209828829019151540832639077 39342905441090913906119827)
          ·
            refine ⟨59014358161636370859179741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39342905441090913906119827 59014358161636370859179741)
            ·
              refine ⟨22130384310613639072192403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59014358161636370859179741 22130384310613639072192403)
              ·
                refine ⟨33195576465920458608288605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22130384310613639072192403 33195576465920458608288605)
                ·
                  refine ⟨12448341174720171978108227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33195576465920458608288605 12448341174720171978108227)
                  ·
                    refine ⟨18672511762080257967162341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12448341174720171978108227 18672511762080257967162341)
                    ·
                      refine ⟨3501095955390048368842939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18672511762080257967162341 3501095955390048368842939)
                      ·
                        rfl

theorem cell23_6818360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_6818360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818360 prefixEnd_6818360 := by exact prefixLift 6818360
  have htrace : WordTrace (prefixWord ++ tailWord_6818360) baseStart_6818360 baseEnd_6818360 := by
    simpa [prefixWord, tailWord_6818360, baseEnd_6818360] using wordTrace_append hprefix tailTrace_6818360
  have hstable : (prefixWord ++ tailWord_6818360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818360).length < 2 ^ (prefixWord ++ tailWord_6818360).sum := by decide
  have hdescent : baseEnd_6818360 < baseStart_6818360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818364 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 2, 3, 2]
def baseStart_6818364 : Nat := 118140960795 + 6818364 * 2 ^ 59
def prefixEnd_6818364 : Nat := 4983230072969 + 3 ^ 40 * 6818364 * 2
def baseEnd_6818364 : Nat := 3501098009312666353192921

theorem tailTrace_6818364 : CollatzResearch.WordTrace tailWord_6818364 prefixEnd_6818364 3501098009312666353192921 := by
  unfold tailWord_6818364
  simp only [CollatzResearch.WordTrace]
  refine ⟨124343082735119593353507073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165790776980159457804676097 124343082735119593353507073)
  ·
    refine ⟨93257312051339695015130305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124343082735119593353507073 93257312051339695015130305)
    ·
      refine ⟨69942984038504771261347729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93257312051339695015130305 69942984038504771261347729)
      ·
        refine ⟨52457238028878578446010797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69942984038504771261347729 52457238028878578446010797)
        ·
          refine ⟨19671464260829466917254049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52457238028878578446010797 19671464260829466917254049)
          ·
            refine ⟨14753598195622100187940537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19671464260829466917254049 14753598195622100187940537)
            ·
              refine ⟨11065198646716575140955403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14753598195622100187940537 11065198646716575140955403)
              ·
                refine ⟨16597797970074862711433105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11065198646716575140955403 16597797970074862711433105)
                ·
                  refine ⟨12448348477556147033574829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16597797970074862711433105 12448348477556147033574829)
                  ·
                    refine ⟨4668130679083555137590561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12448348477556147033574829 4668130679083555137590561)
                    ·
                      refine ⟨3501098009312666353192921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668130679083555137590561 3501098009312666353192921)
                      ·
                        rfl

theorem cell23_6818364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_6818364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818364 prefixEnd_6818364 := by exact prefixLift 6818364
  have htrace : WordTrace (prefixWord ++ tailWord_6818364) baseStart_6818364 baseEnd_6818364 := by
    simpa [prefixWord, tailWord_6818364, baseEnd_6818364] using wordTrace_append hprefix tailTrace_6818364
  have hstable : (prefixWord ++ tailWord_6818364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818364).length < 2 ^ (prefixWord ++ tailWord_6818364).sum := by decide
  have hdescent : baseEnd_6818364 < baseStart_6818364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818388 : List Nat := [2, 4, 1, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_6818388 : Nat := 118140960795 + 6818388 * 2 ^ 59
def prefixEnd_6818388 : Nat := 4983230072969 + 3 ^ 40 * 6818388 * 2
def baseEnd_6818388 : Nat := 3501110332848374259292811

theorem tailTrace_6818388 : CollatzResearch.WordTrace tailWord_6818388 prefixEnd_6818388 3501110332848374259292811 := by
  unfold tailWord_6818388
  simp only [CollatzResearch.WordTrace]
  refine ⟨124343520411076119402943909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165791360548101492537258545 124343520411076119402943909)
  ·
    refine ⟨23314410077076772388051983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124343520411076119402943909 23314410077076772388051983)
    ·
      refine ⟨34971615115615158582077975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23314410077076772388051983 34971615115615158582077975)
      ·
        refine ⟨52457422673422737873116963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34971615115615158582077975 52457422673422737873116963)
        ·
          refine ⟨78686134010134106809675445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52457422673422737873116963 78686134010134106809675445)
          ·
            refine ⟨7376825063450072513407073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78686134010134106809675445 7376825063450072513407073)
            ·
              refine ⟨5532618797587554385055305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7376825063450072513407073 5532618797587554385055305)
              ·
                refine ⟨4149464098190665788791479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532618797587554385055305 4149464098190665788791479)
                ·
                  refine ⟨6224196147285998683187219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4149464098190665788791479 6224196147285998683187219)
                  ·
                    refine ⟨9336294220928998024780829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6224196147285998683187219 9336294220928998024780829)
                    ·
                      refine ⟨3501110332848374259292811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9336294220928998024780829 3501110332848374259292811)
                      ·
                        rfl

theorem cell23_6818388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_6818388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818388 prefixEnd_6818388 := by exact prefixLift 6818388
  have htrace : WordTrace (prefixWord ++ tailWord_6818388) baseStart_6818388 baseEnd_6818388 := by
    simpa [prefixWord, tailWord_6818388, baseEnd_6818388] using wordTrace_append hprefix tailTrace_6818388
  have hstable : (prefixWord ++ tailWord_6818388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818388).length < 2 ^ (prefixWord ++ tailWord_6818388).sum := by decide
  have hdescent : baseEnd_6818388 < baseStart_6818388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818467 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 1, 4, 2]
def baseStart_6818467 : Nat := 118140960795 + 6818467 * 2 ^ 59
def prefixEnd_6818467 : Nat := 4983230072969 + 3 ^ 40 * 6818467 * 2
def baseEnd_6818467 : Nat := 3501150897820079450204947

theorem tailTrace_6818467 : CollatzResearch.WordTrace tailWord_6818467 prefixEnd_6818467 3501150897820079450204947 := by
  unfold tailWord_6818467
  simp only [CollatzResearch.WordTrace]
  refine ⟨248689922188866035298013655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165793281459244023532009103 248689922188866035298013655)
  ·
    refine ⟨373034883283299052947020483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248689922188866035298013655 373034883283299052947020483)
    ·
      refine ⟨559552324924948579420530725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373034883283299052947020483 559552324924948579420530725)
      ·
        refine ⟨104916060923427858641349511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 559552324924948579420530725 104916060923427858641349511)
        ·
          refine ⟨157374091385141787962024267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104916060923427858641349511 157374091385141787962024267)
          ·
            refine ⟨236061137077712681943036401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157374091385141787962024267 236061137077712681943036401)
            ·
              refine ⟨177045852808284511457277301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236061137077712681943036401 177045852808284511457277301)
              ·
                refine ⟨16598048700776672949119747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177045852808284511457277301 16598048700776672949119747)
                ·
                  refine ⟨24897073051165009423679621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16598048700776672949119747 24897073051165009423679621)
                  ·
                    refine ⟨4668201197093439266939929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24897073051165009423679621 4668201197093439266939929)
                    ·
                      refine ⟨3501150897820079450204947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668201197093439266939929 3501150897820079450204947)
                      ·
                        rfl

theorem cell23_6818467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_6818467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818467 prefixEnd_6818467 := by exact prefixLift 6818467
  have htrace : WordTrace (prefixWord ++ tailWord_6818467) baseStart_6818467 baseEnd_6818467 := by
    simpa [prefixWord, tailWord_6818467, baseEnd_6818467] using wordTrace_append hprefix tailTrace_6818467
  have hstable : (prefixWord ++ tailWord_6818467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818467).length < 2 ^ (prefixWord ++ tailWord_6818467).sum := by decide
  have hdescent : baseEnd_6818467 < baseStart_6818467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818487 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 5]
def baseStart_6818487 : Nat := 118140960795 + 6818487 * 2 ^ 59
def prefixEnd_6818487 : Nat := 4983230072969 + 3 ^ 40 * 6818487 * 2
def baseEnd_6818487 : Nat := 3501161167433169371954855

theorem tailTrace_6818487 : CollatzResearch.WordTrace tailWord_6818487 prefixEnd_6818487 3501161167433169371954855 := by
  unfold tailWord_6818487
  simp only [CollatzResearch.WordTrace]
  refine ⟨248690651648793578713741715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165793767765862385809161143 248690651648793578713741715)
  ·
    refine ⟨373035977473190368070612573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248690651648793578713741715 373035977473190368070612573)
    ·
      refine ⟨139888491552446388026479715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373035977473190368070612573 139888491552446388026479715)
      ·
        refine ⟨209832737328669582039719573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139888491552446388026479715 209832737328669582039719573)
        ·
          refine ⟨9835909562281386658111855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 209832737328669582039719573 9835909562281386658111855)
          ·
            refine ⟨14753864343422079987167783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9835909562281386658111855 14753864343422079987167783)
            ·
              refine ⟨22130796515133119980751675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14753864343422079987167783 22130796515133119980751675)
              ·
                refine ⟨33196194772699679971127513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22130796515133119980751675 33196194772699679971127513)
                ·
                  refine ⟨24897146079524759978345635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33196194772699679971127513 24897146079524759978345635)
                  ·
                    refine ⟨37345719119287139967518453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24897146079524759978345635 37345719119287139967518453)
                    ·
                      refine ⟨3501161167433169371954855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37345719119287139967518453 3501161167433169371954855)
                      ·
                        rfl

theorem cell23_6818487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_6818487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818487 prefixEnd_6818487 := by exact prefixLift 6818487
  have htrace : WordTrace (prefixWord ++ tailWord_6818487) baseStart_6818487 baseEnd_6818487 := by
    simpa [prefixWord, tailWord_6818487, baseEnd_6818487] using wordTrace_append hprefix tailTrace_6818487
  have hstable : (prefixWord ++ tailWord_6818487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818487).length < 2 ^ (prefixWord ++ tailWord_6818487).sum := by decide
  have hdescent : baseEnd_6818487 < baseStart_6818487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818557 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_6818557 : Nat := 118140960795 + 6818557 * 2 ^ 59
def prefixEnd_6818557 : Nat := 4983230072969 + 3 ^ 40 * 6818557 * 2
def baseEnd_6818557 : Nat := 3501197111078984098079533

theorem tailTrace_6818557 : CollatzResearch.WordTrace tailWord_6818557 prefixEnd_6818557 3501197111078984098079533 := by
  unfold tailWord_6818557
  simp only [CollatzResearch.WordTrace]
  refine ⟨248693204758539980668789925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165795469839026653779193283 248693204758539980668789925)
  ·
    refine ⟨46629975892226246375398111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248693204758539980668789925 46629975892226246375398111)
    ·
      refine ⟨69944963838339369563097167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46629975892226246375398111 69944963838339369563097167)
      ·
        refine ⟨104917445757509054344645751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69944963838339369563097167 104917445757509054344645751)
        ·
          refine ⟨157376168636263581516968627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104917445757509054344645751 157376168636263581516968627)
          ·
            refine ⟨236064252954395372275452941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157376168636263581516968627 236064252954395372275452941)
            ·
              refine ⟨88524094857898264603294853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236064252954395372275452941 88524094857898264603294853)
              ·
                refine ⟨16598267785855924613117785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88524094857898264603294853 16598267785855924613117785)
                ·
                  refine ⟨12448700839391943459838339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16598267785855924613117785 12448700839391943459838339)
                  ·
                    refine ⟨18673051259087915189757509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12448700839391943459838339 18673051259087915189757509)
                    ·
                      refine ⟨3501197111078984098079533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18673051259087915189757509 3501197111078984098079533)
                      ·
                        rfl

theorem cell23_6818557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_6818557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818557 prefixEnd_6818557 := by exact prefixLift 6818557
  have htrace : WordTrace (prefixWord ++ tailWord_6818557) baseStart_6818557 baseEnd_6818557 := by
    simpa [prefixWord, tailWord_6818557, baseEnd_6818557] using wordTrace_append hprefix tailTrace_6818557
  have hstable : (prefixWord ++ tailWord_6818557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818557).length < 2 ^ (prefixWord ++ tailWord_6818557).sum := by decide
  have hdescent : baseEnd_6818557 < baseStart_6818557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818558 : List Nat := [4, 2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_6818558 : Nat := 118140960795 + 6818558 * 2 ^ 59
def prefixEnd_6818558 : Nat := 4983230072969 + 3 ^ 40 * 6818558 * 2
def baseEnd_6818558 : Nat := 389021958284404288240781

theorem tailTrace_6818558 : CollatzResearch.WordTrace tailWord_6818558 prefixEnd_6818558 389021958284404288240781 := by
  unfold tailWord_6818558
  simp only [CollatzResearch.WordTrace]
  refine ⟨31086655153942044729947041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165795494154357571893050885 31086655153942044729947041)
  ·
    refine ⟨23314991365456533547460281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31086655153942044729947041 23314991365456533547460281)
    ·
      refine ⟨17486243524092400160595211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23314991365456533547460281 17486243524092400160595211)
      ·
        refine ⟨26229365286138600240892817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17486243524092400160595211 26229365286138600240892817)
        ·
          refine ⟨19672023964603950180669613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26229365286138600240892817 19672023964603950180669613)
          ·
            refine ⟨7377008986726481317751105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19672023964603950180669613 7377008986726481317751105)
            ·
              refine ⟨5532756740044860988313329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7377008986726481317751105 5532756740044860988313329)
              ·
                refine ⟨4149567555033645741234997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532756740044860988313329 4149567555033645741234997)
                ·
                  refine ⟨389021958284404288240781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4149567555033645741234997 389021958284404288240781)
                  ·
                    rfl

theorem cell23_6818558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_6818558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818558 prefixEnd_6818558 := by exact prefixLift 6818558
  have htrace : WordTrace (prefixWord ++ tailWord_6818558) baseStart_6818558 baseEnd_6818558 := by
    simpa [prefixWord, tailWord_6818558, baseEnd_6818558] using wordTrace_append hprefix tailTrace_6818558
  have hstable : (prefixWord ++ tailWord_6818558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818558).length < 2 ^ (prefixWord ++ tailWord_6818558).sum := by decide
  have hdescent : baseEnd_6818558 < baseStart_6818558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818577 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 3]
def baseStart_6818577 : Nat := 118140960795 + 6818577 * 2 ^ 59
def prefixEnd_6818577 : Nat := 4983230072969 + 3 ^ 40 * 6818577 * 2
def baseEnd_6818577 : Nat := 3501207380692074019829441

theorem tailTrace_6818577 : CollatzResearch.WordTrace tailWord_6818577 prefixEnd_6818577 3501207380692074019829441 := by
  unfold tailWord_6818577
  simp only [CollatzResearch.WordTrace]
  refine ⟨248693934218467524084517985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165795956145645016056345323 248693934218467524084517985)
  ·
    refine ⟨186520450663850643063388489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248693934218467524084517985 186520450663850643063388489)
    ·
      refine ⟨139890337997887982297541367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186520450663850643063388489 139890337997887982297541367)
      ·
        refine ⟨209835506996831973446312051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139890337997887982297541367 209835506996831973446312051)
        ·
          refine ⟨314753260495247960169468077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209835506996831973446312051 314753260495247960169468077)
          ·
            refine ⟨118032472685717985063550529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314753260495247960169468077 118032472685717985063550529)
            ·
              refine ⟨88524354514288488797662897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118032472685717985063550529 88524354514288488797662897)
              ·
                refine ⟨66393265885716366598247173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88524354514288488797662897 66393265885716366598247173)
                ·
                  refine ⟨12448737353571818737171345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66393265885716366598247173 12448737353571818737171345)
                  ·
                    refine ⟨9336553015178864052878509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12448737353571818737171345 9336553015178864052878509)
                    ·
                      refine ⟨3501207380692074019829441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9336553015178864052878509 3501207380692074019829441)
                      ·
                        rfl

theorem cell23_6818577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_6818577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818577 prefixEnd_6818577 := by exact prefixLift 6818577
  have htrace : WordTrace (prefixWord ++ tailWord_6818577) baseStart_6818577 baseEnd_6818577 := by
    simpa [prefixWord, tailWord_6818577, baseEnd_6818577] using wordTrace_append hprefix tailTrace_6818577
  have hstable : (prefixWord ++ tailWord_6818577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818577).length < 2 ^ (prefixWord ++ tailWord_6818577).sum := by decide
  have hdescent : baseEnd_6818577 < baseStart_6818577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818594 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_6818594 : Nat := 118140960795 + 6818594 * 2 ^ 59
def prefixEnd_6818594 : Nat := 4983230072969 + 3 ^ 40 * 6818594 * 2
def baseEnd_6818594 : Nat := 3501216109863200453316863

theorem tailTrace_6818594 : CollatzResearch.WordTrace tailWord_6818594 prefixEnd_6818594 3501216109863200453316863 := by
  unfold tailWord_6818594
  simp only [CollatzResearch.WordTrace]
  refine ⟨62173638564851483996971709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165796369506270623991924557 62173638564851483996971709)
  ·
    refine ⟨23315114461819306498864391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62173638564851483996971709 23315114461819306498864391)
    ·
      refine ⟨34972671692728959748296587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23315114461819306498864391 34972671692728959748296587)
      ·
        refine ⟨52459007539093439622444881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34972671692728959748296587 52459007539093439622444881)
        ·
          refine ⟨39344255654320079716833661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52459007539093439622444881 39344255654320079716833661)
          ·
            refine ⟨14754095870370029893812623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39344255654320079716833661 14754095870370029893812623)
            ·
              refine ⟨22131143805555044840718935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14754095870370029893812623 22131143805555044840718935)
              ·
                refine ⟨33196715708332567261078403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22131143805555044840718935 33196715708332567261078403)
                ·
                  refine ⟨49795073562498850891617605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33196715708332567261078403 49795073562498850891617605)
                  ·
                    refine ⟨9336576292968534542178301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49795073562498850891617605 9336576292968534542178301)
                    ·
                      refine ⟨3501216109863200453316863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9336576292968534542178301 3501216109863200453316863)
                      ·
                        rfl

theorem cell23_6818594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_6818594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818594 prefixEnd_6818594 := by exact prefixLift 6818594
  have htrace : WordTrace (prefixWord ++ tailWord_6818594) baseStart_6818594 baseEnd_6818594 := by
    simpa [prefixWord, tailWord_6818594, baseEnd_6818594] using wordTrace_append hprefix tailTrace_6818594
  have hstable : (prefixWord ++ tailWord_6818594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818594).length < 2 ^ (prefixWord ++ tailWord_6818594).sum := by decide
  have hdescent : baseEnd_6818594 < baseStart_6818594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818634 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2]
def baseStart_6818634 : Nat := 118140960795 + 6818634 * 2 ^ 59
def prefixEnd_6818634 : Nat := 4983230072969 + 3 ^ 40 * 6818634 * 2
def baseEnd_6818634 : Nat := 3501236649089380296816679

theorem tailTrace_6818634 : CollatzResearch.WordTrace tailWord_6818634 prefixEnd_6818634 3501236649089380296816679 := by
  unfold tailWord_6818634
  simp only [CollatzResearch.WordTrace]
  refine ⟨62174003294815255704835739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165797342119507348546228637 62174003294815255704835739)
  ·
    refine ⟨93261004942222883557253609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62174003294815255704835739 93261004942222883557253609)
    ·
      refine ⟨69945753706667162667940207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93261004942222883557253609 69945753706667162667940207)
      ·
        refine ⟨104918630560000744001910311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69945753706667162667940207 104918630560000744001910311)
        ·
          refine ⟨157377945840001116002865467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104918630560000744001910311 157377945840001116002865467)
          ·
            refine ⟨236066918760001674004298201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157377945840001116002865467 236066918760001674004298201)
            ·
              refine ⟨177050189070001255503223651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236066918760001674004298201 177050189070001255503223651)
              ·
                refine ⟨265575283605001883254835477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177050189070001255503223651 265575283605001883254835477)
                ·
                  refine ⟨12448841418984463277570413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 265575283605001883254835477 12448841418984463277570413)
                  ·
                    refine ⟨4668315532119173729088905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12448841418984463277570413 4668315532119173729088905)
                    ·
                      refine ⟨3501236649089380296816679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668315532119173729088905 3501236649089380296816679)
                      ·
                        rfl

theorem cell23_6818634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_6818634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818634 prefixEnd_6818634 := by exact prefixLift 6818634
  have htrace : WordTrace (prefixWord ++ tailWord_6818634) baseStart_6818634 baseEnd_6818634 := by
    simpa [prefixWord, tailWord_6818634, baseEnd_6818634] using wordTrace_append hprefix tailTrace_6818634
  have hstable : (prefixWord ++ tailWord_6818634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818634).length < 2 ^ (prefixWord ++ tailWord_6818634).sum := by decide
  have hdescent : baseEnd_6818634 < baseStart_6818634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818667 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 5]
def baseStart_6818667 : Nat := 118140960795 + 6818667 * 2 ^ 59
def prefixEnd_6818667 : Nat := 4983230072969 + 3 ^ 40 * 6818667 * 2
def baseEnd_6818667 : Nat := 3501253593950978667704027

theorem tailTrace_6818667 : CollatzResearch.WordTrace tailWord_6818667 prefixEnd_6818667 3501253593950978667704027 := by
  unfold tailWord_6818667
  simp only [CollatzResearch.WordTrace]
  refine ⟨248697216788141469455294255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165798144525427646303529503 248697216788141469455294255)
  ·
    refine ⟨373045825182212204182941383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248697216788141469455294255 373045825182212204182941383)
    ·
      refine ⟨559568737773318306274412075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373045825182212204182941383 559568737773318306274412075)
      ·
        refine ⟨839353106659977459411618113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559568737773318306274412075 839353106659977459411618113)
        ·
          refine ⟨629514829994983094558713585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839353106659977459411618113 629514829994983094558713585)
          ·
            refine ⟨472136122496237320919035189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629514829994983094558713585 472136122496237320919035189)
            ·
              refine ⟨44262761484022248836159549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 472136122496237320919035189 44262761484022248836159549)
              ·
                refine ⟨16598535556508343313559831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44262761484022248836159549 16598535556508343313559831)
                ·
                  refine ⟨24897803334762514970339747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16598535556508343313559831 24897803334762514970339747)
                  ·
                    refine ⟨37346705002143772455509621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24897803334762514970339747 37346705002143772455509621)
                    ·
                      refine ⟨3501253593950978667704027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37346705002143772455509621 3501253593950978667704027)
                      ·
                        rfl

theorem cell23_6818667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 5].length) (baseStart_6818667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818667 prefixEnd_6818667 := by exact prefixLift 6818667
  have htrace : WordTrace (prefixWord ++ tailWord_6818667) baseStart_6818667 baseEnd_6818667 := by
    simpa [prefixWord, tailWord_6818667, baseEnd_6818667] using wordTrace_append hprefix tailTrace_6818667
  have hstable : (prefixWord ++ tailWord_6818667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818667).length < 2 ^ (prefixWord ++ tailWord_6818667).sum := by decide
  have hdescent : baseEnd_6818667 < baseStart_6818667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818674 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_6818674 : Nat := 118140960795 + 6818674 * 2 ^ 59
def prefixEnd_6818674 : Nat := 4983230072969 + 3 ^ 40 * 6818674 * 2
def baseEnd_6818674 : Nat := 1167085729438520046772165

theorem tailTrace_6818674 : CollatzResearch.WordTrace tailWord_6818674 prefixEnd_6818674 1167085729438520046772165 := by
  unfold tailWord_6818674
  simp only [CollatzResearch.WordTrace]
  refine ⟨62174368024779027412699769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165798314732744073100532717 62174368024779027412699769)
  ·
    refine ⟨46630776018584270559524827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62174368024779027412699769 46630776018584270559524827)
    ·
      refine ⟨69946164027876405839287241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46630776018584270559524827 69946164027876405839287241)
      ·
        refine ⟨52459623020907304379465431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69946164027876405839287241 52459623020907304379465431)
        ·
          refine ⟨78689434531360956569198147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52459623020907304379465431 78689434531360956569198147)
          ·
            refine ⟨118034151797041434853797221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78689434531360956569198147 118034151797041434853797221)
            ·
              refine ⟨22131403461945269035086979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118034151797041434853797221 22131403461945269035086979)
              ·
                refine ⟨33197105192917903552630469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22131403461945269035086979 33197105192917903552630469)
                ·
                  refine ⟨6224457223672106916118213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33197105192917903552630469 6224457223672106916118213)
                  ·
                    refine ⟨1167085729438520046772165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6224457223672106916118213 1167085729438520046772165)
                    ·
                      rfl

theorem cell23_6818674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_6818674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818674 prefixEnd_6818674 := by exact prefixLift 6818674
  have htrace : WordTrace (prefixWord ++ tailWord_6818674) baseStart_6818674 baseEnd_6818674 := by
    simpa [prefixWord, tailWord_6818674, baseEnd_6818674] using wordTrace_append hprefix tailTrace_6818674
  have hstable : (prefixWord ++ tailWord_6818674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818674).length < 2 ^ (prefixWord ++ tailWord_6818674).sum := by decide
  have hdescent : baseEnd_6818674 < baseStart_6818674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818698 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_6818698 : Nat := 118140960795 + 6818698 * 2 ^ 59
def prefixEnd_6818698 : Nat := 4983230072969 + 3 ^ 40 * 6818698 * 2
def baseEnd_6818698 : Nat := 3501269511851268046416385

theorem tailTrace_6818698 : CollatzResearch.WordTrace tailWord_6818698 prefixEnd_6818698 3501269511851268046416385 := by
  unfold tailWord_6818698
  simp only [CollatzResearch.WordTrace]
  refine ⟨62174586862757290437418187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165798898300686107833115165 62174586862757290437418187)
  ·
    refine ⟨93261880294135935656127281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62174586862757290437418187 93261880294135935656127281)
    ·
      refine ⟨69946410220601951742095461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93261880294135935656127281 69946410220601951742095461)
      ·
        refine ⟨13114951916362865951642899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69946410220601951742095461 13114951916362865951642899)
        ·
          refine ⟨19672427874544298927464349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13114951916362865951642899 19672427874544298927464349)
          ·
            refine ⟨7377160452954112097799131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19672427874544298927464349 7377160452954112097799131)
            ·
              refine ⟨11065740679431168146698697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377160452954112097799131 11065740679431168146698697)
              ·
                refine ⟨8299305509573376110024023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11065740679431168146698697 8299305509573376110024023)
                ·
                  refine ⟨12448958264360064165036035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8299305509573376110024023 12448958264360064165036035)
                  ·
                    refine ⟨18673437396540096247554053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12448958264360064165036035 18673437396540096247554053)
                    ·
                      refine ⟨3501269511851268046416385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18673437396540096247554053 3501269511851268046416385)
                      ·
                        rfl

theorem cell23_6818698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_6818698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818698 prefixEnd_6818698 := by exact prefixLift 6818698
  have htrace : WordTrace (prefixWord ++ tailWord_6818698) baseStart_6818698 baseEnd_6818698 := by
    simpa [prefixWord, tailWord_6818698, baseEnd_6818698] using wordTrace_append hprefix tailTrace_6818698
  have hstable : (prefixWord ++ tailWord_6818698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818698).length < 2 ^ (prefixWord ++ tailWord_6818698).sum := by decide
  have hdescent : baseEnd_6818698 < baseStart_6818698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818741 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_6818741 : Nat := 118140960795 + 6818741 * 2 ^ 59
def prefixEnd_6818741 : Nat := 4983230072969 + 3 ^ 40 * 6818741 * 2
def baseEnd_6818741 : Nat := 3501291591519411378178687

theorem tailTrace_6818741 : CollatzResearch.WordTrace tailWord_6818741 prefixEnd_6818741 3501291591519411378178687 := by
  unfold tailWord_6818741
  simp only [CollatzResearch.WordTrace]
  refine ⟨248699915789873380093488077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165799943859915586728992051 248699915789873380093488077)
  ·
    refine ⟨93262468421202517535058029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248699915789873380093488077 93262468421202517535058029)
    ·
      refine ⟨34973425657950944075646761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93262468421202517535058029 34973425657950944075646761)
      ·
        refine ⟨26230069243463208056735071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34973425657950944075646761 26230069243463208056735071)
        ·
          refine ⟨39345103865194812085102607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26230069243463208056735071 39345103865194812085102607)
          ·
            refine ⟨59017655797792218127653911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39345103865194812085102607 59017655797792218127653911)
            ·
              refine ⟨88526483696688327191480867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59017655797792218127653911 88526483696688327191480867)
              ·
                refine ⟨132789725545032490787221301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88526483696688327191480867 132789725545032490787221301)
                ·
                  refine ⟨12449036769846796011301997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132789725545032490787221301 12449036769846796011301997)
                  ·
                    refine ⟨4668388788692548504238249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12449036769846796011301997 4668388788692548504238249)
                    ·
                      refine ⟨3501291591519411378178687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668388788692548504238249 3501291591519411378178687)
                      ·
                        rfl

theorem cell23_6818741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_6818741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818741 prefixEnd_6818741 := by exact prefixLift 6818741
  have htrace : WordTrace (prefixWord ++ tailWord_6818741) baseStart_6818741 baseEnd_6818741 := by
    simpa [prefixWord, tailWord_6818741, baseEnd_6818741] using wordTrace_append hprefix tailTrace_6818741
  have hstable : (prefixWord ++ tailWord_6818741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818741).length < 2 ^ (prefixWord ++ tailWord_6818741).sum := by decide
  have hdescent : baseEnd_6818741 < baseStart_6818741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818788 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 2, 2, 2]
def baseStart_6818788 : Nat := 118140960795 + 6818788 * 2 ^ 59
def prefixEnd_6818788 : Nat := 4983230072969 + 3 ^ 40 * 6818788 * 2
def baseEnd_6818788 : Nat := 3501315725110172694290971

theorem tailTrace_6818788 : CollatzResearch.WordTrace tailWord_6818788 prefixEnd_6818788 3501315725110172694290971 := by
  unfold tailWord_6818788
  simp only [CollatzResearch.WordTrace]
  refine ⟨124350815010351553560224509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165801086680468738080299345 124350815010351553560224509)
  ·
    refine ⟨46631555628881832585084191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124350815010351553560224509 46631555628881832585084191)
    ·
      refine ⟨69947333443322748877626287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46631555628881832585084191 69947333443322748877626287)
      ·
        refine ⟨104921000164984123316439431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69947333443322748877626287 104921000164984123316439431)
        ·
          refine ⟨157381500247476184974659147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104921000164984123316439431 157381500247476184974659147)
          ·
            refine ⟨236072250371214277461988721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157381500247476184974659147 236072250371214277461988721)
            ·
              refine ⟨177054187778410708096491541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236072250371214277461988721 177054187778410708096491541)
              ·
                refine ⟨8299415052113001942023041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177054187778410708096491541 8299415052113001942023041)
                ·
                  refine ⟨6224561289084751456517281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8299415052113001942023041 6224561289084751456517281)
                  ·
                    refine ⟨4668420966813563592387961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6224561289084751456517281 4668420966813563592387961)
                    ·
                      refine ⟨3501315725110172694290971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668420966813563592387961 3501315725110172694290971)
                      ·
                        rfl

theorem cell23_6818788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_6818788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818788 prefixEnd_6818788 := by exact prefixLift 6818788
  have htrace : WordTrace (prefixWord ++ tailWord_6818788) baseStart_6818788 baseEnd_6818788 := by
    simpa [prefixWord, tailWord_6818788, baseEnd_6818788] using wordTrace_append hprefix tailTrace_6818788
  have hstable : (prefixWord ++ tailWord_6818788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818788).length < 2 ^ (prefixWord ++ tailWord_6818788).sum := by decide
  have hdescent : baseEnd_6818788 < baseStart_6818788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818794 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 7]
def baseStart_6818794 : Nat := 118140960795 + 6818794 * 2 ^ 59
def prefixEnd_6818794 : Nat := 4983230072969 + 3 ^ 40 * 6818794 * 2
def baseEnd_6818794 : Nat := 389035422888233296757327

theorem tailTrace_6818794 : CollatzResearch.WordTrace tailWord_6818794 prefixEnd_6818794 389035422888233296757327 := by
  unfold tailWord_6818794
  simp only [CollatzResearch.WordTrace]
  refine ⟨62175462214670342536291859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165801232572454246763444957 62175462214670342536291859)
  ·
    refine ⟨93263193322005513804437789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62175462214670342536291859 93263193322005513804437789)
    ·
      refine ⟨34973697495752067676664171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93263193322005513804437789 34973697495752067676664171)
      ·
        refine ⟨52460546243628101514996257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34973697495752067676664171 52460546243628101514996257)
        ·
          refine ⟨39345409682721076136247193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52460546243628101514996257 39345409682721076136247193)
          ·
            refine ⟨29509057262040807102185395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39345409682721076136247193 29509057262040807102185395)
            ·
              refine ⟨44263585893061210653278093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29509057262040807102185395 44263585893061210653278093)
              ·
                refine ⟨16598844709897953994979285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44263585893061210653278093 16598844709897953994979285)
                ·
                  refine ⟨389035422888233296757327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16598844709897953994979285 389035422888233296757327)
                  ·
                    rfl

theorem cell23_6818794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_6818794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818794 prefixEnd_6818794 := by exact prefixLift 6818794
  have htrace : WordTrace (prefixWord ++ tailWord_6818794) baseStart_6818794 baseEnd_6818794 := by
    simpa [prefixWord, tailWord_6818794, baseEnd_6818794] using wordTrace_append hprefix tailTrace_6818794
  have hstable : (prefixWord ++ tailWord_6818794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818794).length < 2 ^ (prefixWord ++ tailWord_6818794).sum := by decide
  have hdescent : baseEnd_6818794 < baseStart_6818794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818824 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 1, 7]
def baseStart_6818824 : Nat := 118140960795 + 6818824 * 2 ^ 59
def prefixEnd_6818824 : Nat := 4983230072969 + 3 ^ 40 * 6818824 * 2
def baseEnd_6818824 : Nat := 1167111403471244851146935

theorem tailTrace_6818824 : CollatzResearch.WordTrace tailWord_6818824 prefixEnd_6818824 1167111403471244851146935 := by
  unfold tailWord_6818824
  simp only [CollatzResearch.WordTrace]
  refine ⟨124351471524286342634379763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165801962032381790179173017 124351471524286342634379763)
  ·
    refine ⟨186527207286429513951569645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124351471524286342634379763 186527207286429513951569645)
    ·
      refine ⟨69947702732411067731838617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186527207286429513951569645 69947702732411067731838617)
      ·
        refine ⟨52460777049308300798878963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69947702732411067731838617 52460777049308300798878963)
        ·
          refine ⟨78691165573962451198318445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52460777049308300798878963 78691165573962451198318445)
          ·
            refine ⟨29509187090235919199369417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78691165573962451198318445 29509187090235919199369417)
            ·
              refine ⟨22131890317676939399527063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29509187090235919199369417 22131890317676939399527063)
              ·
                refine ⟨33197835476515409099290595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22131890317676939399527063 33197835476515409099290595)
                ·
                  refine ⟨49796753214773113648935893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33197835476515409099290595 49796753214773113648935893)
                  ·
                    refine ⟨1167111403471244851146935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49796753214773113648935893 1167111403471244851146935)
                    ·
                      rfl

theorem cell23_6818824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_6818824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818824 prefixEnd_6818824 := by exact prefixLift 6818824
  have htrace : WordTrace (prefixWord ++ tailWord_6818824) baseStart_6818824 baseEnd_6818824 := by
    simpa [prefixWord, tailWord_6818824, baseEnd_6818824] using wordTrace_append hprefix tailTrace_6818824
  have hstable : (prefixWord ++ tailWord_6818824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818824).length < 2 ^ (prefixWord ++ tailWord_6818824).sum := by decide
  have hdescent : baseEnd_6818824 < baseStart_6818824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818828 : List Nat := [2, 2, 1, 2, 3, 4, 1, 3, 5]
def baseStart_6818828 : Nat := 118140960795 + 6818828 * 2 ^ 59
def prefixEnd_6818828 : Nat := 4983230072969 + 3 ^ 40 * 6818828 * 2
def baseEnd_6818828 : Nat := 389037362704039170865643

theorem tailTrace_6818828 : CollatzResearch.WordTrace tailWord_6818828 prefixEnd_6818828 389037362704039170865643 := by
  unfold tailWord_6818828
  simp only [CollatzResearch.WordTrace]
  refine ⟨124351544470279096975952569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165802059293705462634603425 124351544470279096975952569)
  ·
    refine ⟨93263658352709322731964427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124351544470279096975952569 93263658352709322731964427)
    ·
      refine ⟨139895487529063984097946641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93263658352709322731964427 139895487529063984097946641)
      ·
        refine ⟨104921615646797988073459981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139895487529063984097946641 104921615646797988073459981)
        ·
          refine ⟨39345605867549245527547493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104921615646797988073459981 39345605867549245527547493)
          ·
            refine ⟨7377301100165483536415155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39345605867549245527547493 7377301100165483536415155)
            ·
              refine ⟨11065951650248225304622733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377301100165483536415155 11065951650248225304622733)
              ·
                refine ⟨4149731868843084489233525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11065951650248225304622733 4149731868843084489233525)
                ·
                  refine ⟨389037362704039170865643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4149731868843084489233525 389037362704039170865643)
                  ·
                    rfl

theorem cell23_6818828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_6818828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818828 prefixEnd_6818828 := by exact prefixLift 6818828
  have htrace : WordTrace (prefixWord ++ tailWord_6818828) baseStart_6818828 baseEnd_6818828 := by
    simpa [prefixWord, tailWord_6818828, baseEnd_6818828] using wordTrace_append hprefix tailTrace_6818828
  have hstable : (prefixWord ++ tailWord_6818828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818828).length < 2 ^ (prefixWord ++ tailWord_6818828).sum := by decide
  have hdescent : baseEnd_6818828 < baseStart_6818828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818845 : List Nat := [1, 4, 2, 2, 3, 1, 3, 2, 5]
def baseStart_6818845 : Nat := 118140960795 + 6818845 * 2 ^ 59
def prefixEnd_6818845 : Nat := 4983230072969 + 3 ^ 40 * 6818845 * 2
def baseEnd_6818845 : Nat := 389038332611942107919801

theorem tailTrace_6818845 : CollatzResearch.WordTrace tailWord_6818845 prefixEnd_6818845 389038332611942107919801 := by
  unfold tailWord_6818845
  simp only [CollatzResearch.WordTrace]
  refine ⟨248703708981496605855273989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165802472654331070570182659 248703708981496605855273989)
  ·
    refine ⟨46631945434030613597863873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248703708981496605855273989 46631945434030613597863873)
    ·
      refine ⟨34973959075522960198397905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46631945434030613597863873 34973959075522960198397905)
      ·
        refine ⟨26230469306642220148798429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34973959075522960198397905 26230469306642220148798429)
        ·
          refine ⟨9836425989990832555799411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26230469306642220148798429 9836425989990832555799411)
          ·
            refine ⟨14754638984986248833699117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9836425989990832555799411 14754638984986248833699117)
            ·
              refine ⟨5532989619369843312637169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14754638984986248833699117 5532989619369843312637169)
              ·
                refine ⟨4149742214527382484477877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532989619369843312637169 4149742214527382484477877)
                ·
                  refine ⟨389038332611942107919801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4149742214527382484477877 389038332611942107919801)
                  ·
                    rfl

theorem cell23_6818845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_6818845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818845 prefixEnd_6818845 := by exact prefixLift 6818845
  have htrace : WordTrace (prefixWord ++ tailWord_6818845) baseStart_6818845 baseEnd_6818845 := by
    simpa [prefixWord, tailWord_6818845, baseEnd_6818845] using wordTrace_append hprefix tailTrace_6818845
  have hstable : (prefixWord ++ tailWord_6818845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818845).length < 2 ^ (prefixWord ++ tailWord_6818845).sum := by decide
  have hdescent : baseEnd_6818845 < baseStart_6818845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818874 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_6818874 : Nat := 118140960795 + 6818874 * 2 ^ 59
def prefixEnd_6818874 : Nat := 4983230072969 + 3 ^ 40 * 6818874 * 2
def baseEnd_6818874 : Nat := 3501359884446459357815575

theorem tailTrace_6818874 : CollatzResearch.WordTrace tailWord_6818874 prefixEnd_6818874 3501359884446459357815575 := by
  unfold tailWord_6818874
  simp only [CollatzResearch.WordTrace]
  refine ⟨62176191674597885952019919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165803177798927695872053117 62176191674597885952019919)
  ·
    refine ⟨93264287511896828928029879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62176191674597885952019919 93264287511896828928029879)
    ·
      refine ⟨139896431267845243392044819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93264287511896828928029879 139896431267845243392044819)
      ·
        refine ⟨209844646901767865088067229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139896431267845243392044819 209844646901767865088067229)
        ·
          refine ⟨78691742588162949408025211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209844646901767865088067229 78691742588162949408025211)
          ·
            refine ⟨118037613882244424112037817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78691742588162949408025211 118037613882244424112037817)
            ·
              refine ⟨88528210411683318084028363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118037613882244424112037817 88528210411683318084028363)
              ·
                refine ⟨132792315617524977126042545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88528210411683318084028363 132792315617524977126042545)
                ·
                  refine ⟨99594236713143732844531909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132792315617524977126042545 99594236713143732844531909)
                  ·
                    refine ⟨18673919383714449908349733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99594236713143732844531909 18673919383714449908349733)
                    ·
                      refine ⟨3501359884446459357815575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18673919383714449908349733 3501359884446459357815575)
                      ·
                        rfl

theorem cell23_6818874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_6818874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818874 prefixEnd_6818874 := by exact prefixLift 6818874
  have htrace : WordTrace (prefixWord ++ tailWord_6818874) baseStart_6818874 baseEnd_6818874 := by
    simpa [prefixWord, tailWord_6818874, baseEnd_6818874] using wordTrace_append hprefix tailTrace_6818874
  have hstable : (prefixWord ++ tailWord_6818874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818874).length < 2 ^ (prefixWord ++ tailWord_6818874).sum := by decide
  have hdescent : baseEnd_6818874 < baseStart_6818874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818878 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_6818878 : Nat := 118140960795 + 6818878 * 2 ^ 59
def prefixEnd_6818878 : Nat := 4983230072969 + 3 ^ 40 * 6818878 * 2
def baseEnd_6818878 : Nat := 3501361938369077342165557

theorem tailTrace_6818878 : CollatzResearch.WordTrace tailWord_6818878 prefixEnd_6818878 3501361938369077342165557 := by
  unfold tailWord_6818878
  simp only [CollatzResearch.WordTrace]
  refine ⟨31088114073797131561403161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165803275060251368327483525 31088114073797131561403161)
  ·
    refine ⟨23316085555347848671052371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31088114073797131561403161 23316085555347848671052371)
    ·
      refine ⟨34974128333021773006578557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23316085555347848671052371 34974128333021773006578557)
      ·
        refine ⟨13115298124883164877466959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34974128333021773006578557 13115298124883164877466959)
        ·
          refine ⟨19672947187324747316200439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13115298124883164877466959 19672947187324747316200439)
          ·
            refine ⟨29509420780987120974300659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19672947187324747316200439 29509420780987120974300659)
            ·
              refine ⟨44264131171480681461450989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29509420780987120974300659 44264131171480681461450989)
              ·
                refine ⟨16599049189305255548044121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44264131171480681461450989 16599049189305255548044121)
                ·
                  refine ⟨12449286891978941661033091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16599049189305255548044121 12449286891978941661033091)
                  ·
                    refine ⟨18673930337968412491549637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12449286891978941661033091 18673930337968412491549637)
                    ·
                      refine ⟨3501361938369077342165557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18673930337968412491549637 3501361938369077342165557)
                      ·
                        rfl

theorem cell23_6818878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_6818878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818878 prefixEnd_6818878 := by exact prefixLift 6818878
  have htrace : WordTrace (prefixWord ++ tailWord_6818878) baseStart_6818878 baseEnd_6818878 := by
    simpa [prefixWord, tailWord_6818878, baseEnd_6818878] using wordTrace_append hprefix tailTrace_6818878
  have hstable : (prefixWord ++ tailWord_6818878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818878).length < 2 ^ (prefixWord ++ tailWord_6818878).sum := by decide
  have hdescent : baseEnd_6818878 < baseStart_6818878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818888 : List Nat := [2, 1, 3, 1, 1, 1, 4, 5, 1, 4]
def baseStart_6818888 : Nat := 118140960795 + 6818888 * 2 ^ 59
def prefixEnd_6818888 : Nat := 4983230072969 + 3 ^ 40 * 6818888 * 2
def baseEnd_6818888 : Nat := 1167122357725207434346837

theorem tailTrace_6818888 : CollatzResearch.WordTrace tailWord_6818888 prefixEnd_6818888 1167122357725207434346837 := by
  unfold tailWord_6818888
  simp only [CollatzResearch.WordTrace]
  refine ⟨124352638660170412099544659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165803518213560549466059545 124352638660170412099544659)
  ·
    refine ⟨186528957990255618149316989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124352638660170412099544659 186528957990255618149316989)
    ·
      refine ⟨69948359246345856805993871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186528957990255618149316989 69948359246345856805993871)
      ·
        refine ⟨104922538869518785208990807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69948359246345856805993871 104922538869518785208990807)
        ·
          refine ⟨157383808304278177813486211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104922538869518785208990807 157383808304278177813486211)
          ·
            refine ⟨236075712456417266720229317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157383808304278177813486211 236075712456417266720229317)
            ·
              refine ⟨44264196085578237510042997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236075712456417266720229317 44264196085578237510042997)
              ·
                refine ⟨4149768383022959766566531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44264196085578237510042997 4149768383022959766566531)
                ·
                  refine ⟨6224652574534439649849797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4149768383022959766566531 6224652574534439649849797)
                  ·
                    refine ⟨1167122357725207434346837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6224652574534439649849797 1167122357725207434346837)
                    ·
                      rfl

theorem cell23_6818888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_6818888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818888 prefixEnd_6818888 := by exact prefixLift 6818888
  have htrace : WordTrace (prefixWord ++ tailWord_6818888) baseStart_6818888 baseEnd_6818888 := by
    simpa [prefixWord, tailWord_6818888, baseEnd_6818888] using wordTrace_append hprefix tailTrace_6818888
  have hstable : (prefixWord ++ tailWord_6818888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818888).length < 2 ^ (prefixWord ++ tailWord_6818888).sum := by decide
  have hdescent : baseEnd_6818888 < baseStart_6818888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818898 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_6818898 : Nat := 118140960795 + 6818898 * 2 ^ 59
def prefixEnd_6818898 : Nat := 4983230072969 + 3 ^ 40 * 6818898 * 2
def baseEnd_6818898 : Nat := 3501372207982167263915465

theorem tailTrace_6818898 : CollatzResearch.WordTrace tailWord_6818898 prefixEnd_6818898 3501372207982167263915465 := by
  unfold tailWord_6818898
  simp only [CollatzResearch.WordTrace]
  refine ⟨62176410512576148976738337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165803761366869730604635565 62176410512576148976738337)
  ·
    refine ⟨46632307884432111732553753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62176410512576148976738337 46632307884432111732553753)
    ·
      refine ⟨34974230913324083799415315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46632307884432111732553753 34974230913324083799415315)
      ·
        refine ⟨52461346369986125699122973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34974230913324083799415315 52461346369986125699122973)
        ·
          refine ⟨19673004888744797137171115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52461346369986125699122973 19673004888744797137171115)
          ·
            refine ⟨29509507333117195705756673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19673004888744797137171115 29509507333117195705756673)
            ·
              refine ⟨22132130499837896779317505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29509507333117195705756673 22132130499837896779317505)
              ·
                refine ⟨16599097874878422584488129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22132130499837896779317505 16599097874878422584488129)
                ·
                  refine ⟨12449323406158816938366097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16599097874878422584488129 12449323406158816938366097)
                  ·
                    refine ⟨9336992554619112703774573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12449323406158816938366097 9336992554619112703774573)
                    ·
                      refine ⟨3501372207982167263915465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9336992554619112703774573 3501372207982167263915465)
                      ·
                        rfl

theorem cell23_6818898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_6818898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818898 prefixEnd_6818898 := by exact prefixLift 6818898
  have htrace : WordTrace (prefixWord ++ tailWord_6818898) baseStart_6818898 baseEnd_6818898 := by
    simpa [prefixWord, tailWord_6818898, baseEnd_6818898] using wordTrace_append hprefix tailTrace_6818898
  have hstable : (prefixWord ++ tailWord_6818898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818898).length < 2 ^ (prefixWord ++ tailWord_6818898).sum := by decide
  have hdescent : baseEnd_6818898 < baseStart_6818898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818901 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 6]
def baseStart_6818901 : Nat := 118140960795 + 6818901 * 2 ^ 59
def prefixEnd_6818901 : Nat := 4983230072969 + 3 ^ 40 * 6818901 * 2
def baseEnd_6818901 : Nat := 389041527602681194686439

theorem tailTrace_6818901 : CollatzResearch.WordTrace tailWord_6818901 prefixEnd_6818901 389041527602681194686439 := by
  unfold tailWord_6818901
  simp only [CollatzResearch.WordTrace]
  refine ⟨248705751469293727419312557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165803834312862484946208371 248705751469293727419312557)
  ·
    refine ⟨93264656800985147782242209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248705751469293727419312557 93264656800985147782242209)
    ·
      refine ⟨69948492600738860836681657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93264656800985147782242209 69948492600738860836681657)
      ·
        refine ⟨52461369450554145627511243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69948492600738860836681657 52461369450554145627511243)
        ·
          refine ⟨78692054175831218441266865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52461369450554145627511243 78692054175831218441266865)
          ·
            refine ⟨59019040631873413830950149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78692054175831218441266865 59019040631873413830950149)
            ·
              refine ⟨11066070118476265093303153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59019040631873413830950149 11066070118476265093303153)
              ·
                refine ⟨8299552588857198819977365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11066070118476265093303153 8299552588857198819977365)
                ·
                  refine ⟨389041527602681194686439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8299552588857198819977365 389041527602681194686439)
                  ·
                    rfl

theorem cell23_6818901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_6818901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818901 prefixEnd_6818901 := by exact prefixLift 6818901
  have htrace : WordTrace (prefixWord ++ tailWord_6818901) baseStart_6818901 baseEnd_6818901 := by
    simpa [prefixWord, tailWord_6818901, baseEnd_6818901] using wordTrace_append hprefix tailTrace_6818901
  have hstable : (prefixWord ++ tailWord_6818901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818901).length < 2 ^ (prefixWord ++ tailWord_6818901).sum := by decide
  have hdescent : baseEnd_6818901 < baseStart_6818901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818904 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_6818904 : Nat := 118140960795 + 6818904 * 2 ^ 59
def prefixEnd_6818904 : Nat := 4983230072969 + 3 ^ 40 * 6818904 * 2
def baseEnd_6818904 : Nat := 3501375288866094240440437

theorem tailTrace_6818904 : CollatzResearch.WordTrace tailWord_6818904 prefixEnd_6818904 3501375288866094240440437 := by
  unfold tailWord_6818904
  simp only [CollatzResearch.WordTrace]
  refine ⟨124352930444141429465835883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165803907258855239287781177 124352930444141429465835883)
  ·
    refine ⟨186529395666212144198753825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124352930444141429465835883 186529395666212144198753825)
    ·
      refine ⟨139897046749659108149065369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186529395666212144198753825 139897046749659108149065369)
      ·
        refine ⟨104922785062244331111799027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139897046749659108149065369 104922785062244331111799027)
        ·
          refine ⟨157384177593366496667698541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104922785062244331111799027 157384177593366496667698541)
          ·
            refine ⟨59019066597512436250386953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157384177593366496667698541 59019066597512436250386953)
            ·
              refine ⟨44264299948134327187790215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59019066597512436250386953 44264299948134327187790215)
              ·
                refine ⟨66396449922201490781685323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44264299948134327187790215 66396449922201490781685323)
                ·
                  refine ⟨99594674883302236172527985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66396449922201490781685323 99594674883302236172527985)
                  ·
                    refine ⟨74696006162476677129395989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99594674883302236172527985 74696006162476677129395989)
                    ·
                      refine ⟨3501375288866094240440437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74696006162476677129395989 3501375288866094240440437)
                      ·
                        rfl

theorem cell23_6818904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_6818904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818904 prefixEnd_6818904 := by exact prefixLift 6818904
  have htrace : WordTrace (prefixWord ++ tailWord_6818904) baseStart_6818904 baseEnd_6818904 := by
    simpa [prefixWord, tailWord_6818904, baseEnd_6818904] using wordTrace_append hprefix tailTrace_6818904
  have hstable : (prefixWord ++ tailWord_6818904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818904).length < 2 ^ (prefixWord ++ tailWord_6818904).sum := by decide
  have hdescent : baseEnd_6818904 < baseStart_6818904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818924 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_6818924 : Nat := 118140960795 + 6818924 * 2 ^ 59
def prefixEnd_6818924 : Nat := 4983230072969 + 3 ^ 40 * 6818924 * 2
def baseEnd_6818924 : Nat := 3501385558479184162190345

theorem tailTrace_6818924 : CollatzResearch.WordTrace tailWord_6818924 prefixEnd_6818924 3501385558479184162190345 := by
  unfold tailWord_6818924
  simp only [CollatzResearch.WordTrace]
  refine ⟨124353295174105201173699913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165804393565473601564933217 124353295174105201173699913)
  ·
    refine ⟨93264971380578900880274935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124353295174105201173699913 93264971380578900880274935)
    ·
      refine ⟨139897457070868351320412403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93264971380578900880274935 139897457070868351320412403)
      ·
        refine ⟨209846185606302526980618605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139897457070868351320412403 209846185606302526980618605)
        ·
          refine ⟨78692319602363447617731977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209846185606302526980618605 78692319602363447617731977)
          ·
            refine ⟨59019239701772585713298983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78692319602363447617731977 59019239701772585713298983)
            ·
              refine ⟨88528859552658878569948475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59019239701772585713298983 88528859552658878569948475)
              ·
                refine ⟨132793289328988317854922713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88528859552658878569948475 132793289328988317854922713)
                ·
                  refine ⟨99594966996741238391192035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132793289328988317854922713 99594966996741238391192035)
                  ·
                    refine ⟨149392450495111857586788053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99594966996741238391192035 149392450495111857586788053)
                    ·
                      refine ⟨3501385558479184162190345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149392450495111857586788053 3501385558479184162190345)
                      ·
                        rfl

theorem cell23_6818924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_6818924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818924 prefixEnd_6818924 := by exact prefixLift 6818924
  have htrace : WordTrace (prefixWord ++ tailWord_6818924) baseStart_6818924 baseEnd_6818924 := by
    simpa [prefixWord, tailWord_6818924, baseEnd_6818924] using wordTrace_append hprefix tailTrace_6818924
  have hstable : (prefixWord ++ tailWord_6818924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818924).length < 2 ^ (prefixWord ++ tailWord_6818924).sum := by decide
  have hdescent : baseEnd_6818924 < baseStart_6818924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818928 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 3, 1, 3]
def baseStart_6818928 : Nat := 118140960795 + 6818928 * 2 ^ 59
def prefixEnd_6818928 : Nat := 4983230072969 + 3 ^ 40 * 6818928 * 2
def baseEnd_6818928 : Nat := 3501387612401802146540327

theorem tailTrace_6818928 : CollatzResearch.WordTrace tailWord_6818928 prefixEnd_6818928 3501387612401802146540327 := by
  unfold tailWord_6818928
  simp only [CollatzResearch.WordTrace]
  refine ⟨124353368120097955515272719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165804490826797274020363625 124353368120097955515272719)
  ·
    refine ⟨186530052180146933272909079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124353368120097955515272719 186530052180146933272909079)
    ·
      refine ⟨279795078270220399909363619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186530052180146933272909079 279795078270220399909363619)
      ·
        refine ⟨419692617405330599864045429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279795078270220399909363619 419692617405330599864045429)
        ·
          refine ⟨39346182881749743737254259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 419692617405330599864045429 39346182881749743737254259)
          ·
            refine ⟨59019274322624615605881389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39346182881749743737254259 59019274322624615605881389)
            ·
              refine ⟨22132227870984230852205521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59019274322624615605881389 22132227870984230852205521)
              ·
                refine ⟨16599170903238173139154141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22132227870984230852205521 16599170903238173139154141)
                ·
                  refine ⟨6224689088714314927182803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16599170903238173139154141 6224689088714314927182803)
                  ·
                    refine ⟨9337033633071472390774205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6224689088714314927182803 9337033633071472390774205)
                    ·
                      refine ⟨3501387612401802146540327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9337033633071472390774205 3501387612401802146540327)
                      ·
                        rfl

theorem cell23_6818928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 3, 1, 3].length) (baseStart_6818928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818928 prefixEnd_6818928 := by exact prefixLift 6818928
  have htrace : WordTrace (prefixWord ++ tailWord_6818928) baseStart_6818928 baseEnd_6818928 := by
    simpa [prefixWord, tailWord_6818928, baseEnd_6818928] using wordTrace_append hprefix tailTrace_6818928
  have hstable : (prefixWord ++ tailWord_6818928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818928).length < 2 ^ (prefixWord ++ tailWord_6818928).sum := by decide
  have hdescent : baseEnd_6818928 < baseStart_6818928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818948 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_6818948 : Nat := 118140960795 + 6818948 * 2 ^ 59
def prefixEnd_6818948 : Nat := 4983230072969 + 3 ^ 40 * 6818948 * 2
def baseEnd_6818948 : Nat := 1167132627338297356096745

theorem tailTrace_6818948 : CollatzResearch.WordTrace tailWord_6818948 prefixEnd_6818948 1167132627338297356096745 := by
  unfold tailWord_6818948
  simp only [CollatzResearch.WordTrace]
  refine ⟨124353732850061727223136749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165804977133415636297515665 124353732850061727223136749)
  ·
    refine ⟨46632649818773147708676281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124353732850061727223136749 46632649818773147708676281)
    ·
      refine ⟨34974487364079860781507211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46632649818773147708676281 34974487364079860781507211)
      ·
        refine ⟨52461731046119791172260817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34974487364079860781507211 52461731046119791172260817)
        ·
          refine ⟨39346298284589843379195613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52461731046119791172260817 39346298284589843379195613)
          ·
            refine ⟨14754861856721191267198355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39346298284589843379195613 14754861856721191267198355)
            ·
              refine ⟨22132292785081786900797533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14754861856721191267198355 22132292785081786900797533)
              ·
                refine ⟨8299609794405670087799075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22132292785081786900797533 8299609794405670087799075)
                ·
                  refine ⟨12449414691608505131698613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8299609794405670087799075 12449414691608505131698613)
                  ·
                    refine ⟨1167132627338297356096745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12449414691608505131698613 1167132627338297356096745)
                    ·
                      rfl

theorem cell23_6818948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_6818948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818948 prefixEnd_6818948 := by exact prefixLift 6818948
  have htrace : WordTrace (prefixWord ++ tailWord_6818948) baseStart_6818948 baseEnd_6818948 := by
    simpa [prefixWord, tailWord_6818948, baseEnd_6818948] using wordTrace_append hprefix tailTrace_6818948
  have hstable : (prefixWord ++ tailWord_6818948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818948).length < 2 ^ (prefixWord ++ tailWord_6818948).sum := by decide
  have hdescent : baseEnd_6818948 < baseStart_6818948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818962 : List Nat := [3, 2, 3, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_6818962 : Nat := 118140960795 + 6818962 * 2 ^ 59
def prefixEnd_6818962 : Nat := 4983230072969 + 3 ^ 40 * 6818962 * 2
def baseEnd_6818962 : Nat := 3501405070744055013515171

theorem tailTrace_6818962 : CollatzResearch.WordTrace tailWord_6818962 prefixEnd_6818962 3501405070744055013515171 := by
  unfold tailWord_6818962
  simp only [CollatzResearch.WordTrace]
  refine ⟨62176994080518183709320785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165805317548048489891522093 62176994080518183709320785)
  ·
    refine ⟨46632745560388637781990589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62176994080518183709320785 46632745560388637781990589)
    ·
      refine ⟨17487279585145739168246471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46632745560388637781990589 17487279585145739168246471)
      ·
        refine ⟨26230919377718608752369707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17487279585145739168246471 26230919377718608752369707)
        ·
          refine ⟨39346379066577913128554561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26230919377718608752369707 39346379066577913128554561)
          ·
            refine ⟨29509784299933434846415921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39346379066577913128554561 29509784299933434846415921)
            ·
              refine ⟨22132338224950076134811941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29509784299933434846415921 22132338224950076134811941)
              ·
                refine ⟨4149813417178139275277239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22132338224950076134811941 4149813417178139275277239)
                ·
                  refine ⟨6224720125767208912915859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4149813417178139275277239 6224720125767208912915859)
                  ·
                    refine ⟨9337080188650813369373789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6224720125767208912915859 9337080188650813369373789)
                    ·
                      refine ⟨3501405070744055013515171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9337080188650813369373789 3501405070744055013515171)
                      ·
                        rfl

theorem cell23_6818962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_6818962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818962 prefixEnd_6818962 := by exact prefixLift 6818962
  have htrace : WordTrace (prefixWord ++ tailWord_6818962) baseStart_6818962 baseEnd_6818962 := by
    simpa [prefixWord, tailWord_6818962, baseEnd_6818962] using wordTrace_append hprefix tailTrace_6818962
  have hstable : (prefixWord ++ tailWord_6818962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818962).length < 2 ^ (prefixWord ++ tailWord_6818962).sum := by decide
  have hdescent : baseEnd_6818962 < baseStart_6818962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818981 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_6818981 : Nat := 118140960795 + 6818981 * 2 ^ 59
def prefixEnd_6818981 : Nat := 4983230072969 + 3 ^ 40 * 6818981 * 2
def baseEnd_6818981 : Nat := 3501414826876490439177583

theorem tailTrace_6818981 : CollatzResearch.WordTrace tailWord_6818981 prefixEnd_6818981 3501414826876490439177583 := by
  unfold tailWord_6818981
  simp only [CollatzResearch.WordTrace]
  refine ⟨248708669309003901082224797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165805779539335934054816531 248708669309003901082224797)
  ·
    refine ⟨93265750990876462905834299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248708669309003901082224797 93265750990876462905834299)
    ·
      refine ⟨139898626486314694358751449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93265750990876462905834299 139898626486314694358751449)
      ·
        refine ⟨104923969864736020769063587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139898626486314694358751449 104923969864736020769063587)
        ·
          refine ⟨157385954797104031153595381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104923969864736020769063587 157385954797104031153595381)
          ·
            refine ⟨14754933262228502920649567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157385954797104031153595381 14754933262228502920649567)
            ·
              refine ⟨22132399893342754380974351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14754933262228502920649567 22132399893342754380974351)
              ·
                refine ⟨33198599840014131571461527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22132399893342754380974351 33198599840014131571461527)
                ·
                  refine ⟨49797899760021197357192291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33198599840014131571461527 49797899760021197357192291)
                  ·
                    refine ⟨74696849640031796035788437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49797899760021197357192291 74696849640031796035788437)
                    ·
                      refine ⟨3501414826876490439177583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74696849640031796035788437 3501414826876490439177583)
                      ·
                        rfl

theorem cell23_6818981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_6818981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818981 prefixEnd_6818981 := by exact prefixLift 6818981
  have htrace : WordTrace (prefixWord ++ tailWord_6818981) baseStart_6818981 baseEnd_6818981 := by
    simpa [prefixWord, tailWord_6818981, baseEnd_6818981] using wordTrace_append hprefix tailTrace_6818981
  have hstable : (prefixWord ++ tailWord_6818981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818981).length < 2 ^ (prefixWord ++ tailWord_6818981).sum := by decide
  have hdescent : baseEnd_6818981 < baseStart_6818981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6818991 : List Nat := [1, 1, 2, 1, 2, 3, 6, 7]
def baseStart_6818991 : Nat := 118140960795 + 6818991 * 2 ^ 59
def prefixEnd_6818991 : Nat := 4983230072969 + 3 ^ 40 * 6818991 * 2
def baseEnd_6818991 : Nat := 129682220803075385187131

theorem tailTrace_6818991 : CollatzResearch.WordTrace tailWord_6818991 prefixEnd_6818991 129682220803075385187131 := by
  unfold tailWord_6818991
  simp only [CollatzResearch.WordTrace]
  refine ⟨248709034038967672790088827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165806022692645115193392551 248709034038967672790088827)
  ·
    refine ⟨373063551058451509185133241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248709034038967672790088827 373063551058451509185133241)
    ·
      refine ⟨279797663293838631888849931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373063551058451509185133241 279797663293838631888849931)
      ·
        refine ⟨419696494940757947833274897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279797663293838631888849931 419696494940757947833274897)
        ·
          refine ⟨314772371205568460874956173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419696494940757947833274897 314772371205568460874956173)
          ·
            refine ⟨118039639202088172828108565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314772371205568460874956173 118039639202088172828108565)
            ·
              refine ⟨5533108087597883101317589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118039639202088172828108565 5533108087597883101317589)
              ·
                refine ⟨129682220803075385187131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5533108087597883101317589 129682220803075385187131)
                ·
                  rfl

theorem cell23_6818991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 7].length) (baseStart_6818991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6818991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6818991 prefixEnd_6818991 := by exact prefixLift 6818991
  have htrace : WordTrace (prefixWord ++ tailWord_6818991) baseStart_6818991 baseEnd_6818991 := by
    simpa [prefixWord, tailWord_6818991, baseEnd_6818991] using wordTrace_append hprefix tailTrace_6818991
  have hstable : (prefixWord ++ tailWord_6818991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6818991).length < 2 ^ (prefixWord ++ tailWord_6818991).sum := by decide
  have hdescent : baseEnd_6818991 < baseStart_6818991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6818991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819008 : List Nat := [2, 1, 1, 2, 7, 1, 9]
def baseStart_6819008 : Nat := 118140960795 + 6819008 * 2 ^ 59
def prefixEnd_6819008 : Nat := 4983230072969 + 3 ^ 40 * 6819008 * 2
def baseEnd_6819008 : Nat := 43227514701903232512839

theorem tailTrace_6819008 : CollatzResearch.WordTrace tailWord_6819008 prefixEnd_6819008 43227514701903232512839 := by
  unfold tailWord_6819008
  simp only [CollatzResearch.WordTrace]
  refine ⟨124354827039953042346728839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165806436053270723128971785 124354827039953042346728839)
  ·
    refine ⟨186532240559929563520093259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124354827039953042346728839 186532240559929563520093259)
    ·
      refine ⟨279798360839894345280139889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186532240559929563520093259 279798360839894345280139889)
      ·
        refine ⟨209848770629920758960104917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279798360839894345280139889 209848770629920758960104917)
        ·
          refine ⟨4918330561638767788127459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 209848770629920758960104917 4918330561638767788127459)
          ·
            refine ⟨7377495842458151682191189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918330561638767788127459 7377495842458151682191189)
            ·
              refine ⟨43227514701903232512839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7377495842458151682191189 43227514701903232512839)
              ·
                rfl

theorem cell23_6819008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 9].length) (baseStart_6819008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819008 prefixEnd_6819008 := by exact prefixLift 6819008
  have htrace : WordTrace (prefixWord ++ tailWord_6819008) baseStart_6819008 baseEnd_6819008 := by
    simpa [prefixWord, tailWord_6819008, baseEnd_6819008] using wordTrace_append hprefix tailTrace_6819008
  have hstable : (prefixWord ++ tailWord_6819008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819008).length < 2 ^ (prefixWord ++ tailWord_6819008).sum := by decide
  have hdescent : baseEnd_6819008 < baseStart_6819008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819081 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 7]
def baseStart_6819081 : Nat := 118140960795 + 6819081 * 2 ^ 59
def prefixEnd_6819081 : Nat := 4983230072969 + 3 ^ 40 * 6819081 * 2
def baseEnd_6819081 : Nat := 389051797215771116436347

theorem tailTrace_6819081 : CollatzResearch.WordTrace tailWord_6819081 prefixEnd_6819081 389051797215771116436347 := by
  unfold tailWord_6819081
  simp only [CollatzResearch.WordTrace]
  refine ⟨248712316608641618160865097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165808211072427745440576731 248712316608641618160865097)
  ·
    refine ⟨186534237456481213620648823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248712316608641618160865097 186534237456481213620648823)
    ·
      refine ⟨279801356184721820430973235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186534237456481213620648823 279801356184721820430973235)
      ·
        refine ⟨419702034277082730646459853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279801356184721820430973235 419702034277082730646459853)
        ·
          refine ⟨157388262853906023992422445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419702034277082730646459853 157388262853906023992422445)
          ·
            refine ⟨59020598570214758997158417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157388262853906023992422445 59020598570214758997158417)
            ·
              refine ⟨44265448927661069247868813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59020598570214758997158417 44265448927661069247868813)
              ·
                refine ⟨16599543347872900967950805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44265448927661069247868813 16599543347872900967950805)
                ·
                  refine ⟨389051797215771116436347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16599543347872900967950805 389051797215771116436347)
                  ·
                    rfl

theorem cell23_6819081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 7].length) (baseStart_6819081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819081 prefixEnd_6819081 := by exact prefixLift 6819081
  have htrace : WordTrace (prefixWord ++ tailWord_6819081) baseStart_6819081 baseEnd_6819081 := by
    simpa [prefixWord, tailWord_6819081, baseEnd_6819081] using wordTrace_append hprefix tailTrace_6819081
  have hstable : (prefixWord ++ tailWord_6819081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819081).length < 2 ^ (prefixWord ++ tailWord_6819081).sum := by decide
  have hdescent : baseEnd_6819081 < baseStart_6819081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819098 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 7]
def baseStart_6819098 : Nat := 118140960795 + 6819098 * 2 ^ 59
def prefixEnd_6819098 : Nat := 4983230072969 + 3 ^ 40 * 6819098 * 2
def baseEnd_6819098 : Nat := 389052767123674053490505

theorem tailTrace_6819098 : CollatzResearch.WordTrace tailWord_6819098 prefixEnd_6819098 389052767123674053490505 := by
  unfold tailWord_6819098
  simp only [CollatzResearch.WordTrace]
  refine ⟨62178234162395007516058487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165808624433053353376155965 62178234162395007516058487)
  ·
    refine ⟨93267351243592511274087731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62178234162395007516058487 93267351243592511274087731)
    ·
      refine ⟨139901026865388766911131597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93267351243592511274087731 139901026865388766911131597)
      ·
        refine ⟨52462885074520787591674349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139901026865388766911131597 52462885074520787591674349)
        ·
          refine ⟨19673581902945295346877881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52462885074520787591674349 19673581902945295346877881)
          ·
            refine ⟨14755186427208971510158411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19673581902945295346877881 14755186427208971510158411)
            ·
              refine ⟨22132779640813457265237617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14755186427208971510158411 22132779640813457265237617)
              ·
                refine ⟨16599584730610092948928213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22132779640813457265237617 16599584730610092948928213)
                ·
                  refine ⟨389052767123674053490505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16599584730610092948928213 389052767123674053490505)
                  ·
                    rfl

theorem cell23_6819098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_6819098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819098 prefixEnd_6819098 := by exact prefixLift 6819098
  have htrace : WordTrace (prefixWord ++ tailWord_6819098) baseStart_6819098 baseEnd_6819098 := by
    simpa [prefixWord, tailWord_6819098, baseEnd_6819098] using wordTrace_append hprefix tailTrace_6819098
  have hstable : (prefixWord ++ tailWord_6819098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819098).length < 2 ^ (prefixWord ++ tailWord_6819098).sum := by decide
  have hdescent : baseEnd_6819098 < baseStart_6819098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819108 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_6819108 : Nat := 118140960795 + 6819108 * 2 ^ 59
def prefixEnd_6819108 : Nat := 4983230072969 + 3 ^ 40 * 6819108 * 2
def baseEnd_6819108 : Nat := 3501480038919611442289499

theorem tailTrace_6819108 : CollatzResearch.WordTrace tailWord_6819108 prefixEnd_6819108 3501480038919611442289499 := by
  unfold tailWord_6819108
  simp only [CollatzResearch.WordTrace]
  refine ⟨124356650689771900886048989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165808867586362534514731985 124356650689771900886048989)
  ·
    refine ⟨46633744008664462832268371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124356650689771900886048989 46633744008664462832268371)
    ·
      refine ⟨69950616012996694248402557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46633744008664462832268371 69950616012996694248402557)
      ·
        refine ⟨26231481004873760343150959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69950616012996694248402557 26231481004873760343150959)
        ·
          refine ⟨39347221507310640514726439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26231481004873760343150959 39347221507310640514726439)
          ·
            refine ⟨59020832260965960772089659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39347221507310640514726439 59020832260965960772089659)
            ·
              refine ⟨88531248391448941158134489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59020832260965960772089659 88531248391448941158134489)
              ·
                refine ⟨66398436293586705868600867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88531248391448941158134489 66398436293586705868600867)
                ·
                  refine ⟨99597654440380058802901301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66398436293586705868600867 99597654440380058802901301)
                  ·
                    refine ⟨9337280103785630512771997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99597654440380058802901301 9337280103785630512771997)
                    ·
                      refine ⟨3501480038919611442289499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9337280103785630512771997 3501480038919611442289499)
                      ·
                        rfl

theorem cell23_6819108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_6819108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819108 prefixEnd_6819108 := by exact prefixLift 6819108
  have htrace : WordTrace (prefixWord ++ tailWord_6819108) baseStart_6819108 baseEnd_6819108 := by
    simpa [prefixWord, tailWord_6819108, baseEnd_6819108] using wordTrace_append hprefix tailTrace_6819108
  have hstable : (prefixWord ++ tailWord_6819108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819108).length < 2 ^ (prefixWord ++ tailWord_6819108).sum := by decide
  have hdescent : baseEnd_6819108 < baseStart_6819108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819126 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_6819126 : Nat := 118140960795 + 6819126 * 2 ^ 59
def prefixEnd_6819126 : Nat := 4983230072969 + 3 ^ 40 * 6819126 * 2
def baseEnd_6819126 : Nat := 3501489281571392371864417

theorem tailTrace_6819126 : CollatzResearch.WordTrace tailWord_6819126 prefixEnd_6819126 3501489281571392371864417 := by
  unfold tailWord_6819126
  simp only [CollatzResearch.WordTrace]
  refine ⟨15544622368342411927890827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165809305262319060564168821 15544622368342411927890827)
  ·
    refine ⟨23316933552513617891836241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15544622368342411927890827 23316933552513617891836241)
    ·
      refine ⟨17487700164385213418877181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23316933552513617891836241 17487700164385213418877181)
      ·
        refine ⟨6557887561644455032078943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17487700164385213418877181 6557887561644455032078943)
        ·
          refine ⟨9836831342466682548118415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6557887561644455032078943 9836831342466682548118415)
          ·
            refine ⟨14755247013700023822177623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9836831342466682548118415 14755247013700023822177623)
            ·
              refine ⟨22132870520550035733266435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14755247013700023822177623 22132870520550035733266435)
              ·
                refine ⟨33199305780825053599899653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22132870520550035733266435 33199305780825053599899653)
                ·
                  refine ⟨6224869833904697549981185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33199305780825053599899653 6224869833904697549981185)
                  ·
                    refine ⟨4668652375428523162485889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6224869833904697549981185 4668652375428523162485889)
                    ·
                      refine ⟨3501489281571392371864417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668652375428523162485889 3501489281571392371864417)
                      ·
                        rfl

theorem cell23_6819126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_6819126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819126 prefixEnd_6819126 := by exact prefixLift 6819126
  have htrace : WordTrace (prefixWord ++ tailWord_6819126) baseStart_6819126 baseEnd_6819126 := by
    simpa [prefixWord, tailWord_6819126, baseEnd_6819126] using wordTrace_append hprefix tailTrace_6819126
  have hstable : (prefixWord ++ tailWord_6819126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819126).length < 2 ^ (prefixWord ++ tailWord_6819126).sum := by decide
  have hdescent : baseEnd_6819126 < baseStart_6819126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819148 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_6819148 : Nat := 118140960795 + 6819148 * 2 ^ 59
def prefixEnd_6819148 : Nat := 4983230072969 + 3 ^ 40 * 6819148 * 2
def baseEnd_6819148 : Nat := 3501500578145791285789315

theorem tailTrace_6819148 : CollatzResearch.WordTrace tailWord_6819148 prefixEnd_6819148 3501500578145791285789315 := by
  unfold tailWord_6819148
  simp only [CollatzResearch.WordTrace]
  refine ⟨124357380149699444301777049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165809840199599259069036065 124357380149699444301777049)
  ·
    refine ⟨93268035112274583226332787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124357380149699444301777049 93268035112274583226332787)
    ·
      refine ⟨139902052668411874839499181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93268035112274583226332787 139902052668411874839499181)
      ·
        refine ⟨52463269750654453064812193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139902052668411874839499181 52463269750654453064812193)
        ·
          refine ⟨39347452312990839798609145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52463269750654453064812193 39347452312990839798609145)
          ·
            refine ⟨29510589234743129848956859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39347452312990839798609145 29510589234743129848956859)
            ·
              refine ⟨44265883852114694773435289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29510589234743129848956859 44265883852114694773435289)
              ·
                refine ⟨33199412889086021080076467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44265883852114694773435289 33199412889086021080076467)
                ·
                  refine ⟨49799119333629031620114701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33199412889086021080076467 49799119333629031620114701)
                  ·
                    refine ⟨18674669750110886857543013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49799119333629031620114701 18674669750110886857543013)
                    ·
                      refine ⟨3501500578145791285789315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18674669750110886857543013 3501500578145791285789315)
                      ·
                        rfl

theorem cell23_6819148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_6819148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819148 prefixEnd_6819148 := by exact prefixLift 6819148
  have htrace : WordTrace (prefixWord ++ tailWord_6819148) baseStart_6819148 baseEnd_6819148 := by
    simpa [prefixWord, tailWord_6819148, baseEnd_6819148] using wordTrace_append hprefix tailTrace_6819148
  have hstable : (prefixWord ++ tailWord_6819148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819148).length < 2 ^ (prefixWord ++ tailWord_6819148).sum := by decide
  have hdescent : baseEnd_6819148 < baseStart_6819148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819151 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_6819151 : Nat := 118140960795 + 6819151 * 2 ^ 59
def prefixEnd_6819151 : Nat := 4983230072969 + 3 ^ 40 * 6819151 * 2
def baseEnd_6819151 : Nat := 3501502118587754774051801

theorem tailTrace_6819151 : CollatzResearch.WordTrace tailWord_6819151 prefixEnd_6819151 3501502118587754774051801 := by
  unfold tailWord_6819151
  simp only [CollatzResearch.WordTrace]
  refine ⟨248714869718388020115913307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165809913145592013410608871 248714869718388020115913307)
  ·
    refine ⟨373072304577582030173869961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248714869718388020115913307 373072304577582030173869961)
    ·
      refine ⟨279804228433186522630402471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373072304577582030173869961 279804228433186522630402471)
      ·
        refine ⟨419706342649779783945603707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279804228433186522630402471 419706342649779783945603707)
        ·
          refine ⟨629559513974669675918405561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419706342649779783945603707 629559513974669675918405561)
          ·
            refine ⟨472169635481002256938804171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629559513974669675918405561 472169635481002256938804171)
            ·
              refine ⟨708254453221503385408206257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472169635481002256938804171 708254453221503385408206257)
              ·
                refine ⟨531190839916127539056154693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708254453221503385408206257 531190839916127539056154693)
                ·
                  refine ⟨99598282484273913573029005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 531190839916127539056154693 99598282484273913573029005)
                  ·
                    refine ⟨37349355931602717589885877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99598282484273913573029005 37349355931602717589885877)
                    ·
                      refine ⟨3501502118587754774051801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37349355931602717589885877 3501502118587754774051801)
                      ·
                        rfl

theorem cell23_6819151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_6819151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819151 prefixEnd_6819151 := by exact prefixLift 6819151
  have htrace : WordTrace (prefixWord ++ tailWord_6819151) baseStart_6819151 baseEnd_6819151 := by
    simpa [prefixWord, tailWord_6819151, baseEnd_6819151] using wordTrace_append hprefix tailTrace_6819151
  have hstable : (prefixWord ++ tailWord_6819151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819151).length < 2 ^ (prefixWord ++ tailWord_6819151).sum := by decide
  have hdescent : baseEnd_6819151 < baseStart_6819151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819205 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 6]
def baseStart_6819205 : Nat := 118140960795 + 6819205 * 2 ^ 59
def prefixEnd_6819205 : Nat := 4983230072969 + 3 ^ 40 * 6819205 * 2
def baseEnd_6819205 : Nat := 389058871838121951419617

theorem tailTrace_6819205 : CollatzResearch.WordTrace tailWord_6819205 prefixEnd_6819205 389058871838121951419617 := by
  unfold tailWord_6819205
  simp only [CollatzResearch.WordTrace]
  refine ⟨248716839260192387338379069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165811226173461591558919379 248716839260192387338379069)
  ·
    refine ⟨93268814722572145251892151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248716839260192387338379069 93268814722572145251892151)
    ·
      refine ⟨139903222083858217877838227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93268814722572145251892151 139903222083858217877838227)
      ·
        refine ⟨209854833125787326816757341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139903222083858217877838227 209854833125787326816757341)
        ·
          refine ⟨78695562422170247556284003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209854833125787326816757341 78695562422170247556284003)
          ·
            refine ⟨118043343633255371334426005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78695562422170247556284003 118043343633255371334426005)
            ·
              refine ⟨5533281732808845531301219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118043343633255371334426005 5533281732808845531301219)
              ·
                refine ⟨8299922599213268296951829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533281732808845531301219 8299922599213268296951829)
                ·
                  refine ⟨389058871838121951419617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8299922599213268296951829 389058871838121951419617)
                  ·
                    rfl

theorem cell23_6819205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_6819205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819205 prefixEnd_6819205 := by exact prefixLift 6819205
  have htrace : WordTrace (prefixWord ++ tailWord_6819205) baseStart_6819205 baseEnd_6819205 := by
    simpa [prefixWord, tailWord_6819205, baseEnd_6819205] using wordTrace_append hprefix tailTrace_6819205
  have hstable : (prefixWord ++ tailWord_6819205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819205).length < 2 ^ (prefixWord ++ tailWord_6819205).sum := by decide
  have hdescent : baseEnd_6819205 < baseStart_6819205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819249 : List Nat := [1, 2, 2, 4, 1, 1, 3, 4, 1, 1, 3]
def baseStart_6819249 : Nat := 118140960795 + 6819249 * 2 ^ 59
def prefixEnd_6819249 : Nat := 4983230072969 + 3 ^ 40 * 6819249 * 2
def baseEnd_6819249 : Nat := 3501552439691895390626351

theorem tailTrace_6819249 : CollatzResearch.WordTrace tailWord_6819249 prefixEnd_6819249 3501552439691895390626351 := by
  unfold tailWord_6819249
  simp only [CollatzResearch.WordTrace]
  refine ⟨248718444072032982852980801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165812296048021988568653867 248718444072032982852980801)
  ·
    refine ⟨186538833054024737139735601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248718444072032982852980801 186538833054024737139735601)
    ·
      refine ⟨139904124790518552854801701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186538833054024737139735601 139904124790518552854801701)
      ·
        refine ⟨26232023398222228660275319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139904124790518552854801701 26232023398222228660275319)
        ·
          refine ⟨39348035097333342990412979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26232023398222228660275319 39348035097333342990412979)
          ·
            refine ⟨59022052646000014485619469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39348035097333342990412979 59022052646000014485619469)
            ·
              refine ⟨22133269742250005432107301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59022052646000014485619469 22133269742250005432107301)
              ·
                refine ⟨4149988076671876018520119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22133269742250005432107301 4149988076671876018520119)
                ·
                  refine ⟨6224982115007814027780179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4149988076671876018520119 6224982115007814027780179)
                  ·
                    refine ⟨9337473172511721041670269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6224982115007814027780179 9337473172511721041670269)
                    ·
                      refine ⟨3501552439691895390626351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9337473172511721041670269 3501552439691895390626351)
                      ·
                        rfl

theorem cell23_6819249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_6819249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819249 prefixEnd_6819249 := by exact prefixLift 6819249
  have htrace : WordTrace (prefixWord ++ tailWord_6819249) baseStart_6819249 baseEnd_6819249 := by
    simpa [prefixWord, tailWord_6819249, baseEnd_6819249] using wordTrace_append hprefix tailTrace_6819249
  have hstable : (prefixWord ++ tailWord_6819249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819249).length < 2 ^ (prefixWord ++ tailWord_6819249).sum := by decide
  have hdescent : baseEnd_6819249 < baseStart_6819249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819275 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 3]
def baseStart_6819275 : Nat := 118140960795 + 6819275 * 2 ^ 59
def prefixEnd_6819275 : Nat := 4983230072969 + 3 ^ 40 * 6819275 * 2
def baseEnd_6819275 : Nat := 3501565790188912288901231

theorem tailTrace_6819275 : CollatzResearch.WordTrace tailWord_6819275 prefixEnd_6819275 3501565790188912288901231 := by
  unfold tailWord_6819275
  simp only [CollatzResearch.WordTrace]
  refine ⟨248719392369938789293427279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165812928246625859528951519 248719392369938789293427279)
  ·
    refine ⟨373079088554908183940140919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248719392369938789293427279 373079088554908183940140919)
    ·
      refine ⟨559618632832362275910211379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373079088554908183940140919 559618632832362275910211379)
      ·
        refine ⟨839427949248543413865317069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559618632832362275910211379 839427949248543413865317069)
        ·
          refine ⟨314785480968203780199493901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 839427949248543413865317069 314785480968203780199493901)
          ·
            refine ⟨118044555363076417574810213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314785480968203780199493901 118044555363076417574810213)
            ·
              refine ⟨22133354130576828295276915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118044555363076417574810213 22133354130576828295276915)
              ·
                refine ⟨33200031195865242442915373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22133354130576828295276915 33200031195865242442915373)
                ·
                  refine ⟨12450011698449465916093265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33200031195865242442915373 12450011698449465916093265)
                  ·
                    refine ⟨9337508773837099437069949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12450011698449465916093265 9337508773837099437069949)
                    ·
                      refine ⟨3501565790188912288901231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9337508773837099437069949 3501565790188912288901231)
                      ·
                        rfl

theorem cell23_6819275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 3].length) (baseStart_6819275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819275 prefixEnd_6819275 := by exact prefixLift 6819275
  have htrace : WordTrace (prefixWord ++ tailWord_6819275) baseStart_6819275 baseEnd_6819275 := by
    simpa [prefixWord, tailWord_6819275, baseEnd_6819275] using wordTrace_append hprefix tailTrace_6819275
  have hstable : (prefixWord ++ tailWord_6819275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819275).length < 2 ^ (prefixWord ++ tailWord_6819275).sum := by decide
  have hdescent : baseEnd_6819275 < baseStart_6819275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819278 : List Nat := [4, 1, 1, 1, 2, 1, 2, 11]
def baseStart_6819278 : Nat := 118140960795 + 6819278 * 2 ^ 59
def prefixEnd_6819278 : Nat := 4983230072969 + 3 ^ 40 * 6819278 * 2
def baseEnd_6819278 : Nat := 129687678912254658413471

theorem tailTrace_6819278 : CollatzResearch.WordTrace tailWord_6819278 prefixEnd_6819278 129687678912254658413471 := by
  unfold tailWord_6819278
  simp only [CollatzResearch.WordTrace]
  refine ⟨31089937723615990100723311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165813001192618613870524325 31089937723615990100723311)
  ·
    refine ⟨46634906585423985151084967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31089937723615990100723311 46634906585423985151084967)
    ·
      refine ⟨69952359878135977726627451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46634906585423985151084967 69952359878135977726627451)
      ·
        refine ⟨104928539817203966589941177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69952359878135977726627451 104928539817203966589941177)
        ·
          refine ⟨78696404862902974942455883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104928539817203966589941177 78696404862902974942455883)
          ·
            refine ⟨118044607294354462413683825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78696404862902974942455883 118044607294354462413683825)
            ·
              refine ⟨88533455470765846810262869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118044607294354462413683825 88533455470765846810262869)
              ·
                refine ⟨129687678912254658413471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 88533455470765846810262869 129687678912254658413471)
                ·
                  rfl

theorem cell23_6819278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_6819278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819278 prefixEnd_6819278 := by exact prefixLift 6819278
  have htrace : WordTrace (prefixWord ++ tailWord_6819278) baseStart_6819278 baseEnd_6819278 := by
    simpa [prefixWord, tailWord_6819278, baseEnd_6819278] using wordTrace_append hprefix tailTrace_6819278
  have hstable : (prefixWord ++ tailWord_6819278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819278).length < 2 ^ (prefixWord ++ tailWord_6819278).sum := by decide
  have hdescent : baseEnd_6819278 < baseStart_6819278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819285 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6819285 : Nat := 118140960795 + 6819285 * 2 ^ 59
def prefixEnd_6819285 : Nat := 4983230072969 + 3 ^ 40 * 6819285 * 2
def baseEnd_6819285 : Nat := 3501570924995457249776185

theorem tailTrace_6819285 : CollatzResearch.WordTrace tailWord_6819285 prefixEnd_6819285 3501570924995457249776185 := by
  unfold tailWord_6819285
  simp only [CollatzResearch.WordTrace]
  refine ⟨248719757099902561001291309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165813171399935040667527539 248719757099902561001291309)
  ·
    refine ⟨93269908912463460375484241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248719757099902561001291309 93269908912463460375484241)
    ·
      refine ⟨69952431684347595281613181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93269908912463460375484241 69952431684347595281613181)
      ·
        refine ⟨26232161881630348230604943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69952431684347595281613181 26232161881630348230604943)
        ·
          refine ⟨39348242822445522345907415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26232161881630348230604943 39348242822445522345907415)
          ·
            refine ⟨59022364233668283518861123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39348242822445522345907415 59022364233668283518861123)
            ·
              refine ⟨88533546350502425278291685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59022364233668283518861123 88533546350502425278291685)
              ·
                refine ⟨16600039940719204739679691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88533546350502425278291685 16600039940719204739679691)
                ·
                  refine ⟨24900059911078807109519537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16600039940719204739679691 24900059911078807109519537)
                  ·
                    refine ⟨18675044933309105332139653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24900059911078807109519537 18675044933309105332139653)
                    ·
                      refine ⟨3501570924995457249776185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18675044933309105332139653 3501570924995457249776185)
                      ·
                        rfl

theorem cell23_6819285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6819285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819285 prefixEnd_6819285 := by exact prefixLift 6819285
  have htrace : WordTrace (prefixWord ++ tailWord_6819285) baseStart_6819285 baseEnd_6819285 := by
    simpa [prefixWord, tailWord_6819285, baseEnd_6819285] using wordTrace_append hprefix tailTrace_6819285
  have hstable : (prefixWord ++ tailWord_6819285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819285).length < 2 ^ (prefixWord ++ tailWord_6819285).sum := by decide
  have hdescent : baseEnd_6819285 < baseStart_6819285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819286 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_6819286 : Nat := 118140960795 + 6819286 * 2 ^ 59
def prefixEnd_6819286 : Nat := 4983230072969 + 3 ^ 40 * 6819286 * 2
def baseEnd_6819286 : Nat := 1167190479492037248621227

theorem tailTrace_6819286 : CollatzResearch.WordTrace tailWord_6819286 prefixEnd_6819286 1167190479492037248621227 := by
  unfold tailWord_6819286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15544987098306183635754857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165813195715265958781385141 15544987098306183635754857)
  ·
    refine ⟨11658740323729637726816143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15544987098306183635754857 11658740323729637726816143)
    ·
      refine ⟨17488110485594456590224215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11658740323729637726816143 17488110485594456590224215)
      ·
        refine ⟨26232165728391684885336323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17488110485594456590224215 26232165728391684885336323)
        ·
          refine ⟨39348248592587527328004485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26232165728391684885336323 39348248592587527328004485)
          ·
            refine ⟨7377796611110161374000841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39348248592587527328004485 7377796611110161374000841)
            ·
              refine ⟨5533347458332621030500631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7377796611110161374000841 5533347458332621030500631)
              ·
                refine ⟨8300021187498931545750947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533347458332621030500631 8300021187498931545750947)
                ·
                  refine ⟨12450031781248397318626421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8300021187498931545750947 12450031781248397318626421)
                  ·
                    refine ⟨1167190479492037248621227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12450031781248397318626421 1167190479492037248621227)
                    ·
                      rfl

theorem cell23_6819286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_6819286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819286 prefixEnd_6819286 := by exact prefixLift 6819286
  have htrace : WordTrace (prefixWord ++ tailWord_6819286) baseStart_6819286 baseEnd_6819286 := by
    simpa [prefixWord, tailWord_6819286, baseEnd_6819286] using wordTrace_append hprefix tailTrace_6819286
  have hstable : (prefixWord ++ tailWord_6819286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819286).length < 2 ^ (prefixWord ++ tailWord_6819286).sum := by decide
  have hdescent : baseEnd_6819286 < baseStart_6819286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819289 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 1, 1, 4]
def baseStart_6819289 : Nat := 118140960795 + 6819289 * 2 ^ 59
def prefixEnd_6819289 : Nat := 4983230072969 + 3 ^ 40 * 6819289 * 2
def baseEnd_6819289 : Nat := 3501572978918075234126167

theorem tailTrace_6819289 : CollatzResearch.WordTrace tailWord_6819289 prefixEnd_6819289 3501572978918075234126167 := by
  unfold tailWord_6819289
  simp only [CollatzResearch.WordTrace]
  refine ⟨248719902991888069684436921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165813268661258713122957947 248719902991888069684436921)
  ·
    refine ⟨186539927243916052263327691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248719902991888069684436921 186539927243916052263327691)
    ·
      refine ⟨279809890865874078394991537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186539927243916052263327691 279809890865874078394991537)
      ·
        refine ⟨209857418149405558796243653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279809890865874078394991537 209857418149405558796243653)
        ·
          refine ⟨39348265903013542274295685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209857418149405558796243653 39348265903013542274295685)
          ·
            refine ⟨7377799856815039176430441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39348265903013542274295685 7377799856815039176430441)
            ·
              refine ⟨5533349892611279382322831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7377799856815039176430441 5533349892611279382322831)
              ·
                refine ⟨8300024838916919073484247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533349892611279382322831 8300024838916919073484247)
                ·
                  refine ⟨12450037258375378610226371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8300024838916919073484247 12450037258375378610226371)
                  ·
                    refine ⟨18675055887563067915339557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12450037258375378610226371 18675055887563067915339557)
                    ·
                      refine ⟨3501572978918075234126167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18675055887563067915339557 3501572978918075234126167)
                      ·
                        rfl

theorem cell23_6819289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 1, 4].length) (baseStart_6819289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819289 prefixEnd_6819289 := by exact prefixLift 6819289
  have htrace : WordTrace (prefixWord ++ tailWord_6819289) baseStart_6819289 baseEnd_6819289 := by
    simpa [prefixWord, tailWord_6819289, baseEnd_6819289] using wordTrace_append hprefix tailTrace_6819289
  have hstable : (prefixWord ++ tailWord_6819289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819289).length < 2 ^ (prefixWord ++ tailWord_6819289).sum := by decide
  have hdescent : baseEnd_6819289 < baseStart_6819289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819299 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 2, 4]
def baseStart_6819299 : Nat := 118140960795 + 6819299 * 2 ^ 59
def prefixEnd_6819299 : Nat := 4983230072969 + 3 ^ 40 * 6819299 * 2
def baseEnd_6819299 : Nat := 1167192704574873398333707

theorem tailTrace_6819299 : CollatzResearch.WordTrace tailWord_6819299 prefixEnd_6819299 1167192704574873398333707 := by
  unfold tailWord_6819299
  simp only [CollatzResearch.WordTrace]
  refine ⟨248720267721851841392300951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165813511814567894261533967 248720267721851841392300951)
  ·
    refine ⟨373080401582777762088451427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248720267721851841392300951 373080401582777762088451427)
    ·
      refine ⟨559620602374166643132677141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373080401582777762088451427 559620602374166643132677141)
      ·
        refine ⟨26232215736289061396844241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 559620602374166643132677141 26232215736289061396844241)
        ·
          refine ⟨19674161802216796047633181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26232215736289061396844241 19674161802216796047633181)
          ·
            refine ⟨7377810675831298517862443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19674161802216796047633181 7377810675831298517862443)
            ·
              refine ⟨11066716013746947776793665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377810675831298517862443 11066716013746947776793665)
              ·
                refine ⟨8300037010310210832595249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11066716013746947776793665 8300037010310210832595249)
                ·
                  refine ⟨6225027757732658124446437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8300037010310210832595249 6225027757732658124446437)
                  ·
                    refine ⟨1167192704574873398333707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6225027757732658124446437 1167192704574873398333707)
                    ·
                      rfl

theorem cell23_6819299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 4].length) (baseStart_6819299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819299 prefixEnd_6819299 := by exact prefixLift 6819299
  have htrace : WordTrace (prefixWord ++ tailWord_6819299) baseStart_6819299 baseEnd_6819299 := by
    simpa [prefixWord, tailWord_6819299, baseEnd_6819299] using wordTrace_append hprefix tailTrace_6819299
  have hstable : (prefixWord ++ tailWord_6819299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819299).length < 2 ^ (prefixWord ++ tailWord_6819299).sum := by decide
  have hdescent : baseEnd_6819299 < baseStart_6819299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819306 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_6819306 : Nat := 118140960795 + 6819306 * 2 ^ 59
def prefixEnd_6819306 : Nat := 4983230072969 + 3 ^ 40 * 6819306 * 2
def baseEnd_6819306 : Nat := 3501581708089201667613589

theorem tailTrace_6819306 : CollatzResearch.WordTrace tailWord_6819306 prefixEnd_6819306 3501581708089201667613589 := by
  unfold tailWord_6819306
  simp only [CollatzResearch.WordTrace]
  refine ⟨62180130758206620396951443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165813682021884321058537181 62180130758206620396951443)
  ·
    refine ⟨93270196137309930595427165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62180130758206620396951443 93270196137309930595427165)
    ·
      refine ⟨34976323551491223973285187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93270196137309930595427165 34976323551491223973285187)
      ·
        refine ⟨52464485327236835959927781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34976323551491223973285187 52464485327236835959927781)
        ·
          refine ⟨9837090998856906742486459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52464485327236835959927781 9837090998856906742486459)
          ·
            refine ⟨14755636498285360113729689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9837090998856906742486459 14755636498285360113729689)
            ·
              refine ⟨11066727373714020085297267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14755636498285360113729689 11066727373714020085297267)
              ·
                refine ⟨16600091060571030127945901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11066727373714020085297267 16600091060571030127945901)
                ·
                  refine ⟨6225034147714136297979713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16600091060571030127945901 6225034147714136297979713)
                  ·
                    refine ⟨4668775610785602223484785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6225034147714136297979713 4668775610785602223484785)
                    ·
                      refine ⟨3501581708089201667613589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668775610785602223484785 3501581708089201667613589)
                      ·
                        rfl

theorem cell23_6819306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_6819306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819306 prefixEnd_6819306 := by exact prefixLift 6819306
  have htrace : WordTrace (prefixWord ++ tailWord_6819306) baseStart_6819306 baseEnd_6819306 := by
    simpa [prefixWord, tailWord_6819306, baseEnd_6819306] using wordTrace_append hprefix tailTrace_6819306
  have hstable : (prefixWord ++ tailWord_6819306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819306).length < 2 ^ (prefixWord ++ tailWord_6819306).sum := by decide
  have hdescent : baseEnd_6819306 < baseStart_6819306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819308 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_6819308 : Nat := 118140960795 + 6819308 * 2 ^ 59
def prefixEnd_6819308 : Nat := 4983230072969 + 3 ^ 40 * 6819308 * 2
def baseEnd_6819308 : Nat := 1167194245016836886596193

theorem tailTrace_6819308 : CollatzResearch.WordTrace tailWord_6819308 prefixEnd_6819308 1167194245016836886596193 := by
  unfold tailWord_6819308
  simp only [CollatzResearch.WordTrace]
  refine ⟨124360297989409617964689289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165813730652546157286252385 124360297989409617964689289)
  ·
    refine ⟨93270223492057213473516967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124360297989409617964689289 93270223492057213473516967)
    ·
      refine ⟨139905335238085820210275451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93270223492057213473516967 139905335238085820210275451)
      ·
        refine ⟨209858002857128730315413177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139905335238085820210275451 209858002857128730315413177)
        ·
          refine ⟨157393502142846547736559883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209858002857128730315413177 157393502142846547736559883)
          ·
            refine ⟨236090253214269821604839825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157393502142846547736559883 236090253214269821604839825)
            ·
              refine ⟨177067689910702366203629869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236090253214269821604839825 177067689910702366203629869)
              ·
                refine ⟨66400383716513387326361201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177067689910702366203629869 66400383716513387326361201)
                ·
                  refine ⟨49800287787385040494770901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66400383716513387326361201 49800287787385040494770901)
                  ·
                    refine ⟨1167194245016836886596193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49800287787385040494770901 1167194245016836886596193)
                    ·
                      rfl

theorem cell23_6819308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_6819308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819308 prefixEnd_6819308 := by exact prefixLift 6819308
  have htrace : WordTrace (prefixWord ++ tailWord_6819308) baseStart_6819308 baseEnd_6819308 := by
    simpa [prefixWord, tailWord_6819308, baseEnd_6819308] using wordTrace_append hprefix tailTrace_6819308
  have hstable : (prefixWord ++ tailWord_6819308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819308).length < 2 ^ (prefixWord ++ tailWord_6819308).sum := by decide
  have hdescent : baseEnd_6819308 < baseStart_6819308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819315 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 2, 7, 2]
def baseStart_6819315 : Nat := 118140960795 + 6819315 * 2 ^ 59
def prefixEnd_6819315 : Nat := 4983230072969 + 3 ^ 40 * 6819315 * 2
def baseEnd_6819315 : Nat := 3501586329415092132401047

theorem tailTrace_6819315 : CollatzResearch.WordTrace tailWord_6819315 prefixEnd_6819315 3501586329415092132401047 := by
  unfold tailWord_6819315
  simp only [CollatzResearch.WordTrace]
  refine ⟨248720851289793876124883399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165813900859862584083255599 248720851289793876124883399)
  ·
    refine ⟨373081276934690814187325099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248720851289793876124883399 373081276934690814187325099)
    ·
      refine ⟨559621915402036221280987649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373081276934690814187325099 559621915402036221280987649)
      ·
        refine ⟨419716436551527165960740737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559621915402036221280987649 419716436551527165960740737)
        ·
          refine ⟨314787327413645374470555553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419716436551527165960740737 314787327413645374470555553)
          ·
            refine ⟨236090495560234030852916665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314787327413645374470555553 236090495560234030852916665)
            ·
              refine ⟨177067871670175523139687499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236090495560234030852916665 177067871670175523139687499)
              ·
                refine ⟨265601807505263284709531249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177067871670175523139687499 265601807505263284709531249)
                ·
                  refine ⟨199201355628947463532148437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265601807505263284709531249 199201355628947463532148437)
                  ·
                    refine ⟨4668781772553456176534729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 199201355628947463532148437 4668781772553456176534729)
                    ·
                      refine ⟨3501586329415092132401047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668781772553456176534729 3501586329415092132401047)
                      ·
                        rfl

theorem cell23_6819315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 7, 2].length) (baseStart_6819315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819315 prefixEnd_6819315 := by exact prefixLift 6819315
  have htrace : WordTrace (prefixWord ++ tailWord_6819315) baseStart_6819315 baseEnd_6819315 := by
    simpa [prefixWord, tailWord_6819315, baseEnd_6819315] using wordTrace_append hprefix tailTrace_6819315
  have hstable : (prefixWord ++ tailWord_6819315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819315).length < 2 ^ (prefixWord ++ tailWord_6819315).sum := by decide
  have hdescent : baseEnd_6819315 < baseStart_6819315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819329 : List Nat := [1, 2, 4, 1, 5, 1, 2, 7]
def baseStart_6819329 : Nat := 118140960795 + 6819329 * 2 ^ 59
def prefixEnd_6819329 : Nat := 4983230072969 + 3 ^ 40 * 6819329 * 2
def baseEnd_6819329 : Nat := 129688648820157595467629

theorem tailTrace_6819329 : CollatzResearch.WordTrace tailWord_6819329 prefixEnd_6819329 129688648820157595467629 := by
  unfold tailWord_6819329
  simp only [CollatzResearch.WordTrace]
  refine ⟨248721361911743156515893041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165814241274495437677262027 248721361911743156515893041)
  ·
    refine ⟨186541021433807367386919781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248721361911743156515893041 186541021433807367386919781)
    ·
      refine ⟨34976441518838881385047459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186541021433807367386919781 34976441518838881385047459)
      ·
        refine ⟨52464662278258322077571189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34976441518838881385047459 52464662278258322077571189)
        ·
          refine ⟨4918562088586717694772299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52464662278258322077571189 4918562088586717694772299)
          ·
            refine ⟨7377843132880076542158449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918562088586717694772299 7377843132880076542158449)
            ·
              refine ⟨5533382349660057406618837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7377843132880076542158449 5533382349660057406618837)
              ·
                refine ⟨129688648820157595467629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5533382349660057406618837 129688648820157595467629)
                ·
                  rfl

theorem cell23_6819329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 7].length) (baseStart_6819329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819329 prefixEnd_6819329 := by exact prefixLift 6819329
  have htrace : WordTrace (prefixWord ++ tailWord_6819329) baseStart_6819329 baseEnd_6819329 := by
    simpa [prefixWord, tailWord_6819329, baseEnd_6819329] using wordTrace_append hprefix tailTrace_6819329
  have hstable : (prefixWord ++ tailWord_6819329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819329).length < 2 ^ (prefixWord ++ tailWord_6819329).sum := by decide
  have hdescent : baseEnd_6819329 < baseStart_6819329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819334 : List Nat := [6, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_6819334 : Nat := 118140960795 + 6819334 * 2 ^ 59
def prefixEnd_6819334 : Nat := 4983230072969 + 3 ^ 40 * 6819334 * 2
def baseEnd_6819334 : Nat := 3501596085547527558063461

theorem tailTrace_6819334 : CollatzResearch.WordTrace tailWord_6819334 prefixEnd_6819334 3501596085547527558063461 := by
  unfold tailWord_6819334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7772548258647657574057033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165814362851150028246550037 7772548258647657574057033)
  ·
    refine ⟨5829411193985743180542775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7772548258647657574057033 5829411193985743180542775)
    ·
      refine ⟨8744116790978614770814163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5829411193985743180542775 8744116790978614770814163)
      ·
        refine ⟨13116175186467922156221245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8744116790978614770814163 13116175186467922156221245)
        ·
          refine ⟨4918565694925470808582967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13116175186467922156221245 4918565694925470808582967)
          ·
            refine ⟨7377848542388206212874451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918565694925470808582967 7377848542388206212874451)
            ·
              refine ⟨11066772813582309319311677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377848542388206212874451 11066772813582309319311677)
              ·
                refine ⟨4150039805093365994741879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11066772813582309319311677 4150039805093365994741879)
                ·
                  refine ⟨6225059707640048992112819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150039805093365994741879 6225059707640048992112819)
                  ·
                    refine ⟨9337589561460073488169229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6225059707640048992112819 9337589561460073488169229)
                    ·
                      refine ⟨3501596085547527558063461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9337589561460073488169229 3501596085547527558063461)
                      ·
                        rfl

theorem cell23_6819334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_6819334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819334 prefixEnd_6819334 := by exact prefixLift 6819334
  have htrace : WordTrace (prefixWord ++ tailWord_6819334) baseStart_6819334 baseEnd_6819334 := by
    simpa [prefixWord, tailWord_6819334, baseEnd_6819334] using wordTrace_append hprefix tailTrace_6819334
  have hstable : (prefixWord ++ tailWord_6819334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819334).length < 2 ^ (prefixWord ++ tailWord_6819334).sum := by decide
  have hdescent : baseEnd_6819334 < baseStart_6819334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819335 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_6819335 : Nat := 118140960795 + 6819335 * 2 ^ 59
def prefixEnd_6819335 : Nat := 4983230072969 + 3 ^ 40 * 6819335 * 2
def baseEnd_6819335 : Nat := 3501596599028182054150955

theorem tailTrace_6819335 : CollatzResearch.WordTrace tailWord_6819335 prefixEnd_6819335 3501596599028182054150955 := by
  unfold tailWord_6819335
  simp only [CollatzResearch.WordTrace]
  refine ⟨248721580749721419540611459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165814387166480946360407639 248721580749721419540611459)
  ·
    refine ⟨373082371124582129310917189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248721580749721419540611459 373082371124582129310917189)
    ·
      refine ⟨69952944585859149245796973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373082371124582129310917189 69952944585859149245796973)
      ·
        refine ⟨26232354219697180967173865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69952944585859149245796973 26232354219697180967173865)
        ·
          refine ⟨19674265664772885725380399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26232354219697180967173865 19674265664772885725380399)
          ·
            refine ⟨29511398497159328588070599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19674265664772885725380399 29511398497159328588070599)
            ·
              refine ⟨44267097745738992882105899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29511398497159328588070599 44267097745738992882105899)
              ·
                refine ⟨66400646618608489323158849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44267097745738992882105899 66400646618608489323158849)
                ·
                  refine ⟨49800484963956366992369137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66400646618608489323158849 49800484963956366992369137)
                  ·
                    refine ⟨37350363722967275244276853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49800484963956366992369137 37350363722967275244276853)
                    ·
                      refine ⟨3501596599028182054150955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37350363722967275244276853 3501596599028182054150955)
                      ·
                        rfl

theorem cell23_6819335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_6819335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819335 prefixEnd_6819335 := by exact prefixLift 6819335
  have htrace : WordTrace (prefixWord ++ tailWord_6819335) baseStart_6819335 baseEnd_6819335 := by
    simpa [prefixWord, tailWord_6819335, baseEnd_6819335] using wordTrace_append hprefix tailTrace_6819335
  have hstable : (prefixWord ++ tailWord_6819335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819335).length < 2 ^ (prefixWord ++ tailWord_6819335).sum := by decide
  have hdescent : baseEnd_6819335 < baseStart_6819335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819340 : List Nat := [2, 2, 1, 2, 6, 1, 1, 3, 1, 2, 2]
def baseStart_6819340 : Nat := 118140960795 + 6819340 * 2 ^ 59
def prefixEnd_6819340 : Nat := 4983230072969 + 3 ^ 40 * 6819340 * 2
def baseEnd_6819340 : Nat := 3501599166431454534588433

theorem tailTrace_6819340 : CollatzResearch.WordTrace tailWord_6819340 prefixEnd_6819340 3501599166431454534588433 := by
  unfold tailWord_6819340
  simp only [CollatzResearch.WordTrace]
  refine ⟨124360881557351652697271737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165814508743135536929695649 124360881557351652697271737)
  ·
    refine ⟨93270661168013739522953803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124360881557351652697271737 93270661168013739522953803)
    ·
      refine ⟨139905991752020609284430705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93270661168013739522953803 139905991752020609284430705)
      ·
        refine ⟨104929493814015456963323029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139905991752020609284430705 104929493814015456963323029)
        ·
          refine ⟨4918570022531974545155767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104929493814015456963323029 4918570022531974545155767)
          ·
            refine ⟨7377855033797961817733651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918570022531974545155767 7377855033797961817733651)
            ·
              refine ⟨11066782550696942726600477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377855033797961817733651 11066782550696942726600477)
              ·
                refine ⟨4150043456511353522475179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11066782550696942726600477 4150043456511353522475179)
                ·
                  refine ⟨6225065184767030283712769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150043456511353522475179 6225065184767030283712769)
                  ·
                    refine ⟨4668798888575272712784577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6225065184767030283712769 4668798888575272712784577)
                    ·
                      refine ⟨3501599166431454534588433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668798888575272712784577 3501599166431454534588433)
                      ·
                        rfl

theorem cell23_6819340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_6819340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819340 prefixEnd_6819340 := by exact prefixLift 6819340
  have htrace : WordTrace (prefixWord ++ tailWord_6819340) baseStart_6819340 baseEnd_6819340 := by
    simpa [prefixWord, tailWord_6819340, baseEnd_6819340] using wordTrace_append hprefix tailTrace_6819340
  have hstable : (prefixWord ++ tailWord_6819340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819340).length < 2 ^ (prefixWord ++ tailWord_6819340).sum := by decide
  have hdescent : baseEnd_6819340 < baseStart_6819340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819349 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 1, 3, 2]
def baseStart_6819349 : Nat := 118140960795 + 6819349 * 2 ^ 59
def prefixEnd_6819349 : Nat := 4983230072969 + 3 ^ 40 * 6819349 * 2
def baseEnd_6819349 : Nat := 3501603787757344999375891

theorem tailTrace_6819349 : CollatzResearch.WordTrace tailWord_6819349 prefixEnd_6819349 3501603787757344999375891 := by
  unfold tailWord_6819349
  simp only [CollatzResearch.WordTrace]
  refine ⟨248722091371670699931621101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165814727581113799954414067 248722091371670699931621101)
  ·
    refine ⟨93270784264376512474357913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248722091371670699931621101 93270784264376512474357913)
    ·
      refine ⟨69953088198282384355768435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93270784264376512474357913 69953088198282384355768435)
      ·
        refine ⟨104929632297423576533652653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69953088198282384355768435 104929632297423576533652653)
        ·
          refine ⟨39348612111533841200119745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104929632297423576533652653 39348612111533841200119745)
          ·
            refine ⟨29511459083650380900089809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39348612111533841200119745 29511459083650380900089809)
            ·
              refine ⟨22133594312737785675067357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29511459083650380900089809 22133594312737785675067357)
              ·
                refine ⟨8300097867276669628150259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22133594312737785675067357 8300097867276669628150259)
                ·
                  refine ⟨12450146800915004442225389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8300097867276669628150259 12450146800915004442225389)
                  ·
                    refine ⟨4668805050343126665834521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12450146800915004442225389 4668805050343126665834521)
                    ·
                      refine ⟨3501603787757344999375891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668805050343126665834521 3501603787757344999375891)
                      ·
                        rfl

theorem cell23_6819349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_6819349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819349 prefixEnd_6819349 := by exact prefixLift 6819349
  have htrace : WordTrace (prefixWord ++ tailWord_6819349) baseStart_6819349 baseEnd_6819349 := by
    simpa [prefixWord, tailWord_6819349, baseEnd_6819349] using wordTrace_append hprefix tailTrace_6819349
  have hstable : (prefixWord ++ tailWord_6819349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819349).length < 2 ^ (prefixWord ++ tailWord_6819349).sum := by decide
  have hdescent : baseEnd_6819349 < baseStart_6819349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819365 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 2, 4, 3]
def baseStart_6819365 : Nat := 118140960795 + 6819365 * 2 ^ 59
def prefixEnd_6819365 : Nat := 4983230072969 + 3 ^ 40 * 6819365 * 2
def baseEnd_6819365 : Nat := 3501612003447816936775817

theorem tailTrace_6819365 : CollatzResearch.WordTrace tailWord_6819365 prefixEnd_6819365 3501612003447816936775817 := by
  unfold tailWord_6819365
  simp only [CollatzResearch.WordTrace]
  refine ⟨248722674939612734664203549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165815116626408489776135699 248722674939612734664203549)
  ·
    refine ⟨93271003102354775499076331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248722674939612734664203549 93271003102354775499076331)
    ·
      refine ⟨139906504653532163248614497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93271003102354775499076331 139906504653532163248614497)
      ·
        refine ⟨104929878490149122436460873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139906504653532163248614497 104929878490149122436460873)
        ·
          refine ⟨78697408867611841827345655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104929878490149122436460873 78697408867611841827345655)
          ·
            refine ⟨118046113301417762741018483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78697408867611841827345655 118046113301417762741018483)
            ·
              refine ⟨177069169952126644111527725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118046113301417762741018483 177069169952126644111527725)
              ·
                refine ⟨66400938732047491541822897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177069169952126644111527725 66400938732047491541822897)
                ·
                  refine ⟨49800704049035618656367173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66400938732047491541822897 49800704049035618656367173)
                  ·
                    refine ⟨9337632009194178498068845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49800704049035618656367173 9337632009194178498068845)
                    ·
                      refine ⟨3501612003447816936775817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9337632009194178498068845 3501612003447816936775817)
                      ·
                        rfl

theorem cell23_6819365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_6819365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819365 prefixEnd_6819365 := by exact prefixLift 6819365
  have htrace : WordTrace (prefixWord ++ tailWord_6819365) baseStart_6819365 baseEnd_6819365 := by
    simpa [prefixWord, tailWord_6819365, baseEnd_6819365] using wordTrace_append hprefix tailTrace_6819365
  have hstable : (prefixWord ++ tailWord_6819365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819365).length < 2 ^ (prefixWord ++ tailWord_6819365).sum := by decide
  have hdescent : baseEnd_6819365 < baseStart_6819365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819395 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 3]
def baseStart_6819395 : Nat := 118140960795 + 6819395 * 2 ^ 59
def prefixEnd_6819395 : Nat := 4983230072969 + 3 ^ 40 * 6819395 * 2
def baseEnd_6819395 : Nat := 3501627407867451819400679

theorem tailTrace_6819395 : CollatzResearch.WordTrace tailWord_6819395 prefixEnd_6819395 3501627407867451819400679 := by
  unfold tailWord_6819395
  simp only [CollatzResearch.WordTrace]
  refine ⟨248723769129504049787795639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165815846086336033191863759 248723769129504049787795639)
  ·
    refine ⟨373085653694256074681693459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248723769129504049787795639 373085653694256074681693459)
    ·
      refine ⟨559628480541384112022540189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373085653694256074681693459 559628480541384112022540189)
      ·
        refine ⟨209860680203019042008452571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559628480541384112022540189 209860680203019042008452571)
        ·
          refine ⟨314791020304528563012678857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209860680203019042008452571 314791020304528563012678857)
          ·
            refine ⟨236093265228396422259509143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314791020304528563012678857 236093265228396422259509143)
            ·
              refine ⟨354139897842594633389263715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236093265228396422259509143 354139897842594633389263715)
              ·
                refine ⟨531209846763891950083895573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354139897842594633389263715 531209846763891950083895573)
                ·
                  refine ⟨24900461567057435160182605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 531209846763891950083895573 24900461567057435160182605)
                  ·
                    refine ⟨9337673087646538185068477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24900461567057435160182605 9337673087646538185068477)
                    ·
                      refine ⟨3501627407867451819400679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9337673087646538185068477 3501627407867451819400679)
                      ·
                        rfl

theorem cell23_6819395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_6819395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819395 prefixEnd_6819395 := by exact prefixLift 6819395
  have htrace : WordTrace (prefixWord ++ tailWord_6819395) baseStart_6819395 baseEnd_6819395 := by
    simpa [prefixWord, tailWord_6819395, baseEnd_6819395] using wordTrace_append hprefix tailTrace_6819395
  have hstable : (prefixWord ++ tailWord_6819395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819395).length < 2 ^ (prefixWord ++ tailWord_6819395).sum := by decide
  have hdescent : baseEnd_6819395 < baseStart_6819395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819402 : List Nat := [3, 1, 2, 1, 1, 3, 2, 5, 5]
def baseStart_6819402 : Nat := 118140960795 + 6819402 * 2 ^ 59
def prefixEnd_6819402 : Nat := 4983230072969 + 3 ^ 40 * 6819402 * 2
def baseEnd_6819402 : Nat := 389070111359114810223683

theorem tailTrace_6819402 : CollatzResearch.WordTrace tailWord_6819402 prefixEnd_6819402 389070111359114810223683 := by
  unfold tailWord_6819402
  simp only [CollatzResearch.WordTrace]
  refine ⟨62181006110119672495825115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165816016293652459988866973 62181006110119672495825115)
  ·
    refine ⟨93271509165179508743737673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62181006110119672495825115 93271509165179508743737673)
    ·
      refine ⟨69953631873884631557803255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93271509165179508743737673 69953631873884631557803255)
      ·
        refine ⟨104930447810826947336704883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69953631873884631557803255 104930447810826947336704883)
        ·
          refine ⟨157395671716240421005057325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104930447810826947336704883 157395671716240421005057325)
          ·
            refine ⟨59023376893590157876896497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157395671716240421005057325 59023376893590157876896497)
            ·
              refine ⟨44267532670192618407672373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59023376893590157876896497 44267532670192618407672373)
              ·
                refine ⟨4150081187830557975719285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44267532670192618407672373 4150081187830557975719285)
                ·
                  refine ⟨389070111359114810223683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4150081187830557975719285 389070111359114810223683)
                  ·
                    rfl

theorem cell23_6819402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_6819402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819402 prefixEnd_6819402 := by exact prefixLift 6819402
  have htrace : WordTrace (prefixWord ++ tailWord_6819402) baseStart_6819402 baseEnd_6819402 := by
    simpa [prefixWord, tailWord_6819402, baseEnd_6819402] using wordTrace_append hprefix tailTrace_6819402
  have hstable : (prefixWord ++ tailWord_6819402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819402).length < 2 ^ (prefixWord ++ tailWord_6819402).sum := by decide
  have hdescent : baseEnd_6819402 < baseStart_6819402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819412 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_6819412 : Nat := 118140960795 + 6819412 * 2 ^ 59
def prefixEnd_6819412 : Nat := 4983230072969 + 3 ^ 40 * 6819412 * 2
def baseEnd_6819412 : Nat := 3501636137038578252888101

theorem tailTrace_6819412 : CollatzResearch.WordTrace tailWord_6819412 prefixEnd_6819412 3501636137038578252888101 := by
  unfold tailWord_6819412
  simp only [CollatzResearch.WordTrace]
  refine ⟨124362194585221230845582245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165816259446961641127442993 124362194585221230845582245)
  ·
    refine ⟨23317911484728980783546671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124362194585221230845582245 23317911484728980783546671)
    ·
      refine ⟨34976867227093471175320007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23317911484728980783546671 34976867227093471175320007)
      ·
        refine ⟨52465300840640206762980011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34976867227093471175320007 52465300840640206762980011)
        ·
          refine ⟨78697951260960310144470017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52465300840640206762980011 78697951260960310144470017)
          ·
            refine ⟨59023463445720232608352513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78697951260960310144470017 59023463445720232608352513)
            ·
              refine ⟨44267597584290174456264385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59023463445720232608352513 44267597584290174456264385)
              ·
                refine ⟨33200698188217630842198289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44267597584290174456264385 33200698188217630842198289)
                ·
                  refine ⟨24900523641163223131648717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33200698188217630842198289 24900523641163223131648717)
                  ·
                    refine ⟨9337696365436208674368269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24900523641163223131648717 9337696365436208674368269)
                    ·
                      refine ⟨3501636137038578252888101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9337696365436208674368269 3501636137038578252888101)
                      ·
                        rfl

theorem cell23_6819412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_6819412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819412 prefixEnd_6819412 := by exact prefixLift 6819412
  have htrace : WordTrace (prefixWord ++ tailWord_6819412) baseStart_6819412 baseEnd_6819412 := by
    simpa [prefixWord, tailWord_6819412, baseEnd_6819412] using wordTrace_append hprefix tailTrace_6819412
  have hstable : (prefixWord ++ tailWord_6819412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819412).length < 2 ^ (prefixWord ++ tailWord_6819412).sum := by decide
  have hdescent : baseEnd_6819412 < baseStart_6819412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819425 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_6819425 : Nat := 118140960795 + 6819425 * 2 ^ 59
def prefixEnd_6819425 : Nat := 4983230072969 + 3 ^ 40 * 6819425 * 2
def baseEnd_6819425 : Nat := 3501642812287086702025541

theorem tailTrace_6819425 : CollatzResearch.WordTrace tailWord_6819425 prefixEnd_6819425 3501642812287086702025541 := by
  unfold tailWord_6819425
  simp only [CollatzResearch.WordTrace]
  refine ⟨248724863319395364911387729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165816575546263576607591819 248724863319395364911387729)
  ·
    refine ⟨186543647489546523683540797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248724863319395364911387729 186543647489546523683540797)
    ·
      refine ⟨69953867808579946381327799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186543647489546523683540797 69953867808579946381327799)
      ·
        refine ⟨104930801712869919571991699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69953867808579946381327799 104930801712869919571991699)
        ·
          refine ⟨157396202569304879357987549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104930801712869919571991699 157396202569304879357987549)
          ·
            refine ⟨59023575963489329759245331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157396202569304879357987549 59023575963489329759245331)
            ·
              refine ⟨88535363945233994638867997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59023575963489329759245331 88535363945233994638867997)
              ·
                refine ⟨33200761479462747989575499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88535363945233994638867997 33200761479462747989575499)
                ·
                  refine ⟨49801142219194121984363249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33200761479462747989575499 49801142219194121984363249)
                  ·
                    refine ⟨37350856664395591488272437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49801142219194121984363249 37350856664395591488272437)
                    ·
                      refine ⟨3501642812287086702025541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37350856664395591488272437 3501642812287086702025541)
                      ·
                        rfl

theorem cell23_6819425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_6819425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819425 prefixEnd_6819425 := by exact prefixLift 6819425
  have htrace : WordTrace (prefixWord ++ tailWord_6819425) baseStart_6819425 baseEnd_6819425 := by
    simpa [prefixWord, tailWord_6819425, baseEnd_6819425] using wordTrace_append hprefix tailTrace_6819425
  have hstable : (prefixWord ++ tailWord_6819425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819425).length < 2 ^ (prefixWord ++ tailWord_6819425).sum := by decide
  have hdescent : baseEnd_6819425 < baseStart_6819425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819452 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 3, 6, 2]
def baseStart_6819452 : Nat := 118140960795 + 6819452 * 2 ^ 59
def prefixEnd_6819452 : Nat := 4983230072969 + 3 ^ 40 * 6819452 * 2
def baseEnd_6819452 : Nat := 3501656676264758096387917

theorem tailTrace_6819452 : CollatzResearch.WordTrace tailWord_6819452 prefixEnd_6819452 3501656676264758096387917 := by
  unfold tailWord_6819452
  simp only [CollatzResearch.WordTrace]
  refine ⟨124362924045148774261310305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165817232060198365681747073 124362924045148774261310305)
  ·
    refine ⟨93272193033861580695982729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124362924045148774261310305 93272193033861580695982729)
    ·
      refine ⟨69954144775396185521987047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93272193033861580695982729 69954144775396185521987047)
      ·
        refine ⟨104931217163094278282980571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69954144775396185521987047 104931217163094278282980571)
        ·
          refine ⟨157396825744641417424470857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104931217163094278282980571 157396825744641417424470857)
          ·
            refine ⟨118047619308481063068353143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157396825744641417424470857 118047619308481063068353143)
            ·
              refine ⟨177071428962721594602529715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118047619308481063068353143 177071428962721594602529715)
              ·
                refine ⟨265607143444082391903794573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177071428962721594602529715 265607143444082391903794573)
                ·
                  refine ⟨99602678791530896963922965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265607143444082391903794573 99602678791530896963922965)
                  ·
                    refine ⟨4668875568353010795183889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99602678791530896963922965 4668875568353010795183889)
                    ·
                      refine ⟨3501656676264758096387917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668875568353010795183889 3501656676264758096387917)
                      ·
                        rfl

theorem cell23_6819452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_6819452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819452 prefixEnd_6819452 := by exact prefixLift 6819452
  have htrace : WordTrace (prefixWord ++ tailWord_6819452) baseStart_6819452 baseEnd_6819452 := by
    simpa [prefixWord, tailWord_6819452, baseEnd_6819452] using wordTrace_append hprefix tailTrace_6819452
  have hstable : (prefixWord ++ tailWord_6819452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819452).length < 2 ^ (prefixWord ++ tailWord_6819452).sum := by decide
  have hdescent : baseEnd_6819452 < baseStart_6819452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819465 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_6819465 : Nat := 118140960795 + 6819465 * 2 ^ 59
def prefixEnd_6819465 : Nat := 4983230072969 + 3 ^ 40 * 6819465 * 2
def baseEnd_6819465 : Nat := 3501663351513266545525357

theorem tailTrace_6819465 : CollatzResearch.WordTrace tailWord_6819465 prefixEnd_6819465 3501663351513266545525357 := by
  unfold tailWord_6819465
  simp only [CollatzResearch.WordTrace]
  refine ⟨248726322239250451742843849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165817548159500301161895899 248726322239250451742843849)
  ·
    refine ⟨186544741679437838807132887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248726322239250451742843849 186544741679437838807132887)
    ·
      refine ⟨279817112519156758210699331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186544741679437838807132887 279817112519156758210699331)
      ·
        refine ⟨419725668778735137316048997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279817112519156758210699331 419725668778735137316048997)
        ·
          refine ⟨78698562896012838246759187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 419725668778735137316048997 78698562896012838246759187)
          ·
            refine ⟨118047844344019257370138781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78698562896012838246759187 118047844344019257370138781)
            ·
              refine ⟨44267941629007221513802043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118047844344019257370138781 44267941629007221513802043)
              ·
                refine ⟨66401912443510832270703065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44267941629007221513802043 66401912443510832270703065)
                ·
                  refine ⟨49801434332633124203027299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66401912443510832270703065 49801434332633124203027299)
                  ·
                    refine ⟨74702151498949686304540949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49801434332633124203027299 74702151498949686304540949)
                    ·
                      refine ⟨3501663351513266545525357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74702151498949686304540949 3501663351513266545525357)
                      ·
                        rfl

theorem cell23_6819465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_6819465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819465 prefixEnd_6819465 := by exact prefixLift 6819465
  have htrace : WordTrace (prefixWord ++ tailWord_6819465) baseStart_6819465 baseEnd_6819465 := by
    simpa [prefixWord, tailWord_6819465, baseEnd_6819465] using wordTrace_append hprefix tailTrace_6819465
  have hstable : (prefixWord ++ tailWord_6819465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819465).length < 2 ^ (prefixWord ++ tailWord_6819465).sum := by decide
  have hdescent : baseEnd_6819465 < baseStart_6819465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819472 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 3]
def baseStart_6819472 : Nat := 118140960795 + 6819472 * 2 ^ 59
def prefixEnd_6819472 : Nat := 4983230072969 + 3 ^ 40 * 6819472 * 2
def baseEnd_6819472 : Nat := 3501666945877848018137825

theorem tailTrace_6819472 : CollatzResearch.WordTrace tailWord_6819472 prefixEnd_6819472 3501666945877848018137825 := by
  unfold tailWord_6819472
  simp only [CollatzResearch.WordTrace]
  refine ⟨124363288775112545969174335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165817718366816727958899113 124363288775112545969174335)
  ·
    refine ⟨186544933162668818953761503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124363288775112545969174335 186544933162668818953761503)
    ·
      refine ⟨279817399744003228430642255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186544933162668818953761503 279817399744003228430642255)
      ·
        refine ⟨419726099616004842645963383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279817399744003228430642255 419726099616004842645963383)
        ·
          refine ⟨629589149424007263968945075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419726099616004842645963383 629589149424007263968945075)
          ·
            refine ⟨944383724136010895953417613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629589149424007263968945075 944383724136010895953417613)
            ·
              refine ⟨354143896551004085982531605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 944383724136010895953417613 354143896551004085982531605)
              ·
                refine ⟨16600495150828316530431169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 354143896551004085982531605 16600495150828316530431169)
                ·
                  refine ⟨12450371363121237397823377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16600495150828316530431169 12450371363121237397823377)
                  ·
                    refine ⟨9337778522340928048367533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12450371363121237397823377 9337778522340928048367533)
                    ·
                      refine ⟨3501666945877848018137825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9337778522340928048367533 3501666945877848018137825)
                      ·
                        rfl

theorem cell23_6819472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 3].length) (baseStart_6819472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819472 prefixEnd_6819472 := by exact prefixLift 6819472
  have htrace : WordTrace (prefixWord ++ tailWord_6819472) baseStart_6819472 baseEnd_6819472 := by
    simpa [prefixWord, tailWord_6819472, baseEnd_6819472] using wordTrace_append hprefix tailTrace_6819472
  have hstable : (prefixWord ++ tailWord_6819472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819472).length < 2 ^ (prefixWord ++ tailWord_6819472).sum := by decide
  have hdescent : baseEnd_6819472 < baseStart_6819472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819479 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 3, 4]
def baseStart_6819479 : Nat := 118140960795 + 6819479 * 2 ^ 59
def prefixEnd_6819479 : Nat := 4983230072969 + 3 ^ 40 * 6819479 * 2
def baseEnd_6819479 : Nat := 1167223513414143163583431

theorem tailTrace_6819479 : CollatzResearch.WordTrace tailWord_6819479 prefixEnd_6819479 1167223513414143163583431 := by
  unfold tailWord_6819479
  simp only [CollatzResearch.WordTrace]
  refine ⟨248726832861199732133853491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165817888574133154755902327 248726832861199732133853491)
  ·
    refine ⟨373090249291799598200780237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248726832861199732133853491 373090249291799598200780237)
    ·
      refine ⟨139908843484424849325292589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373090249291799598200780237 139908843484424849325292589)
      ·
        refine ⟨52465816306659318496984721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139908843484424849325292589 52465816306659318496984721)
        ·
          refine ⟨39349362229994488872738541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52465816306659318496984721 39349362229994488872738541)
          ·
            refine ⟨14756010836247933327276953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39349362229994488872738541 14756010836247933327276953)
            ·
              refine ⟨11067008127185949995457715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14756010836247933327276953 11067008127185949995457715)
              ·
                refine ⟨16600512190778924993186573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11067008127185949995457715 16600512190778924993186573)
                ·
                  refine ⟨6225192071542096872444965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16600512190778924993186573 6225192071542096872444965)
                  ·
                    refine ⟨1167223513414143163583431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6225192071542096872444965 1167223513414143163583431)
                    ·
                      rfl

theorem cell23_6819479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_6819479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819479 prefixEnd_6819479 := by exact prefixLift 6819479
  have htrace : WordTrace (prefixWord ++ tailWord_6819479) baseStart_6819479 baseEnd_6819479 := by
    simpa [prefixWord, tailWord_6819479, baseEnd_6819479] using wordTrace_append hprefix tailTrace_6819479
  have hstable : (prefixWord ++ tailWord_6819479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819479).length < 2 ^ (prefixWord ++ tailWord_6819479).sum := by decide
  have hdescent : baseEnd_6819479 < baseStart_6819479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819486 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_6819486 : Nat := 118140960795 + 6819486 * 2 ^ 59
def prefixEnd_6819486 : Nat := 4983230072969 + 3 ^ 40 * 6819486 * 2
def baseEnd_6819486 : Nat := 3501674134607010963362761

theorem tailTrace_6819486 : CollatzResearch.WordTrace tailWord_6819486 prefixEnd_6819486 3501674134607010963362761 := by
  unfold tailWord_6819486
  simp only [CollatzResearch.WordTrace]
  refine ⟨31090886021521796541169789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165818058781449581552905541 31090886021521796541169789)
  ·
    refine ⟨11659082258070673702938671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31090886021521796541169789 11659082258070673702938671)
    ·
      refine ⟨17488623387106010554408007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11659082258070673702938671 17488623387106010554408007)
      ·
        refine ⟨26232935080659015831612011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17488623387106010554408007 26232935080659015831612011)
        ·
          refine ⟨39349402620988523747418017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26232935080659015831612011 39349402620988523747418017)
          ·
            refine ⟨29512051965741392810563513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39349402620988523747418017 29512051965741392810563513)
            ·
              refine ⟨22134038974306044607922635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29512051965741392810563513 22134038974306044607922635)
              ·
                refine ⟨33201058461459066911883953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22134038974306044607922635 33201058461459066911883953)
                ·
                  refine ⟨24900793846094300183912965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33201058461459066911883953 24900793846094300183912965)
                  ·
                    refine ⟨4668898846142681284483681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24900793846094300183912965 4668898846142681284483681)
                    ·
                      refine ⟨3501674134607010963362761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668898846142681284483681 3501674134607010963362761)
                      ·
                        rfl

theorem cell23_6819486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_6819486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819486 prefixEnd_6819486 := by exact prefixLift 6819486
  have htrace : WordTrace (prefixWord ++ tailWord_6819486) baseStart_6819486 baseEnd_6819486 := by
    simpa [prefixWord, tailWord_6819486, baseEnd_6819486] using wordTrace_append hprefix tailTrace_6819486
  have hstable : (prefixWord ++ tailWord_6819486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819486).length < 2 ^ (prefixWord ++ tailWord_6819486).sum := by decide
  have hdescent : baseEnd_6819486 < baseStart_6819486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819526 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_6819526 : Nat := 118140960795 + 6819526 * 2 ^ 59
def prefixEnd_6819526 : Nat := 4983230072969 + 3 ^ 40 * 6819526 * 2
def baseEnd_6819526 : Nat := 389077185981465645206953

theorem tailTrace_6819526 : CollatzResearch.WordTrace tailWord_6819526 prefixEnd_6819526 389077185981465645206953 := by
  unfold tailWord_6819526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7772767096625920598775451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165819031394686306107209621 7772767096625920598775451)
  ·
    refine ⟨11659150644938880898163177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7772767096625920598775451 11659150644938880898163177)
    ·
      refine ⟨8744362983704160673622383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11659150644938880898163177 8744362983704160673622383)
      ·
        refine ⟨13116544475556241010433575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8744362983704160673622383 13116544475556241010433575)
        ·
          refine ⟨19674816713334361515650363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13116544475556241010433575 19674816713334361515650363)
          ·
            refine ⟨29512225070001542273475545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19674816713334361515650363 29512225070001542273475545)
            ·
              refine ⟨22134168802501156705106659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29512225070001542273475545 22134168802501156705106659)
              ·
                refine ⟨33201253203751735057659989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22134168802501156705106659 33201253203751735057659989)
                ·
                  refine ⟨389077185981465645206953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33201253203751735057659989 389077185981465645206953)
                  ·
                    rfl

theorem cell23_6819526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_6819526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819526 prefixEnd_6819526 := by exact prefixLift 6819526
  have htrace : WordTrace (prefixWord ++ tailWord_6819526) baseStart_6819526 baseEnd_6819526 := by
    simpa [prefixWord, tailWord_6819526, baseEnd_6819526] using wordTrace_append hprefix tailTrace_6819526
  have hstable : (prefixWord ++ tailWord_6819526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819526).length < 2 ^ (prefixWord ++ tailWord_6819526).sum := by decide
  have hdescent : baseEnd_6819526 < baseStart_6819526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819562 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_6819562 : Nat := 118140960795 + 6819562 * 2 ^ 59
def prefixEnd_6819562 : Nat := 4983230072969 + 3 ^ 40 * 6819562 * 2
def baseEnd_6819562 : Nat := 3501713159136752666012411

theorem tailTrace_6819562 : CollatzResearch.WordTrace tailWord_6819562 prefixEnd_6819562 3501713159136752666012411 := by
  unfold tailWord_6819562
  simp only [CollatzResearch.WordTrace]
  refine ⟨62182465029974759327281235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165819906746599358206083293 62182465029974759327281235)
  ·
    refine ⟨93273697544962138990921853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62182465029974759327281235 93273697544962138990921853)
    ·
      refine ⟨34977636579360802121595695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93273697544962138990921853 34977636579360802121595695)
      ·
        refine ⟨52466454869041203182393543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34977636579360802121595695 52466454869041203182393543)
        ·
          refine ⟨78699682303561804773590315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52466454869041203182393543 78699682303561804773590315)
          ·
            refine ⟨118049523455342707160385473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78699682303561804773590315 118049523455342707160385473)
            ·
              refine ⟨88537142591507030370289105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118049523455342707160385473 88537142591507030370289105)
              ·
                refine ⟨66402856943630272777716829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88537142591507030370289105 66402856943630272777716829)
                ·
                  refine ⟨24901071353861352291643811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66402856943630272777716829 24901071353861352291643811)
                  ·
                    refine ⟨37351607030792028437465717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24901071353861352291643811 37351607030792028437465717)
                    ·
                      refine ⟨3501713159136752666012411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37351607030792028437465717 3501713159136752666012411)
                      ·
                        rfl

theorem cell23_6819562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_6819562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819562 prefixEnd_6819562 := by exact prefixLift 6819562
  have htrace : WordTrace (prefixWord ++ tailWord_6819562) baseStart_6819562 baseEnd_6819562 := by
    simpa [prefixWord, tailWord_6819562, baseEnd_6819562] using wordTrace_append hprefix tailTrace_6819562
  have hstable : (prefixWord ++ tailWord_6819562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819562).length < 2 ^ (prefixWord ++ tailWord_6819562).sum := by decide
  have hdescent : baseEnd_6819562 < baseStart_6819562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819582 : List Nat := [4, 2, 2, 1, 14]
def baseStart_6819582 : Nat := 118140960795 + 6819582 * 2 ^ 59
def prefixEnd_6819582 : Nat := 4983230072969 + 3 ^ 40 * 6819582 * 2
def baseEnd_6819582 : Nat := 4803461493484009036711

theorem tailTrace_6819582 : CollatzResearch.WordTrace tailWord_6819582 prefixEnd_6819582 4803461493484009036711 := by
  unfold tailWord_6819582
  simp only [CollatzResearch.WordTrace]
  refine ⟨31091323697478322590606625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165820393053217720483235333 31091323697478322590606625)
  ·
    refine ⟨23318492773108741942954969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31091323697478322590606625 23318492773108741942954969)
    ·
      refine ⟨17488869579831556457216227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23318492773108741942954969 17488869579831556457216227)
      ·
        refine ⟨26233304369747334685824341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17488869579831556457216227 26233304369747334685824341)
        ·
          refine ⟨4803461493484009036711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 26233304369747334685824341 4803461493484009036711)
          ·
            rfl

theorem cell23_6819582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 14].length) (baseStart_6819582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819582 prefixEnd_6819582 := by exact prefixLift 6819582
  have htrace : WordTrace (prefixWord ++ tailWord_6819582) baseStart_6819582 baseEnd_6819582 := by
    simpa [prefixWord, tailWord_6819582, baseEnd_6819582] using wordTrace_append hprefix tailTrace_6819582
  have hstable : (prefixWord ++ tailWord_6819582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819582).length < 2 ^ (prefixWord ++ tailWord_6819582).sum := by decide
  have hdescent : baseEnd_6819582 < baseStart_6819582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819612 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_6819612 : Nat := 118140960795 + 6819612 * 2 ^ 59
def prefixEnd_6819612 : Nat := 4983230072969 + 3 ^ 40 * 6819612 * 2
def baseEnd_6819612 : Nat := 1167246277723159156795727

theorem tailTrace_6819612 : CollatzResearch.WordTrace tailWord_6819612 prefixEnd_6819612 1167246277723159156795727 := by
  unfold tailWord_6819612
  simp only [CollatzResearch.WordTrace]
  refine ⟨124365841884858947924222545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165821122513145263898963393 124365841884858947924222545)
  ·
    refine ⟨93274381413644210943166909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124365841884858947924222545 93274381413644210943166909)
    ·
      refine ⟨34977893030116579103687591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93274381413644210943166909 34977893030116579103687591)
      ·
        refine ⟨52466839545174868655531387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34977893030116579103687591 52466839545174868655531387)
        ·
          refine ⟨78700259317762302983297081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52466839545174868655531387 78700259317762302983297081)
          ·
            refine ⟨59025194488321727237472811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78700259317762302983297081 59025194488321727237472811)
            ·
              refine ⟨88537791732482590856209217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59025194488321727237472811 88537791732482590856209217)
              ·
                refine ⟨66403343799361943142156913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88537791732482590856209217 66403343799361943142156913)
                ·
                  refine ⟨49802507849521457356617685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66403343799361943142156913 49802507849521457356617685)
                  ·
                    refine ⟨1167246277723159156795727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49802507849521457356617685 1167246277723159156795727)
                    ·
                      rfl

theorem cell23_6819612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_6819612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819612 prefixEnd_6819612 := by exact prefixLift 6819612
  have htrace : WordTrace (prefixWord ++ tailWord_6819612) baseStart_6819612 baseEnd_6819612 := by
    simpa [prefixWord, tailWord_6819612, baseEnd_6819612] using wordTrace_append hprefix tailTrace_6819612
  have hstable : (prefixWord ++ tailWord_6819612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819612).length < 2 ^ (prefixWord ++ tailWord_6819612).sum := by decide
  have hdescent : baseEnd_6819612 < baseStart_6819612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819614 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6819614 : Nat := 118140960795 + 6819614 * 2 ^ 59
def prefixEnd_6819614 : Nat := 4983230072969 + 3 ^ 40 * 6819614 * 2
def baseEnd_6819614 : Nat := 3501739860130786462562173

theorem tailTrace_6819614 : CollatzResearch.WordTrace tailWord_6819614 prefixEnd_6819614 3501739860130786462562173 := by
  unfold tailWord_6819614
  simp only [CollatzResearch.WordTrace]
  refine ⟨31091469589463831273752237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165821171143807100126678597 31091469589463831273752237)
  ·
    refine ⟨11659301096048936727657089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31091469589463831273752237 11659301096048936727657089)
    ·
      refine ⟨8744475822036702545742817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11659301096048936727657089 8744475822036702545742817)
      ·
        refine ⟨6558356866527526909307113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8744475822036702545742817 6558356866527526909307113)
        ·
          refine ⟨4918767649895645181980335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6558356866527526909307113 4918767649895645181980335)
          ·
            refine ⟨7378151474843467772970503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918767649895645181980335 7378151474843467772970503)
            ·
              refine ⟨11067227212265201659455755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378151474843467772970503 11067227212265201659455755)
              ·
                refine ⟨16600840818397802489183633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11067227212265201659455755 16600840818397802489183633)
                ·
                  refine ⟨12450630613798351866887725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16600840818397802489183633 12450630613798351866887725)
                  ·
                    refine ⟨4668986480174381950082897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12450630613798351866887725 4668986480174381950082897)
                    ·
                      refine ⟨3501739860130786462562173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4668986480174381950082897 3501739860130786462562173)
                      ·
                        rfl

theorem cell23_6819614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6819614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819614 prefixEnd_6819614 := by exact prefixLift 6819614
  have htrace : WordTrace (prefixWord ++ tailWord_6819614) baseStart_6819614 baseEnd_6819614 := by
    simpa [prefixWord, tailWord_6819614, baseEnd_6819614] using wordTrace_append hprefix tailTrace_6819614
  have hstable : (prefixWord ++ tailWord_6819614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819614).length < 2 ^ (prefixWord ++ tailWord_6819614).sum := by decide
  have hdescent : baseEnd_6819614 < baseStart_6819614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819660 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 2, 1, 3]
def baseStart_6819660 : Nat := 118140960795 + 6819660 * 2 ^ 59
def prefixEnd_6819660 : Nat := 4983230072969 + 3 ^ 40 * 6819660 * 2
def baseEnd_6819660 : Nat := 3501763480240893282586961

theorem tailTrace_6819660 : CollatzResearch.WordTrace tailWord_6819660 prefixEnd_6819660 3501763480240893282586961 := by
  unfold tailWord_6819660
  simp only [CollatzResearch.WordTrace]
  refine ⟨124366717236772000023096217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165822289649029333364128289 124366717236772000023096217)
  ·
    refine ⟨93275037927579000017322163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124366717236772000023096217 93275037927579000017322163)
    ·
      refine ⟨139912556891368500025983245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93275037927579000017322163 139912556891368500025983245)
      ·
        refine ⟨52467208834263187509743717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139912556891368500025983245 52467208834263187509743717)
        ·
          refine ⟨9837601656424347658076947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52467208834263187509743717 9837601656424347658076947)
          ·
            refine ⟨14756402484636521487115421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9837601656424347658076947 14756402484636521487115421)
            ·
              refine ⟨5533650931738695557668283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14756402484636521487115421 5533650931738695557668283)
              ·
                refine ⟨8300476397608043336502425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533650931738695557668283 8300476397608043336502425)
                ·
                  refine ⟨6225357298206032502376819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8300476397608043336502425 6225357298206032502376819)
                  ·
                    refine ⟨9338035947309048753565229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6225357298206032502376819 9338035947309048753565229)
                    ·
                      refine ⟨3501763480240893282586961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9338035947309048753565229 3501763480240893282586961)
                      ·
                        rfl

theorem cell23_6819660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_6819660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819660 prefixEnd_6819660 := by exact prefixLift 6819660
  have htrace : WordTrace (prefixWord ++ tailWord_6819660) baseStart_6819660 baseEnd_6819660 := by
    simpa [prefixWord, tailWord_6819660, baseEnd_6819660] using wordTrace_append hprefix tailTrace_6819660
  have hstable : (prefixWord ++ tailWord_6819660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819660).length < 2 ^ (prefixWord ++ tailWord_6819660).sum := by decide
  have hdescent : baseEnd_6819660 < baseStart_6819660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819773 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 2, 4, 2]
def baseStart_6819773 : Nat := 118140960795 + 6819773 * 2 ^ 59
def prefixEnd_6819773 : Nat := 4983230072969 + 3 ^ 40 * 6819773 * 2
def baseEnd_6819773 : Nat := 3501821503554851340473941

theorem tailTrace_6819773 : CollatzResearch.WordTrace tailWord_6819773 prefixEnd_6819773 3501821503554851340473941 := by
  unfold tailWord_6819773
  simp only [CollatzResearch.WordTrace]
  refine ⟨248737555922134620345055973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165825037281423080230037315 248737555922134620345055973)
  ·
    refine ⟨46638291735400241314697995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248737555922134620345055973 46638291735400241314697995)
    ·
      refine ⟨69957437603100361972046993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46638291735400241314697995 69957437603100361972046993)
      ·
        refine ⟨52468078202325271479035245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69957437603100361972046993 52468078202325271479035245)
        ·
          refine ⟨19675529325871976804638217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52468078202325271479035245 19675529325871976804638217)
          ·
            refine ⟨14756646994403982603478663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19675529325871976804638217 14756646994403982603478663)
            ·
              refine ⟨22134970491605973905217995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14756646994403982603478663 22134970491605973905217995)
              ·
                refine ⟨33202455737408960857826993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22134970491605973905217995 33202455737408960857826993)
                ·
                  refine ⟨24901841803056720643370245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33202455737408960857826993 24901841803056720643370245)
                  ·
                    refine ⟨4669095338073135120631921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24901841803056720643370245 4669095338073135120631921)
                    ·
                      refine ⟨3501821503554851340473941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669095338073135120631921 3501821503554851340473941)
                      ·
                        rfl

theorem cell23_6819773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_6819773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819773 prefixEnd_6819773 := by exact prefixLift 6819773
  have htrace : WordTrace (prefixWord ++ tailWord_6819773) baseStart_6819773 baseEnd_6819773 := by
    simpa [prefixWord, tailWord_6819773, baseEnd_6819773] using wordTrace_append hprefix tailTrace_6819773
  have hstable : (prefixWord ++ tailWord_6819773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819773).length < 2 ^ (prefixWord ++ tailWord_6819773).sum := by decide
  have hdescent : baseEnd_6819773 < baseStart_6819773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819823 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 3, 1, 3]
def baseStart_6819823 : Nat := 118140960795 + 6819823 * 2 ^ 59
def prefixEnd_6819823 : Nat := 4983230072969 + 3 ^ 40 * 6819823 * 2
def baseEnd_6819823 : Nat := 3501847177587576144848711

theorem tailTrace_6819823 : CollatzResearch.WordTrace tailWord_6819823 prefixEnd_6819823 3501847177587576144848711 := by
  unfold tailWord_6819823
  simp only [CollatzResearch.WordTrace]
  refine ⟨248739379571953478884376123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165826253047968985922917415 248739379571953478884376123)
  ·
    refine ⟨373109069357930218326564185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248739379571953478884376123 373109069357930218326564185)
    ·
      refine ⟨279831802018447663744923139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373109069357930218326564185 279831802018447663744923139)
      ·
        refine ⟨419747703027671495617384709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279831802018447663744923139 419747703027671495617384709)
        ·
          refine ⟨78702694317688405428259633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 419747703027671495617384709 78702694317688405428259633)
          ·
            refine ⟨59027020738266304071194725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78702694317688405428259633 59027020738266304071194725)
            ·
              refine ⟨11067566388424932013349011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59027020738266304071194725 11067566388424932013349011)
              ·
                refine ⟨16601349582637398020023517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11067566388424932013349011 16601349582637398020023517)
                ·
                  refine ⟨6225506093489024257508819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16601349582637398020023517 6225506093489024257508819)
                  ·
                    refine ⟨9338259140233536386263229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6225506093489024257508819 9338259140233536386263229)
                    ·
                      refine ⟨3501847177587576144848711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9338259140233536386263229 3501847177587576144848711)
                      ·
                        rfl

theorem cell23_6819823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 1, 3].length) (baseStart_6819823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819823 prefixEnd_6819823 := by exact prefixLift 6819823
  have htrace : WordTrace (prefixWord ++ tailWord_6819823) baseStart_6819823 baseEnd_6819823 := by
    simpa [prefixWord, tailWord_6819823, baseEnd_6819823] using wordTrace_append hprefix tailTrace_6819823
  have hstable : (prefixWord ++ tailWord_6819823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819823).length < 2 ^ (prefixWord ++ tailWord_6819823).sum := by decide
  have hdescent : baseEnd_6819823 < baseStart_6819823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819830 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_6819830 : Nat := 118140960795 + 6819830 * 2 ^ 59
def prefixEnd_6819830 : Nat := 4983230072969 + 3 ^ 40 * 6819830 * 2
def baseEnd_6819830 : Nat := 389094530216906401940131

theorem tailTrace_6819830 : CollatzResearch.WordTrace tailWord_6819830 prefixEnd_6819830 389094530216906401940131 := by
  unfold tailWord_6819830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15546227180183007442492559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165826423255285412719920629 15546227180183007442492559)
  ·
    refine ⟨23319340770274511163738839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15546227180183007442492559 23319340770274511163738839)
    ·
      refine ⟨34979011155411766745608259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23319340770274511163738839 34979011155411766745608259)
      ·
        refine ⟨52468516733117650118412389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34979011155411766745608259 52468516733117650118412389)
        ·
          refine ⟨9837846887459559397202323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52468516733117650118412389 9837846887459559397202323)
          ·
            refine ⟨14756770331189339095803485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9837846887459559397202323 14756770331189339095803485)
            ·
              refine ⟨5533788874196002160926307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14756770331189339095803485 5533788874196002160926307)
              ·
                refine ⟨8300683311294003241389461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533788874196002160926307 8300683311294003241389461)
                ·
                  refine ⟨389094530216906401940131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8300683311294003241389461 389094530216906401940131)
                  ·
                    rfl

theorem cell23_6819830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_6819830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819830 prefixEnd_6819830 := by exact prefixLift 6819830
  have htrace : WordTrace (prefixWord ++ tailWord_6819830) baseStart_6819830 baseEnd_6819830 := by
    simpa [prefixWord, tailWord_6819830, baseEnd_6819830] using wordTrace_append hprefix tailTrace_6819830
  have hstable : (prefixWord ++ tailWord_6819830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819830).length < 2 ^ (prefixWord ++ tailWord_6819830).sum := by decide
  have hdescent : baseEnd_6819830 < baseStart_6819830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819866 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_6819866 : Nat := 118140960795 + 6819866 * 2 ^ 59
def prefixEnd_6819866 : Nat := 4983230072969 + 3 ^ 40 * 6819866 * 2
def baseEnd_6819866 : Nat := 3501869257255719476611013

theorem tailTrace_6819866 : CollatzResearch.WordTrace tailWord_6819866 prefixEnd_6819866 3501869257255719476611013 := by
  unfold tailWord_6819866
  simp only [CollatzResearch.WordTrace]
  refine ⟨62185236977699424307047863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165827298607198464818794301 62185236977699424307047863)
  ·
    refine ⟨93277855466549136460571795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62185236977699424307047863 93277855466549136460571795)
    ·
      refine ⟨139916783199823704690857693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93277855466549136460571795 139916783199823704690857693)
      ·
        refine ⟨52468793699933889259071635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139916783199823704690857693 52468793699933889259071635)
        ·
          refine ⟨78703190549900833888607453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52468793699933889259071635 78703190549900833888607453)
          ·
            refine ⟨29513696456212812708227795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78703190549900833888607453 29513696456212812708227795)
            ·
              refine ⟨44270544684319219062341693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29513696456212812708227795 44270544684319219062341693)
              ·
                refine ⟨16601454256619707148378135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44270544684319219062341693 16601454256619707148378135)
                ·
                  refine ⟨24902181384929560722567203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16601454256619707148378135 24902181384929560722567203)
                  ·
                    refine ⟨37353272077394341083850805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24902181384929560722567203 37353272077394341083850805)
                    ·
                      refine ⟨3501869257255719476611013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37353272077394341083850805 3501869257255719476611013)
                      ·
                        rfl

theorem cell23_6819866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_6819866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819866 prefixEnd_6819866 := by exact prefixLift 6819866
  have htrace : WordTrace (prefixWord ++ tailWord_6819866) baseStart_6819866 baseEnd_6819866 := by
    simpa [prefixWord, tailWord_6819866, baseEnd_6819866] using wordTrace_append hprefix tailTrace_6819866
  have hstable : (prefixWord ++ tailWord_6819866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819866).length < 2 ^ (prefixWord ++ tailWord_6819866).sum := by decide
  have hdescent : baseEnd_6819866 < baseStart_6819866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819886 : List Nat := [4, 1, 3, 1, 1, 2, 1, 10]
def baseStart_6819886 : Nat := 118140960795 + 6819886 * 2 ^ 59
def prefixEnd_6819886 : Nat := 4983230072969 + 3 ^ 40 * 6819886 * 2
def baseEnd_6819886 : Nat := 129699241735881829568923

theorem tailTrace_6819886 : CollatzResearch.WordTrace tailWord_6819886 prefixEnd_6819886 129699241735881829568923 := by
  unfold tailWord_6819886
  simp only [CollatzResearch.WordTrace]
  refine ⟨31092709671340655080489939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165827784913816827095946341 31092709671340655080489939)
  ·
    refine ⟨46639064507010982620734909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31092709671340655080489939 46639064507010982620734909)
    ·
      refine ⟨17489649190129118482775591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46639064507010982620734909 17489649190129118482775591)
      ·
        refine ⟨26234473785193677724163387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17489649190129118482775591 26234473785193677724163387)
        ·
          refine ⟨39351710677790516586245081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26234473785193677724163387 39351710677790516586245081)
          ·
            refine ⟨29513783008342887439683811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39351710677790516586245081 29513783008342887439683811)
            ·
              refine ⟨44270674512514331159525717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29513783008342887439683811 44270674512514331159525717)
              ·
                refine ⟨129699241735881829568923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44270674512514331159525717 129699241735881829568923)
                ·
                  rfl

theorem cell23_6819886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_6819886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819886 prefixEnd_6819886 := by exact prefixLift 6819886
  have htrace : WordTrace (prefixWord ++ tailWord_6819886) baseStart_6819886 baseEnd_6819886 := by
    simpa [prefixWord, tailWord_6819886, baseEnd_6819886] using wordTrace_append hprefix tailTrace_6819886
  have hstable : (prefixWord ++ tailWord_6819886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819886).length < 2 ^ (prefixWord ++ tailWord_6819886).sum := by decide
  have hdescent : baseEnd_6819886 < baseStart_6819886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819890 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_6819890 : Nat := 118140960795 + 6819890 * 2 ^ 59
def prefixEnd_6819890 : Nat := 4983230072969 + 3 ^ 40 * 6819890 * 2
def baseEnd_6819890 : Nat := 1167293860263809127570301

theorem tailTrace_6819890 : CollatzResearch.WordTrace tailWord_6819890 prefixEnd_6819890 1167293860263809127570301 := by
  unfold tailWord_6819890
  simp only [CollatzResearch.WordTrace]
  refine ⟨62185455815677687331766281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165827882175140499551376749 62185455815677687331766281)
  ·
    refine ⟨46639091861758265498824711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62185455815677687331766281 46639091861758265498824711)
    ·
      refine ⟨69958637792637398248237067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46639091861758265498824711 69958637792637398248237067)
      ·
        refine ⟨104937956688956097372355601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69958637792637398248237067 104937956688956097372355601)
        ·
          refine ⟨78703467516717073029266701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104937956688956097372355601 78703467516717073029266701)
          ·
            refine ⟨29513800318768902385975013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78703467516717073029266701 29513800318768902385975013)
            ·
              refine ⟨5533837559769169197370315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29513800318768902385975013 5533837559769169197370315)
              ·
                refine ⟨8300756339653753796055473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533837559769169197370315 8300756339653753796055473)
                ·
                  refine ⟨6225567254740315347041605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8300756339653753796055473 6225567254740315347041605)
                  ·
                    refine ⟨1167293860263809127570301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6225567254740315347041605 1167293860263809127570301)
                    ·
                      rfl

theorem cell23_6819890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_6819890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819890 prefixEnd_6819890 := by exact prefixLift 6819890
  have htrace : WordTrace (prefixWord ++ tailWord_6819890) baseStart_6819890 baseEnd_6819890 := by
    simpa [prefixWord, tailWord_6819890, baseEnd_6819890] using wordTrace_append hprefix tailTrace_6819890
  have hstable : (prefixWord ++ tailWord_6819890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819890).length < 2 ^ (prefixWord ++ tailWord_6819890).sum := by decide
  have hdescent : baseEnd_6819890 < baseStart_6819890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819897 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 1, 1, 4]
def baseStart_6819897 : Nat := 118140960795 + 6819897 * 2 ^ 59
def prefixEnd_6819897 : Nat := 4983230072969 + 3 ^ 40 * 6819897 * 2
def baseEnd_6819897 : Nat := 3501885175156008855323371

theorem tailTrace_6819897 : CollatzResearch.WordTrace tailWord_6819897 prefixEnd_6819897 3501885175156008855323371 := by
  unfold tailWord_6819897
  simp only [CollatzResearch.WordTrace]
  refine ⟨248742078573685389522569945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165828052382456926348379963 248742078573685389522569945)
  ·
    refine ⟨186556558930264042141927459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248742078573685389522569945 186556558930264042141927459)
    ·
      refine ⟨279834838395396063212891189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186556558930264042141927459 279834838395396063212891189)
      ·
        refine ⟨26234516099568380926208549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279834838395396063212891189 26234516099568380926208549)
        ·
          refine ⟨4918971768669071423664103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26234516099568380926208549 4918971768669071423664103)
          ·
            refine ⟨7378457653003607135496155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918971768669071423664103 7378457653003607135496155)
            ·
              refine ⟨11067686479505410703244233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378457653003607135496155 11067686479505410703244233)
              ·
                refine ⟨8300764859629058027433175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11067686479505410703244233 8300764859629058027433175)
                ·
                  refine ⟨12451147289443587041149763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8300764859629058027433175 12451147289443587041149763)
                  ·
                    refine ⟨18676720934165380561724645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12451147289443587041149763 18676720934165380561724645)
                    ·
                      refine ⟨3501885175156008855323371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18676720934165380561724645 3501885175156008855323371)
                      ·
                        rfl

theorem cell23_6819897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_6819897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819897 prefixEnd_6819897 := by exact prefixLift 6819897
  have htrace : WordTrace (prefixWord ++ tailWord_6819897) baseStart_6819897 baseEnd_6819897 := by
    simpa [prefixWord, tailWord_6819897, baseEnd_6819897] using wordTrace_append hprefix tailTrace_6819897
  have hstable : (prefixWord ++ tailWord_6819897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819897).length < 2 ^ (prefixWord ++ tailWord_6819897).sum := by decide
  have hdescent : baseEnd_6819897 < baseStart_6819897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819899 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 2, 7]
def baseStart_6819899 : Nat := 118140960795 + 6819899 * 2 ^ 59
def prefixEnd_6819899 : Nat := 4983230072969 + 3 ^ 40 * 6819899 * 2
def baseEnd_6819899 : Nat := 1167295400705772615832787

theorem tailTrace_6819899 : CollatzResearch.WordTrace tailWord_6819899 prefixEnd_6819899 1167295400705772615832787 := by
  unfold tailWord_6819899
  simp only [CollatzResearch.WordTrace]
  refine ⟨248742151519678143864142751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165828101013118762576095167 248742151519678143864142751)
  ·
    refine ⟨373113227279517215796214127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248742151519678143864142751 373113227279517215796214127)
    ·
      refine ⟨559669840919275823694321191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373113227279517215796214127 559669840919275823694321191)
      ·
        refine ⟨839504761378913735541481787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559669840919275823694321191 839504761378913735541481787)
        ·
          refine ⟨1259257142068370603312222681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839504761378913735541481787 1259257142068370603312222681)
          ·
            refine ⟨944442856551277952484167011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259257142068370603312222681 944442856551277952484167011)
            ·
              refine ⟨1416664284826916928726250517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944442856551277952484167011 1416664284826916928726250517)
              ·
                refine ⟨66406138351261731034042993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1416664284826916928726250517 66406138351261731034042993)
                ·
                  refine ⟨49804603763446298275532245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66406138351261731034042993 49804603763446298275532245)
                  ·
                    refine ⟨1167295400705772615832787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49804603763446298275532245 1167295400705772615832787)
                    ·
                      rfl

theorem cell23_6819899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 7].length) (baseStart_6819899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819899 prefixEnd_6819899 := by exact prefixLift 6819899
  have htrace : WordTrace (prefixWord ++ tailWord_6819899) baseStart_6819899 baseEnd_6819899 := by
    simpa [prefixWord, tailWord_6819899, baseEnd_6819899] using wordTrace_append hprefix tailTrace_6819899
  have hstable : (prefixWord ++ tailWord_6819899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819899).length < 2 ^ (prefixWord ++ tailWord_6819899).sum := by decide
  have hdescent : baseEnd_6819899 < baseStart_6819899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819910 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6819910 : Nat := 118140960795 + 6819910 * 2 ^ 59
def prefixEnd_6819910 : Nat := 4983230072969 + 3 ^ 40 * 6819910 * 2
def baseEnd_6819910 : Nat := 3501891850404517304460811

theorem tailTrace_6819910 : CollatzResearch.WordTrace tailWord_6819910 prefixEnd_6819910 3501891850404517304460811 := by
  unfold tailWord_6819910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7773204772582446648212287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165828368481758861828528789 7773204772582446648212287)
  ·
    refine ⟨11659807158873669972318431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7773204772582446648212287 11659807158873669972318431)
    ·
      refine ⟨17489710738310504958477647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11659807158873669972318431 17489710738310504958477647)
      ·
        refine ⟨26234566107465757437716471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17489710738310504958477647 26234566107465757437716471)
        ·
          refine ⟨39351849161198636156574707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26234566107465757437716471 39351849161198636156574707)
          ·
            refine ⟨59027773741797954234862061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39351849161198636156574707 59027773741797954234862061)
            ·
              refine ⟨22135415153174232838073273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59027773741797954234862061 22135415153174232838073273)
              ·
                refine ⟨16601561364880674628554955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22135415153174232838073273 16601561364880674628554955)
                ·
                  refine ⟨24902342047321011942832433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16601561364880674628554955 24902342047321011942832433)
                  ·
                    refine ⟨18676756535490758957124325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24902342047321011942832433 18676756535490758957124325)
                    ·
                      refine ⟨3501891850404517304460811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18676756535490758957124325 3501891850404517304460811)
                      ·
                        rfl

theorem cell23_6819910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6819910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819910 prefixEnd_6819910 := by exact prefixLift 6819910
  have htrace : WordTrace (prefixWord ++ tailWord_6819910) baseStart_6819910 baseEnd_6819910 := by
    simpa [prefixWord, tailWord_6819910, baseEnd_6819910] using wordTrace_append hprefix tailTrace_6819910
  have hstable : (prefixWord ++ tailWord_6819910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819910).length < 2 ^ (prefixWord ++ tailWord_6819910).sum := by decide
  have hdescent : baseEnd_6819910 < baseStart_6819910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819917 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_6819917 : Nat := 118140960795 + 6819917 * 2 ^ 59
def prefixEnd_6819917 : Nat := 4983230072969 + 3 ^ 40 * 6819917 * 2
def baseEnd_6819917 : Nat := 3501895444769098777073279

theorem tailTrace_6819917 : CollatzResearch.WordTrace tailWord_6819917 prefixEnd_6819917 3501895444769098777073279 := by
  unfold tailWord_6819917
  simp only [CollatzResearch.WordTrace]
  refine ⟨248742808033612932938298005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165828538689075288625532003 248742808033612932938298005)
  ·
    refine ⟨11659819126575606231482719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248742808033612932938298005 11659819126575606231482719)
    ·
      refine ⟨17489728689863409347224079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11659819126575606231482719 17489728689863409347224079)
      ·
        refine ⟨26234593034795114020836119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17489728689863409347224079 26234593034795114020836119)
        ·
          refine ⟨39351889552192671031254179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26234593034795114020836119 39351889552192671031254179)
          ·
            refine ⟨59027834328289006546881269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39351889552192671031254179 59027834328289006546881269)
            ·
              refine ⟨5533859468277094363770119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59027834328289006546881269 5533859468277094363770119)
              ·
                refine ⟨8300789202415641545655179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533859468277094363770119 8300789202415641545655179)
                ·
                  refine ⟨12451183803623462318482769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8300789202415641545655179 12451183803623462318482769)
                  ·
                    refine ⟨9338387852717596738862077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12451183803623462318482769 9338387852717596738862077)
                    ·
                      refine ⟨3501895444769098777073279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9338387852717596738862077 3501895444769098777073279)
                      ·
                        rfl

theorem cell23_6819917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_6819917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819917 prefixEnd_6819917 := by exact prefixLift 6819917
  have htrace : WordTrace (prefixWord ++ tailWord_6819917) baseStart_6819917 baseEnd_6819917 := by
    simpa [prefixWord, tailWord_6819917, baseEnd_6819917] using wordTrace_append hprefix tailTrace_6819917
  have hstable : (prefixWord ++ tailWord_6819917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819917).length < 2 ^ (prefixWord ++ tailWord_6819917).sum := by decide
  have hdescent : baseEnd_6819917 < baseStart_6819917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819919 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_6819919 : Nat := 118140960795 + 6819919 * 2 ^ 59
def prefixEnd_6819919 : Nat := 4983230072969 + 3 ^ 40 * 6819919 * 2
def baseEnd_6819919 : Nat := 3501896471730407769248269

theorem tailTrace_6819919 : CollatzResearch.WordTrace tailWord_6819919 prefixEnd_6819919 3501896471730407769248269 := by
  unfold tailWord_6819919
  simp only [CollatzResearch.WordTrace]
  refine ⟨248742880979605687279870811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165828587319737124853247207 248742880979605687279870811)
  ·
    refine ⟨373114321469408530919806217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248742880979605687279870811 373114321469408530919806217)
    ·
      refine ⟨279835741102056398189854663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373114321469408530919806217 279835741102056398189854663)
      ·
        refine ⟨419753611653084597284781995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279835741102056398189854663 419753611653084597284781995)
        ·
          refine ⟨629630417479626895927172993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419753611653084597284781995 629630417479626895927172993)
          ·
            refine ⟨472222813109720171945379745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629630417479626895927172993 472222813109720171945379745)
            ·
              refine ⟨354167109832290128959034809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472222813109720171945379745 354167109832290128959034809)
              ·
                refine ⟨265625332374217596719276107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354167109832290128959034809 265625332374217596719276107)
                ·
                  refine ⟨398437998561326395078914161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265625332374217596719276107 398437998561326395078914161)
                  ·
                    refine ⟨298828498920994796309185621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 398437998561326395078914161 298828498920994796309185621)
                    ·
                      refine ⟨3501896471730407769248269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 298828498920994796309185621 3501896471730407769248269)
                      ·
                        rfl

theorem cell23_6819919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_6819919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819919 prefixEnd_6819919 := by exact prefixLift 6819919
  have htrace : WordTrace (prefixWord ++ tailWord_6819919) baseStart_6819919 baseEnd_6819919 := by
    simpa [prefixWord, tailWord_6819919, baseEnd_6819919] using wordTrace_append hprefix tailTrace_6819919
  have hstable : (prefixWord ++ tailWord_6819919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819919).length < 2 ^ (prefixWord ++ tailWord_6819919).sum := by decide
  have hdescent : baseEnd_6819919 < baseStart_6819919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819930 : List Nat := [3, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3]
def baseStart_6819930 : Nat := 118140960795 + 6819930 * 2 ^ 59
def prefixEnd_6819930 : Nat := 4983230072969 + 3 ^ 40 * 6819930 * 2
def baseEnd_6819930 : Nat := 3501902120017607226210719

theorem tailTrace_6819930 : CollatzResearch.WordTrace tailWord_6819930 prefixEnd_6819930 3501902120017607226210719 := by
  unfold tailWord_6819930
  simp only [CollatzResearch.WordTrace]
  refine ⟨62185820545641459039630311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165828854788377224105680829 62185820545641459039630311)
  ·
    refine ⟨93278730818462188559445467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62185820545641459039630311 93278730818462188559445467)
    ·
      refine ⟨139918096227693282839168201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93278730818462188559445467 139918096227693282839168201)
      ·
        refine ⟨104938572170769962129376151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139918096227693282839168201 104938572170769962129376151)
        ·
          refine ⟨157407858256154943194064227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104938572170769962129376151 157407858256154943194064227)
          ·
            refine ⟨236111787384232414791096341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157407858256154943194064227 236111787384232414791096341)
            ·
              refine ⟨11067740033635894443332641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 236111787384232414791096341 11067740033635894443332641)
              ·
                refine ⟨8300805025226920832499481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11067740033635894443332641 8300805025226920832499481)
                ·
                  refine ⟨6225603768920190624374611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8300805025226920832499481 6225603768920190624374611)
                  ·
                    refine ⟨9338405653380285936561917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6225603768920190624374611 9338405653380285936561917)
                    ·
                      refine ⟨3501902120017607226210719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9338405653380285936561917 3501902120017607226210719)
                      ·
                        rfl

theorem cell23_6819930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_6819930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819930 prefixEnd_6819930 := by exact prefixLift 6819930
  have htrace : WordTrace (prefixWord ++ tailWord_6819930) baseStart_6819930 baseEnd_6819930 := by
    simpa [prefixWord, tailWord_6819930, baseEnd_6819930] using wordTrace_append hprefix tailTrace_6819930
  have hstable : (prefixWord ++ tailWord_6819930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819930).length < 2 ^ (prefixWord ++ tailWord_6819930).sum := by decide
  have hdescent : baseEnd_6819930 < baseStart_6819930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819933 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6819933 : Nat := 118140960795 + 6819933 * 2 ^ 59
def prefixEnd_6819933 : Nat := 4983230072969 + 3 ^ 40 * 6819933 * 2
def baseEnd_6819933 : Nat := 1167301220153190238157735

theorem tailTrace_6819933 : CollatzResearch.WordTrace tailWord_6819933 prefixEnd_6819933 1167301220153190238157735 := by
  unfold tailWord_6819933
  simp only [CollatzResearch.WordTrace]
  refine ⟨248743391601554967670880453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165828927734369978447253635 248743391601554967670880453)
  ·
    refine ⟨46639385925291556438290085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248743391601554967670880453 46639385925291556438290085)
    ·
      refine ⟨8744884860992166832179391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46639385925291556438290085 8744884860992166832179391)
      ·
        refine ⟨13117327291488250248269087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8744884860992166832179391 13117327291488250248269087)
        ·
          refine ⟨19675990937232375372403631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13117327291488250248269087 19675990937232375372403631)
          ·
            refine ⟨29513986405848563058605447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19675990937232375372403631 29513986405848563058605447)
            ·
              refine ⟨44270979608772844587908171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29513986405848563058605447 44270979608772844587908171)
              ·
                refine ⟨66406469413159266881862257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44270979608772844587908171 66406469413159266881862257)
                ·
                  refine ⟨49804852059869450161396693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66406469413159266881862257 49804852059869450161396693)
                  ·
                    refine ⟨1167301220153190238157735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49804852059869450161396693 1167301220153190238157735)
                    ·
                      rfl

theorem cell23_6819933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6819933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819933 prefixEnd_6819933 := by exact prefixLift 6819933
  have htrace : WordTrace (prefixWord ++ tailWord_6819933) baseStart_6819933 baseEnd_6819933 := by
    simpa [prefixWord, tailWord_6819933, baseEnd_6819933] using wordTrace_append hprefix tailTrace_6819933
  have hstable : (prefixWord ++ tailWord_6819933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819933).length < 2 ^ (prefixWord ++ tailWord_6819933).sum := by decide
  have hdescent : baseEnd_6819933 < baseStart_6819933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6819936 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 4]
def baseStart_6819936 : Nat := 118140960795 + 6819936 * 2 ^ 59
def prefixEnd_6819936 : Nat := 4983230072969 + 3 ^ 40 * 6819936 * 2
def baseEnd_6819936 : Nat := 3501905200901534202735691

theorem tailTrace_6819936 : CollatzResearch.WordTrace tailWord_6819936 prefixEnd_6819936 3501905200901534202735691 := by
  unfold tailWord_6819936
  simp only [CollatzResearch.WordTrace]
  refine ⟨124371750510272049591619831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165829000680362732788826441 124371750510272049591619831)
  ·
    refine ⟨186557625765408074387429747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124371750510272049591619831 186557625765408074387429747)
    ·
      refine ⟨279836438648112111581144621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186557625765408074387429747 279836438648112111581144621)
      ·
        refine ⟨104938664493042041842929233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279836438648112111581144621 104938664493042041842929233)
        ·
          refine ⟨78703998369781531382196925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104938664493042041842929233 78703998369781531382196925)
          ·
            refine ⟨29513999388668074268323847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78703998369781531382196925 29513999388668074268323847)
            ·
              refine ⟨44270999083002111402485771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29513999388668074268323847 44270999083002111402485771)
              ·
                refine ⟨66406498624503167103728657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44270999083002111402485771 66406498624503167103728657)
                ·
                  refine ⟨49804873968377375327796493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66406498624503167103728657 49804873968377375327796493)
                  ·
                    refine ⟨18676827738141515747923685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49804873968377375327796493 18676827738141515747923685)
                    ·
                      refine ⟨3501905200901534202735691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18676827738141515747923685 3501905200901534202735691)
                      ·
                        rfl

theorem cell23_6819936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_6819936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6819936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6819936 prefixEnd_6819936 := by exact prefixLift 6819936
  have htrace : WordTrace (prefixWord ++ tailWord_6819936) baseStart_6819936 baseEnd_6819936 := by
    simpa [prefixWord, tailWord_6819936, baseEnd_6819936] using wordTrace_append hprefix tailTrace_6819936
  have hstable : (prefixWord ++ tailWord_6819936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6819936).length < 2 ^ (prefixWord ++ tailWord_6819936).sum := by decide
  have hdescent : baseEnd_6819936 < baseStart_6819936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6819936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820004 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 1, 4, 2]
def baseStart_6820004 : Nat := 118140960795 + 6820004 * 2 ^ 59
def prefixEnd_6820004 : Nat := 4983230072969 + 3 ^ 40 * 6820004 * 2
def baseEnd_6820004 : Nat := 3501940117586039936685379

theorem tailTrace_6820004 : CollatzResearch.WordTrace tailWord_6820004 prefixEnd_6820004 3501940117586039936685379 := by
  unfold tailWord_6820004
  simp only [CollatzResearch.WordTrace]
  refine ⟨124372990592148873398357533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165830654122865164531143377 124372990592148873398357533)
  ·
    refine ⟨46639871472055827524384075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124372990592148873398357533 46639871472055827524384075)
    ·
      refine ⟨69959807208083741286576113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46639871472055827524384075 69959807208083741286576113)
      ·
        refine ⟨52469855406062805964932085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69959807208083741286576113 52469855406062805964932085)
        ·
          refine ⟨4919048944318388059212383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52469855406062805964932085 4919048944318388059212383)
          ·
            refine ⟨7378573416477582088818575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919048944318388059212383 7378573416477582088818575)
            ·
              refine ⟨11067860124716373133227863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378573416477582088818575 11067860124716373133227863)
              ·
                refine ⟨16601790187074559699841795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11067860124716373133227863 16601790187074559699841795)
                ·
                  refine ⟨24902685280611839549762693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16601790187074559699841795 24902685280611839549762693)
                  ·
                    refine ⟨4669253490114719915580505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24902685280611839549762693 4669253490114719915580505)
                    ·
                      refine ⟨3501940117586039936685379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669253490114719915580505 3501940117586039936685379)
                      ·
                        rfl

theorem cell23_6820004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_6820004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820004 prefixEnd_6820004 := by exact prefixLift 6820004
  have htrace : WordTrace (prefixWord ++ tailWord_6820004) baseStart_6820004 baseEnd_6820004 := by
    simpa [prefixWord, tailWord_6820004, baseEnd_6820004] using wordTrace_append hprefix tailTrace_6820004
  have hstable : (prefixWord ++ tailWord_6820004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820004).length < 2 ^ (prefixWord ++ tailWord_6820004).sum := by decide
  have hdescent : baseEnd_6820004 < baseStart_6820004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820043 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 4]
def baseStart_6820043 : Nat := 118140960795 + 6820043 * 2 ^ 59
def prefixEnd_6820043 : Nat := 4983230072969 + 3 ^ 40 * 6820043 * 2
def baseEnd_6820043 : Nat := 3501960143331565284097699

theorem tailTrace_6820043 : CollatzResearch.WordTrace tailWord_6820043 prefixEnd_6820043 3501960143331565284097699 := by
  unfold tailWord_6820043
  simp only [CollatzResearch.WordTrace]
  refine ⟨248747403631156456457384783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165831602420770970971589855 248747403631156456457384783)
  ·
    refine ⟨373121105446734684686077175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248747403631156456457384783 373121105446734684686077175)
    ·
      refine ⟨559681658170102027029115763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373121105446734684686077175 559681658170102027029115763)
      ·
        refine ⟨839522487255153040543673645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559681658170102027029115763 839522487255153040543673645)
        ·
          refine ⟨314820932720682390203877617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 839522487255153040543673645 314820932720682390203877617)
          ·
            refine ⟨236115699540511792652908213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314820932720682390203877617 236115699540511792652908213)
            ·
              refine ⟨22135846831922980561210145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236115699540511792652908213 22135846831922980561210145)
              ·
                refine ⟨16601885123942235420907609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22135846831922980561210145 16601885123942235420907609)
                ·
                  refine ⟨12451413842956676565680707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16601885123942235420907609 12451413842956676565680707)
                  ·
                    refine ⟨18677120764435014848521061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12451413842956676565680707 18677120764435014848521061)
                    ·
                      refine ⟨3501960143331565284097699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18677120764435014848521061 3501960143331565284097699)
                      ·
                        rfl

theorem cell23_6820043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 4].length) (baseStart_6820043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820043 prefixEnd_6820043 := by exact prefixLift 6820043
  have htrace : WordTrace (prefixWord ++ tailWord_6820043) baseStart_6820043 baseEnd_6820043 := by
    simpa [prefixWord, tailWord_6820043, baseEnd_6820043] using wordTrace_append hprefix tailTrace_6820043
  have hstable : (prefixWord ++ tailWord_6820043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820043).length < 2 ^ (prefixWord ++ tailWord_6820043).sum := by decide
  have hdescent : baseEnd_6820043 < baseStart_6820043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820044 : List Nat := [2, 2, 1, 6, 1, 1, 3, 2, 5]
def baseStart_6820044 : Nat := 118140960795 + 6820044 * 2 ^ 59
def prefixEnd_6820044 : Nat := 4983230072969 + 3 ^ 40 * 6820044 * 2
def baseEnd_6820044 : Nat := 389106739645802197798355

theorem tailTrace_6820044 : CollatzResearch.WordTrace tailWord_6820044 prefixEnd_6820044 389106739645802197798355 := by
  unfold tailWord_6820044
  simp only [CollatzResearch.WordTrace]
  refine ⟨124373720052076416814085593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165831626736101889085447457 124373720052076416814085593)
  ·
    refine ⟨93280290039057312610564195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124373720052076416814085593 93280290039057312610564195)
    ·
      refine ⟨139920435058585968915846293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93280290039057312610564195 139920435058585968915846293)
      ·
        refine ⟨6558770393371217292930295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139920435058585968915846293 6558770393371217292930295)
        ·
          refine ⟨9838155590056825939395443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6558770393371217292930295 9838155590056825939395443)
          ·
            refine ⟨14757233385085238909093165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9838155590056825939395443 14757233385085238909093165)
            ·
              refine ⟨5533962519406964590909937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14757233385085238909093165 5533962519406964590909937)
              ·
                refine ⟨4150471889555223443182453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5533962519406964590909937 4150471889555223443182453)
                ·
                  refine ⟨389106739645802197798355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4150471889555223443182453 389106739645802197798355)
                  ·
                    rfl

theorem cell23_6820044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_6820044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820044 prefixEnd_6820044 := by exact prefixLift 6820044
  have htrace : WordTrace (prefixWord ++ tailWord_6820044) baseStart_6820044 baseEnd_6820044 := by
    simpa [prefixWord, tailWord_6820044, baseEnd_6820044] using wordTrace_append hprefix tailTrace_6820044
  have hstable : (prefixWord ++ tailWord_6820044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820044).length < 2 ^ (prefixWord ++ tailWord_6820044).sum := by decide
  have hdescent : baseEnd_6820044 < baseStart_6820044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820063 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 3]
def baseStart_6820063 : Nat := 118140960795 + 6820063 * 2 ^ 59
def prefixEnd_6820063 : Nat := 4983230072969 + 3 ^ 40 * 6820063 * 2
def baseEnd_6820063 : Nat := 3501970412944655205847607

theorem tailTrace_6820063 : CollatzResearch.WordTrace tailWord_6820063 prefixEnd_6820063 3501970412944655205847607 := by
  unfold tailWord_6820063
  simp only [CollatzResearch.WordTrace]
  refine ⟨248748133091083999873112843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165832088727389333248741895 248748133091083999873112843)
  ·
    refine ⟨373122199636625999809669265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248748133091083999873112843 373122199636625999809669265)
    ·
      refine ⟨279841649727469499857251949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373122199636625999809669265 279841649727469499857251949)
      ·
        refine ⟨104940618647801062446469481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279841649727469499857251949 104940618647801062446469481)
        ·
          refine ⟨78705463985850796834852111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104940618647801062446469481 78705463985850796834852111)
          ·
            refine ⟨118058195978776195252278167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78705463985850796834852111 118058195978776195252278167)
            ·
              refine ⟨177087293968164292878417251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118058195978776195252278167 177087293968164292878417251)
              ·
                refine ⟨265630940952246439317625877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177087293968164292878417251 265630940952246439317625877)
                ·
                  refine ⟨12451450357136551843013713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 265630940952246439317625877 12451450357136551843013713)
                  ·
                    refine ⟨9338587767852413882260285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12451450357136551843013713 9338587767852413882260285)
                    ·
                      refine ⟨3501970412944655205847607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9338587767852413882260285 3501970412944655205847607)
                      ·
                        rfl

theorem cell23_6820063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_6820063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820063 prefixEnd_6820063 := by exact prefixLift 6820063
  have htrace : WordTrace (prefixWord ++ tailWord_6820063) baseStart_6820063 baseEnd_6820063 := by
    simpa [prefixWord, tailWord_6820063, baseEnd_6820063] using wordTrace_append hprefix tailTrace_6820063
  have hstable : (prefixWord ++ tailWord_6820063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820063).length < 2 ^ (prefixWord ++ tailWord_6820063).sum := by decide
  have hdescent : baseEnd_6820063 < baseStart_6820063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820077 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_6820077 : Nat := 118140960795 + 6820077 * 2 ^ 59
def prefixEnd_6820077 : Nat := 4983230072969 + 3 ^ 40 * 6820077 * 2
def baseEnd_6820077 : Nat := 3501977601673818151072543

theorem tailTrace_6820077 : CollatzResearch.WordTrace tailWord_6820077 prefixEnd_6820077 3501977601673818151072543 := by
  unfold tailWord_6820077
  simp only [CollatzResearch.WordTrace]
  refine ⟨248748643713033280264122485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165832429142022186842748323 248748643713033280264122485)
  ·
    refine ⟨23320185348096870024761483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248748643713033280264122485 23320185348096870024761483)
    ·
      refine ⟨34980278022145305037142225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23320185348096870024761483 34980278022145305037142225)
      ·
        refine ⟨26235208516608978777856669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34980278022145305037142225 26235208516608978777856669)
        ·
          refine ⟨9838203193728367041696251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26235208516608978777856669 9838203193728367041696251)
          ·
            refine ⟨14757304790592550562544377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9838203193728367041696251 14757304790592550562544377)
            ·
              refine ⟨11067978592944412921908283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14757304790592550562544377 11067978592944412921908283)
              ·
                refine ⟨16601967889416619382862425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11067978592944412921908283 16601967889416619382862425)
                ·
                  refine ⟨12451475917062464537146819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16601967889416619382862425 12451475917062464537146819)
                  ·
                    refine ⟨18677213875593696805720229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12451475917062464537146819 18677213875593696805720229)
                    ·
                      refine ⟨3501977601673818151072543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18677213875593696805720229 3501977601673818151072543)
                      ·
                        rfl

theorem cell23_6820077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_6820077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820077 prefixEnd_6820077 := by exact prefixLift 6820077
  have htrace : WordTrace (prefixWord ++ tailWord_6820077) baseStart_6820077 baseEnd_6820077 := by
    simpa [prefixWord, tailWord_6820077, baseEnd_6820077] using wordTrace_append hprefix tailTrace_6820077
  have hstable : (prefixWord ++ tailWord_6820077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820077).length < 2 ^ (prefixWord ++ tailWord_6820077).sum := by decide
  have hdescent : baseEnd_6820077 < baseStart_6820077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820104 : List Nat := [2, 1, 3, 2, 3, 1, 4, 2, 1, 4]
def baseStart_6820104 : Nat := 118140960795 + 6820104 * 2 ^ 59
def prefixEnd_6820104 : Nat := 4983230072969 + 3 ^ 40 * 6820104 * 2
def baseEnd_6820104 : Nat := 1167330488550496515144973

theorem tailTrace_6820104 : CollatzResearch.WordTrace tailWord_6820104 prefixEnd_6820104 1167330488550496515144973 := by
  unfold tailWord_6820104
  simp only [CollatzResearch.WordTrace]
  refine ⟨124374814241967731937677683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165833085655956975916903577 124374814241967731937677683)
  ·
    refine ⟨186562221362951597906516525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124374814241967731937677683 186562221362951597906516525)
    ·
      refine ⟨69960833011106849214943697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186562221362951597906516525 69960833011106849214943697)
      ·
        refine ⟨52470624758330136911207773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69960833011106849214943697 52470624758330136911207773)
        ·
          refine ⟨19676484284373801341702915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52470624758330136911207773 19676484284373801341702915)
          ·
            refine ⟨29514726426560702012554373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19676484284373801341702915 29514726426560702012554373)
            ·
              refine ⟨5534011204980131627353945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29514726426560702012554373 5534011204980131627353945)
              ·
                refine ⟨4150508403735098720515459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5534011204980131627353945 4150508403735098720515459)
                ·
                  refine ⟨6225762605602648080773189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150508403735098720515459 6225762605602648080773189)
                  ·
                    refine ⟨1167330488550496515144973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6225762605602648080773189 1167330488550496515144973)
                    ·
                      rfl

theorem cell23_6820104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_6820104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820104 prefixEnd_6820104 := by exact prefixLift 6820104
  have htrace : WordTrace (prefixWord ++ tailWord_6820104) baseStart_6820104 baseEnd_6820104 := by
    simpa [prefixWord, tailWord_6820104, baseEnd_6820104] using wordTrace_append hprefix tailTrace_6820104
  have hstable : (prefixWord ++ tailWord_6820104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820104).length < 2 ^ (prefixWord ++ tailWord_6820104).sum := by decide
  have hdescent : baseEnd_6820104 < baseStart_6820104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820113 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 3, 5]
def baseStart_6820113 : Nat := 118140960795 + 6820113 * 2 ^ 59
def prefixEnd_6820113 : Nat := 4983230072969 + 3 ^ 40 * 6820113 * 2
def baseEnd_6820113 : Nat := 1167332028992460003407459

theorem tailTrace_6820113 : CollatzResearch.WordTrace tailWord_6820113 prefixEnd_6820113 1167332028992460003407459 := by
  unfold tailWord_6820113
  simp only [CollatzResearch.WordTrace]
  refine ⟨248749956740902858412432993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165833304493935238941621995 248749956740902858412432993)
  ·
    refine ⟨186562467555677143809324745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248749956740902858412432993 186562467555677143809324745)
    ·
      refine ⟨139921850666757857856993559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186562467555677143809324745 139921850666757857856993559)
      ·
        refine ⟨209882776000136786785490339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139921850666757857856993559 209882776000136786785490339)
        ·
          refine ⟨314824164000205180178235509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209882776000136786785490339 314824164000205180178235509)
          ·
            refine ⟨29514765375019235641709579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 314824164000205180178235509 29514765375019235641709579)
            ·
              refine ⟨44272148062528853462564369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29514765375019235641709579 44272148062528853462564369)
              ·
                refine ⟨33204111046896640096923277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44272148062528853462564369 33204111046896640096923277)
                ·
                  refine ⟨12451541642586240036346229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33204111046896640096923277 12451541642586240036346229)
                  ·
                    refine ⟨1167332028992460003407459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12451541642586240036346229 1167332028992460003407459)
                    ·
                      rfl

theorem cell23_6820113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_6820113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820113 prefixEnd_6820113 := by exact prefixLift 6820113
  have htrace : WordTrace (prefixWord ++ tailWord_6820113) baseStart_6820113 baseEnd_6820113 := by
    simpa [prefixWord, tailWord_6820113, baseEnd_6820113] using wordTrace_append hprefix tailTrace_6820113
  have hstable : (prefixWord ++ tailWord_6820113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820113).length < 2 ^ (prefixWord ++ tailWord_6820113).sum := by decide
  have hdescent : baseEnd_6820113 < baseStart_6820113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820120 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 1, 5, 2]
def baseStart_6820120 : Nat := 118140960795 + 6820120 * 2 ^ 59
def prefixEnd_6820120 : Nat := 4983230072969 + 3 ^ 40 * 6820120 * 2
def baseEnd_6820120 : Nat := 3501999681341961482834845

theorem tailTrace_6820120 : CollatzResearch.WordTrace tailWord_6820120 prefixEnd_6820120 3501999681341961482834845 := by
  unfold tailWord_6820120
  simp only [CollatzResearch.WordTrace]
  refine ⟨124375106025938749303968907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165833474701251665738625209 124375106025938749303968907)
  ·
    refine ⟨186562659038908123955953361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124375106025938749303968907 186562659038908123955953361)
    ·
      refine ⟨139921994279181092966965021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186562659038908123955953361 139921994279181092966965021)
      ·
        refine ⟨52470747854692909862611883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139921994279181092966965021 52470747854692909862611883)
        ·
          refine ⟨78706121782039364793917825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52470747854692909862611883 78706121782039364793917825)
          ·
            refine ⟨59029591336529523595438369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78706121782039364793917825 59029591336529523595438369)
            ·
              refine ⟨44272193502397142696578777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59029591336529523595438369 44272193502397142696578777)
              ·
                refine ⟨33204145126797857022434083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44272193502397142696578777 33204145126797857022434083)
                ·
                  refine ⟨49806217690196785533651125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33204145126797857022434083 49806217690196785533651125)
                  ·
                    refine ⟨4669332908455948643779793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49806217690196785533651125 4669332908455948643779793)
                    ·
                      refine ⟨3501999681341961482834845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669332908455948643779793 3501999681341961482834845)
                      ·
                        rfl

theorem cell23_6820120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_6820120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820120 prefixEnd_6820120 := by exact prefixLift 6820120
  have htrace : WordTrace (prefixWord ++ tailWord_6820120) baseStart_6820120 baseEnd_6820120 := by
    simpa [prefixWord, tailWord_6820120, baseEnd_6820120] using wordTrace_append hprefix tailTrace_6820120
  have hstable : (prefixWord ++ tailWord_6820120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820120).length < 2 ^ (prefixWord ++ tailWord_6820120).sum := by decide
  have hdescent : baseEnd_6820120 < baseStart_6820120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820127 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 3, 1, 3]
def baseStart_6820127 : Nat := 118140960795 + 6820127 * 2 ^ 59
def prefixEnd_6820127 : Nat := 4983230072969 + 3 ^ 40 * 6820127 * 2
def baseEnd_6820127 : Nat := 3502003275706542955447313

theorem tailTrace_6820127 : CollatzResearch.WordTrace tailWord_6820127 prefixEnd_6820127 3502003275706542955447313 := by
  unfold tailWord_6820127
  simp only [CollatzResearch.WordTrace]
  refine ⟨248750467362852138803442635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165833644908568092535628423 248750467362852138803442635)
  ·
    refine ⟨373125701044278208205163953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248750467362852138803442635 373125701044278208205163953)
    ·
      refine ⟨279844275783208656153872965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373125701044278208205163953 279844275783208656153872965)
      ·
        refine ⟨52470801709351623028851181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279844275783208656153872965 52470801709351623028851181)
        ·
          refine ⟨19676550641006858635819193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52470801709351623028851181 19676550641006858635819193)
          ·
            refine ⟨14757412980755143976864395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19676550641006858635819193 14757412980755143976864395)
            ·
              refine ⟨22136119471132715965296593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14757412980755143976864395 22136119471132715965296593)
              ·
                refine ⟨16602089603349536973972445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22136119471132715965296593 16602089603349536973972445)
                ·
                  refine ⟨6225783601256076365239667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16602089603349536973972445 6225783601256076365239667)
                  ·
                    refine ⟨9338675401884114547859501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6225783601256076365239667 9338675401884114547859501)
                    ·
                      refine ⟨3502003275706542955447313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9338675401884114547859501 3502003275706542955447313)
                      ·
                        rfl

theorem cell23_6820127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_6820127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820127 prefixEnd_6820127 := by exact prefixLift 6820127
  have htrace : WordTrace (prefixWord ++ tailWord_6820127) baseStart_6820127 baseEnd_6820127 := by
    simpa [prefixWord, tailWord_6820127, baseEnd_6820127] using wordTrace_append hprefix tailTrace_6820127
  have hstable : (prefixWord ++ tailWord_6820127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820127).length < 2 ^ (prefixWord ++ tailWord_6820127).sum := by decide
  have hdescent : baseEnd_6820127 < baseStart_6820127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820130 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_6820130 : Nat := 118140960795 + 6820130 * 2 ^ 59
def prefixEnd_6820130 : Nat := 4983230072969 + 3 ^ 40 * 6820130 * 2
def baseEnd_6820130 : Nat := 1167334938716168814569933

theorem tailTrace_6820130 : CollatzResearch.WordTrace tailWord_6820130 prefixEnd_6820130 1167334938716168814569933 := by
  unfold tailWord_6820130
  simp only [CollatzResearch.WordTrace]
  refine ⟨62187644195460317578950461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165833717854560846877201229 62187644195460317578950461)
  ·
    refine ⟨23320366573297619092106423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62187644195460317578950461 23320366573297619092106423)
    ·
      refine ⟨34980549859946428638159635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23320366573297619092106423 34980549859946428638159635)
      ·
        refine ⟨52470824789919642957239453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34980549859946428638159635 52470824789919642957239453)
        ·
          refine ⟨19676559296219866108964795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52470824789919642957239453 19676559296219866108964795)
          ·
            refine ⟨29514838944329799163447193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19676559296219866108964795 29514838944329799163447193)
            ·
              refine ⟨22136129208247349372585395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29514838944329799163447193 22136129208247349372585395)
              ·
                refine ⟨33204193812371024058878093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22136129208247349372585395 33204193812371024058878093)
                ·
                  refine ⟨12451572679639134022079285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33204193812371024058878093 12451572679639134022079285)
                  ·
                    refine ⟨1167334938716168814569933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12451572679639134022079285 1167334938716168814569933)
                    ·
                      rfl

theorem cell23_6820130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_6820130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820130 prefixEnd_6820130 := by exact prefixLift 6820130
  have htrace : WordTrace (prefixWord ++ tailWord_6820130) baseStart_6820130 baseEnd_6820130 := by
    simpa [prefixWord, tailWord_6820130, baseEnd_6820130] using wordTrace_append hprefix tailTrace_6820130
  have hstable : (prefixWord ++ tailWord_6820130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820130).length < 2 ^ (prefixWord ++ tailWord_6820130).sum := by decide
  have hdescent : baseEnd_6820130 < baseStart_6820130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820143 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 1, 6]
def baseStart_6820143 : Nat := 118140960795 + 6820143 * 2 ^ 59
def prefixEnd_6820143 : Nat := 4983230072969 + 3 ^ 40 * 6820143 * 2
def baseEnd_6820143 : Nat := 1167337163799004964282413

theorem tailTrace_6820143 : CollatzResearch.WordTrace tailWord_6820143 prefixEnd_6820143 1167337163799004964282413 := by
  unfold tailWord_6820143
  simp only [CollatzResearch.WordTrace]
  refine ⟨248751050930794173536025083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165834033953862782357350055 248751050930794173536025083)
  ·
    refine ⟨373126576396191260304037625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248751050930794173536025083 373126576396191260304037625)
    ·
      refine ⟨279844932297143445228028219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373126576396191260304037625 279844932297143445228028219)
      ·
        refine ⟨419767398445715167842042329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279844932297143445228028219 419767398445715167842042329)
        ·
          refine ⟨314825548834286375881531747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419767398445715167842042329 314825548834286375881531747)
          ·
            refine ⟨472238323251429563822297621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314825548834286375881531747 472238323251429563822297621)
            ·
              refine ⟨22136171402410760804170201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 472238323251429563822297621 22136171402410760804170201)
              ·
                refine ⟨16602128551808070603127651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22136171402410760804170201 16602128551808070603127651)
                ·
                  refine ⟨24903192827712105904691477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16602128551808070603127651 24903192827712105904691477)
                  ·
                    refine ⟨1167337163799004964282413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24903192827712105904691477 1167337163799004964282413)
                    ·
                      rfl

theorem cell23_6820143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_6820143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820143 prefixEnd_6820143 := by exact prefixLift 6820143
  have htrace : WordTrace (prefixWord ++ tailWord_6820143) baseStart_6820143 baseEnd_6820143 := by
    simpa [prefixWord, tailWord_6820143, baseEnd_6820143] using wordTrace_append hprefix tailTrace_6820143
  have hstable : (prefixWord ++ tailWord_6820143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820143).length < 2 ^ (prefixWord ++ tailWord_6820143).sum := by decide
  have hdescent : baseEnd_6820143 < baseStart_6820143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820160 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 2, 4]
def baseStart_6820160 : Nat := 118140960795 + 6820160 * 2 ^ 59
def prefixEnd_6820160 : Nat := 4983230072969 + 3 ^ 40 * 6820160 * 2
def baseEnd_6820160 : Nat := 1167340073522713775444887

theorem tailTrace_6820160 : CollatzResearch.WordTrace tailWord_6820160 prefixEnd_6820160 1167340073522713775444887 := by
  unfold tailWord_6820160
  simp only [CollatzResearch.WordTrace]
  refine ⟨124375835485866292719696967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165834447314488390292929289 124375835485866292719696967)
  ·
    refine ⟨186563753228799439079545451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124375835485866292719696967 186563753228799439079545451)
    ·
      refine ⟨279845629843199158619318177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186563753228799439079545451 279845629843199158619318177)
      ·
        refine ⟨209884222382399368964488633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279845629843199158619318177 209884222382399368964488633)
        ·
          refine ⟨157413166786799526723366475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209884222382399368964488633 157413166786799526723366475)
          ·
            refine ⟨236119750180199290085049713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157413166786799526723366475 236119750180199290085049713)
            ·
              refine ⟨177089812635149467563787285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236119750180199290085049713 177089812635149467563787285)
              ·
                refine ⟨8301084967272631292052529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177089812635149467563787285 8301084967272631292052529)
                ·
                  refine ⟨6225813725454473469039397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8301084967272631292052529 6225813725454473469039397)
                  ·
                    refine ⟨1167340073522713775444887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6225813725454473469039397 1167340073522713775444887)
                    ·
                      rfl

theorem cell23_6820160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2, 4].length) (baseStart_6820160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820160 prefixEnd_6820160 := by exact prefixLift 6820160
  have htrace : WordTrace (prefixWord ++ tailWord_6820160) baseStart_6820160 baseEnd_6820160 := by
    simpa [prefixWord, tailWord_6820160, baseEnd_6820160] using wordTrace_append hprefix tailTrace_6820160
  have hstable : (prefixWord ++ tailWord_6820160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820160).length < 2 ^ (prefixWord ++ tailWord_6820160).sum := by decide
  have hdescent : baseEnd_6820160 < baseStart_6820160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820163 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 4]
def baseStart_6820163 : Nat := 118140960795 + 6820163 * 2 ^ 59
def prefixEnd_6820163 : Nat := 4983230072969 + 3 ^ 40 * 6820163 * 2
def baseEnd_6820163 : Nat := 3502021761010104814597147

theorem tailTrace_6820163 : CollatzResearch.WordTrace tailWord_6820163 prefixEnd_6820163 3502021761010104814597147 := by
  unfold tailWord_6820163
  simp only [CollatzResearch.WordTrace]
  refine ⟨248751780390721716951753143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165834520260481144634502095 248751780390721716951753143)
  ·
    refine ⟨373127670586082575427629715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248751780390721716951753143 373127670586082575427629715)
    ·
      refine ⟨559691505879123863141444573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373127670586082575427629715 559691505879123863141444573)
      ·
        refine ⟨209884314704671448678041715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559691505879123863141444573 209884314704671448678041715)
        ·
          refine ⟨314826472057007173017062573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209884314704671448678041715 314826472057007173017062573)
          ·
            refine ⟨118059927021377689881398465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314826472057007173017062573 118059927021377689881398465)
            ·
              refine ⟨88544945266033267411048849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118059927021377689881398465 88544945266033267411048849)
              ·
                refine ⟨66408708949524950558286637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88544945266033267411048849 66408708949524950558286637)
                ·
                  refine ⟨24903265856071856459357489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66408708949524950558286637 24903265856071856459357489)
                  ·
                    refine ⟨18677449392053892344518117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24903265856071856459357489 18677449392053892344518117)
                    ·
                      refine ⟨3502021761010104814597147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18677449392053892344518117 3502021761010104814597147)
                      ·
                        rfl

theorem cell23_6820163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_6820163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820163 prefixEnd_6820163 := by exact prefixLift 6820163
  have htrace : WordTrace (prefixWord ++ tailWord_6820163) baseStart_6820163 baseEnd_6820163 := by
    simpa [prefixWord, tailWord_6820163, baseEnd_6820163] using wordTrace_append hprefix tailTrace_6820163
  have hstable : (prefixWord ++ tailWord_6820163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820163).length < 2 ^ (prefixWord ++ tailWord_6820163).sum := by decide
  have hdescent : baseEnd_6820163 < baseStart_6820163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820180 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_6820180 : Nat := 118140960795 + 6820180 * 2 ^ 59
def prefixEnd_6820180 : Nat := 4983230072969 + 3 ^ 40 * 6820180 * 2
def baseEnd_6820180 : Nat := 3502030490181231248084569

theorem tailTrace_6820180 : CollatzResearch.WordTrace tailWord_6820180 prefixEnd_6820180 3502030490181231248084569 := by
  unfold tailWord_6820180
  simp only [CollatzResearch.WordTrace]
  refine ⟨124376200215830064427560997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165834933621106752570081329 124376200215830064427560997)
  ·
    refine ⟨23320537540468137080167687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124376200215830064427560997 23320537540468137080167687)
    ·
      refine ⟨34980806310702205620251531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23320537540468137080167687 34980806310702205620251531)
      ·
        refine ⟨52471209466053308430377297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34980806310702205620251531 52471209466053308430377297)
        ·
          refine ⟨39353407099539981322782973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52471209466053308430377297 39353407099539981322782973)
          ·
            refine ⟨14757527662327492996043615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39353407099539981322782973 14757527662327492996043615)
            ·
              refine ⟨22136291493491239494065423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14757527662327492996043615 22136291493491239494065423)
              ·
                refine ⟨33204437240236859241098135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22136291493491239494065423 33204437240236859241098135)
                ·
                  refine ⟨49806655860355288861647203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33204437240236859241098135 49806655860355288861647203)
                  ·
                    refine ⟨74709983790532933292470805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49806655860355288861647203 74709983790532933292470805)
                    ·
                      refine ⟨3502030490181231248084569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74709983790532933292470805 3502030490181231248084569)
                      ·
                        rfl

theorem cell23_6820180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_6820180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820180 prefixEnd_6820180 := by exact prefixLift 6820180
  have htrace : WordTrace (prefixWord ++ tailWord_6820180) baseStart_6820180 baseEnd_6820180 := by
    simpa [prefixWord, tailWord_6820180, baseEnd_6820180] using wordTrace_append hprefix tailTrace_6820180
  have hstable : (prefixWord ++ tailWord_6820180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820180).length < 2 ^ (prefixWord ++ tailWord_6820180).sum := by decide
  have hdescent : baseEnd_6820180 < baseStart_6820180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820217 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 2, 1, 3]
def baseStart_6820217 : Nat := 118140960795 + 6820217 * 2 ^ 59
def prefixEnd_6820217 : Nat := 4983230072969 + 3 ^ 40 * 6820217 * 2
def baseEnd_6820217 : Nat := 3502049488965447603321899

theorem tailTrace_6820217 : CollatzResearch.WordTrace tailWord_6820217 prefixEnd_6820217 3502049488965447603321899 := by
  unfold tailWord_6820217
  simp only [CollatzResearch.WordTrace]
  refine ⟨248753749932526084174218905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165835833288350722782812603 248753749932526084174218905)
  ·
    refine ⟨186565312449394563130664179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248753749932526084174218905 186565312449394563130664179)
    ·
      refine ⟨279847968674091844695996269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186565312449394563130664179 279847968674091844695996269)
      ·
        refine ⟨104942988252784441760998601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279847968674091844695996269 104942988252784441760998601)
        ·
          refine ⟨78707241189588331320748951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104942988252784441760998601 78707241189588331320748951)
          ·
            refine ⟨118060861784382496981123427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78707241189588331320748951 118060861784382496981123427)
            ·
              refine ⟨177091292676573745471685141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118060861784382496981123427 177091292676573745471685141)
              ·
                refine ⟨8301154344214394318985241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177091292676573745471685141 8301154344214394318985241)
                ·
                  refine ⟨6225865758160795739238931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8301154344214394318985241 6225865758160795739238931)
                  ·
                    refine ⟨9338798637241193608858397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6225865758160795739238931 9338798637241193608858397)
                    ·
                      refine ⟨3502049488965447603321899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9338798637241193608858397 3502049488965447603321899)
                      ·
                        rfl

theorem cell23_6820217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_6820217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820217 prefixEnd_6820217 := by exact prefixLift 6820217
  have htrace : WordTrace (prefixWord ++ tailWord_6820217) baseStart_6820217 baseEnd_6820217 := by
    simpa [prefixWord, tailWord_6820217, baseEnd_6820217] using wordTrace_append hprefix tailTrace_6820217
  have hstable : (prefixWord ++ tailWord_6820217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820217).length < 2 ^ (prefixWord ++ tailWord_6820217).sum := by decide
  have hdescent : baseEnd_6820217 < baseStart_6820217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820223 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 4]
def baseStart_6820223 : Nat := 118140960795 + 6820223 * 2 ^ 59
def prefixEnd_6820223 : Nat := 4983230072969 + 3 ^ 40 * 6820223 * 2
def baseEnd_6820223 : Nat := 3502052569849374579846871

theorem tailTrace_6820223 : CollatzResearch.WordTrace tailWord_6820223 prefixEnd_6820223 3502052569849374579846871 := by
  unfold tailWord_6820223
  simp only [CollatzResearch.WordTrace]
  refine ⟨248753968770504347198937323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165835979180336231465958215 248753968770504347198937323)
  ·
    refine ⟨373130953155756520798405985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248753968770504347198937323 373130953155756520798405985)
    ·
      refine ⟨279848214866817390598804489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373130953155756520798405985 279848214866817390598804489)
      ·
        refine ⟨209886161150113042949103367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279848214866817390598804489 209886161150113042949103367)
        ·
          refine ⟨314829241725169564423655051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209886161150113042949103367 314829241725169564423655051)
          ·
            refine ⟨472243862587754346635482577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314829241725169564423655051 472243862587754346635482577)
            ·
              refine ⟨354182896940815759976611933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472243862587754346635482577 354182896940815759976611933)
              ·
                refine ⟨132818586352805909991229475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354182896940815759976611933 132818586352805909991229475)
                ·
                  refine ⟨199227879529208864986844213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132818586352805909991229475 199227879529208864986844213)
                  ·
                    refine ⟨18677613705863331092516645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 199227879529208864986844213 18677613705863331092516645)
                    ·
                      refine ⟨3502052569849374579846871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18677613705863331092516645 3502052569849374579846871)
                      ·
                        rfl

theorem cell23_6820223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_6820223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820223 prefixEnd_6820223 := by exact prefixLift 6820223
  have htrace : WordTrace (prefixWord ++ tailWord_6820223) baseStart_6820223 baseEnd_6820223 := by
    simpa [prefixWord, tailWord_6820223, baseEnd_6820223] using wordTrace_append hprefix tailTrace_6820223
  have hstable : (prefixWord ++ tailWord_6820223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820223).length < 2 ^ (prefixWord ++ tailWord_6820223).sum := by decide
  have hdescent : baseEnd_6820223 < baseStart_6820223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820260 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_6820260 : Nat := 118140960795 + 6820260 * 2 ^ 59
def prefixEnd_6820260 : Nat := 4983230072969 + 3 ^ 40 * 6820260 * 2
def baseEnd_6820260 : Nat := 3502071568633590935084201

theorem tailTrace_6820260 : CollatzResearch.WordTrace tailWord_6820260 prefixEnd_6820260 3502071568633590935084201 := by
  unfold tailWord_6820260
  simp only [CollatzResearch.WordTrace]
  refine ⟨124377659135685151259017117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165836878847580201678689489 124377659135685151259017117)
  ·
    refine ⟨46641622175881931722131419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124377659135685151259017117 46641622175881931722131419)
    ·
      refine ⟨69962433263822897583197129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46641622175881931722131419 69962433263822897583197129)
      ·
        refine ⟨52471824947867173187397847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69962433263822897583197129 52471824947867173187397847)
        ·
          refine ⟨78707737421800759781096771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52471824947867173187397847 78707737421800759781096771)
          ·
            refine ⟨118061606132701139671645157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78707737421800759781096771 118061606132701139671645157)
            ·
              refine ⟨22136551149881463688433467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118061606132701139671645157 22136551149881463688433467)
              ·
                refine ⟨33204826724822195532650201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22136551149881463688433467 33204826724822195532650201)
                ·
                  refine ⟨24903620043616646649487651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33204826724822195532650201 24903620043616646649487651)
                  ·
                    refine ⟨37355430065424969974231477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24903620043616646649487651 37355430065424969974231477)
                    ·
                      refine ⟨3502071568633590935084201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37355430065424969974231477 3502071568633590935084201)
                      ·
                        rfl

theorem cell23_6820260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_6820260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820260 prefixEnd_6820260 := by exact prefixLift 6820260
  have htrace : WordTrace (prefixWord ++ tailWord_6820260) baseStart_6820260 baseEnd_6820260 := by
    simpa [prefixWord, tailWord_6820260, baseEnd_6820260] using wordTrace_append hprefix tailTrace_6820260
  have hstable : (prefixWord ++ tailWord_6820260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820260).length < 2 ^ (prefixWord ++ tailWord_6820260).sum := by decide
  have hdescent : baseEnd_6820260 < baseStart_6820260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820325 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 2, 2, 2]
def baseStart_6820325 : Nat := 118140960795 + 6820325 * 2 ^ 59
def prefixEnd_6820325 : Nat := 4983230072969 + 3 ^ 40 * 6820325 * 2
def baseEnd_6820325 : Nat := 3502104944876133180771403

theorem tailTrace_6820325 : CollatzResearch.WordTrace tailWord_6820325 prefixEnd_6820325 3502104944876133180771403 := by
  unfold tailWord_6820325
  simp only [CollatzResearch.WordTrace]
  refine ⟨248757689016134818619150429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165838459344089879079433619 248757689016134818619150429)
  ·
    refine ⟨93284133381050556982181411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248757689016134818619150429 93284133381050556982181411)
    ·
      refine ⟨139926200071575835473272117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93284133381050556982181411 139926200071575835473272117)
      ·
        refine ⟨13118081256710234575619261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139926200071575835473272117 13118081256710234575619261)
        ·
          refine ⟨4919280471266337965857223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13118081256710234575619261 4919280471266337965857223)
          ·
            refine ⟨7378920706899506948785835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919280471266337965857223 7378920706899506948785835)
            ·
              refine ⟨11068381060349260423178753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378920706899506948785835 11068381060349260423178753)
              ·
                refine ⟨8301285795261945317384065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11068381060349260423178753 8301285795261945317384065)
                ·
                  refine ⟨6225964346446458988038049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8301285795261945317384065 6225964346446458988038049)
                  ·
                    refine ⟨4669473259834844241028537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6225964346446458988038049 4669473259834844241028537)
                    ·
                      refine ⟨3502104944876133180771403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669473259834844241028537 3502104944876133180771403)
                      ·
                        rfl

theorem cell23_6820325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_6820325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820325 prefixEnd_6820325 := by exact prefixLift 6820325
  have htrace : WordTrace (prefixWord ++ tailWord_6820325) baseStart_6820325 baseEnd_6820325 := by
    simpa [prefixWord, tailWord_6820325, baseEnd_6820325] using wordTrace_append hprefix tailTrace_6820325
  have hstable : (prefixWord ++ tailWord_6820325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820325).length < 2 ^ (prefixWord ++ tailWord_6820325).sum := by decide
  have hdescent : baseEnd_6820325 < baseStart_6820325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820357 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 3, 4]
def baseStart_6820357 : Nat := 118140960795 + 6820357 * 2 ^ 59
def prefixEnd_6820357 : Nat := 4983230072969 + 3 ^ 40 * 6820357 * 2
def baseEnd_6820357 : Nat := 1167373792085692351857085

theorem tailTrace_6820357 : CollatzResearch.WordTrace tailWord_6820357 prefixEnd_6820357 1167373792085692351857085 := by
  unfold tailWord_6820357
  simp only [CollatzResearch.WordTrace]
  refine ⟨248758856152018888084315325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165839237434679258722876883 248758856152018888084315325)
  ·
    refine ⟨93284571057007083031618247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248758856152018888084315325 93284571057007083031618247)
    ·
      refine ⟨139926856585510624547427371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93284571057007083031618247 139926856585510624547427371)
      ·
        refine ⟨209890284878265936821141057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139926856585510624547427371 209890284878265936821141057)
        ·
          refine ⟨157417713658699452615855793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209890284878265936821141057 157417713658699452615855793)
          ·
            refine ⟨118063285244024589461891845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157417713658699452615855793 118063285244024589461891845)
            ·
              refine ⟨22136865983254610524104721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118063285244024589461891845 22136865983254610524104721)
              ·
                refine ⟨16602649487440957893078541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22136865983254610524104721 16602649487440957893078541)
                ·
                  refine ⟨6225993557790359209904453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16602649487440957893078541 6225993557790359209904453)
                  ·
                    refine ⟨1167373792085692351857085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6225993557790359209904453 1167373792085692351857085)
                    ·
                      rfl

theorem cell23_6820357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_6820357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820357 prefixEnd_6820357 := by exact prefixLift 6820357
  have htrace : WordTrace (prefixWord ++ tailWord_6820357) baseStart_6820357 baseEnd_6820357 := by
    simpa [prefixWord, tailWord_6820357, baseEnd_6820357] using wordTrace_append hprefix tailTrace_6820357
  have hstable : (prefixWord ++ tailWord_6820357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820357).length < 2 ^ (prefixWord ++ tailWord_6820357).sum := by decide
  have hdescent : baseEnd_6820357 < baseStart_6820357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820360 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_6820360 : Nat := 118140960795 + 6820360 * 2 ^ 59
def prefixEnd_6820360 : Nat := 4983230072969 + 3 ^ 40 * 6820360 * 2
def baseEnd_6820360 : Nat := 3502122916699040543833741

theorem tailTrace_6820360 : CollatzResearch.WordTrace tailWord_6820360 prefixEnd_6820360 3502122916699040543833741 := by
  unfold tailWord_6820360
  simp only [CollatzResearch.WordTrace]
  refine ⟨124379482785504009798337267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165839310380672013064449689 124379482785504009798337267)
  ·
    refine ⟨186569224178256014697505901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124379482785504009798337267 186569224178256014697505901)
    ·
      refine ⟨69963459066846005511564713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186569224178256014697505901 69963459066846005511564713)
      ·
        refine ⟨52472594300134504133673535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69963459066846005511564713 52472594300134504133673535)
        ·
          refine ⟨78708891450201756200510303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52472594300134504133673535 78708891450201756200510303)
          ·
            refine ⟨118063337175302634300765455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78708891450201756200510303 118063337175302634300765455)
            ·
              refine ⟨177095005762953951451148183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118063337175302634300765455 177095005762953951451148183)
              ·
                refine ⟨265642508644430927176722275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177095005762953951451148183 265642508644430927176722275)
                ·
                  refine ⟨398463762966646390765083413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265642508644430927176722275 398463762966646390765083413)
                  ·
                    refine ⟨18677988889061549567113285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 398463762966646390765083413 18677988889061549567113285)
                    ·
                      refine ⟨3502122916699040543833741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18677988889061549567113285 3502122916699040543833741)
                      ·
                        rfl

theorem cell23_6820360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_6820360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820360 prefixEnd_6820360 := by exact prefixLift 6820360
  have htrace : WordTrace (prefixWord ++ tailWord_6820360) baseStart_6820360 baseEnd_6820360 := by
    simpa [prefixWord, tailWord_6820360, baseEnd_6820360] using wordTrace_append hprefix tailTrace_6820360
  have hstable : (prefixWord ++ tailWord_6820360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820360).length < 2 ^ (prefixWord ++ tailWord_6820360).sum := by decide
  have hdescent : baseEnd_6820360 < baseStart_6820360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820447 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 4, 4]
def baseStart_6820447 : Nat := 118140960795 + 6820447 * 2 ^ 59
def prefixEnd_6820447 : Nat := 4983230072969 + 3 ^ 40 * 6820447 * 2
def baseEnd_6820447 : Nat := 1167389196505327234481947

theorem tailTrace_6820447 : CollatzResearch.WordTrace tailWord_6820447 prefixEnd_6820447 1167389196505327234481947 := by
  unfold tailWord_6820447
  simp only [CollatzResearch.WordTrace]
  refine ⟨248762138721692833455091595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165841425814461888970061063 248762138721692833455091595)
  ·
    refine ⟨373143208082539250182637393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248762138721692833455091595 373143208082539250182637393)
    ·
      refine ⟨279857406061904437636978045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373143208082539250182637393 279857406061904437636978045)
      ·
        refine ⟨104946527273214164113866767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279857406061904437636978045 104946527273214164113866767)
        ·
          refine ⟨157419790909821246170800151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104946527273214164113866767 157419790909821246170800151)
          ·
            refine ⟨236129686364731869256200227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157419790909821246170800151 236129686364731869256200227)
            ·
              refine ⟨354194529547097803884300341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236129686364731869256200227 354194529547097803884300341)
              ·
                refine ⟨33205737145040419114153157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 354194529547097803884300341 33205737145040419114153157)
                ·
                  refine ⟨6226075714695078583903717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33205737145040419114153157 6226075714695078583903717)
                  ·
                    refine ⟨1167389196505327234481947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6226075714695078583903717 1167389196505327234481947)
                    ·
                      rfl

theorem cell23_6820447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 4].length) (baseStart_6820447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820447 prefixEnd_6820447 := by exact prefixLift 6820447
  have htrace : WordTrace (prefixWord ++ tailWord_6820447) baseStart_6820447 baseEnd_6820447 := by
    simpa [prefixWord, tailWord_6820447, baseEnd_6820447] using wordTrace_append hprefix tailTrace_6820447
  have hstable : (prefixWord ++ tailWord_6820447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820447).length < 2 ^ (prefixWord ++ tailWord_6820447).sum := by decide
  have hdescent : baseEnd_6820447 < baseStart_6820447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820448 : List Nat := [2, 1, 1, 3, 2, 1, 6, 2, 1, 1, 3]
def baseStart_6820448 : Nat := 118140960795 + 6820448 * 2 ^ 59
def prefixEnd_6820448 : Nat := 4983230072969 + 3 ^ 40 * 6820448 * 2
def baseEnd_6820448 : Nat := 3502168102996636199533337

theorem tailTrace_6820448 : CollatzResearch.WordTrace tailWord_6820448 prefixEnd_6820448 3502168102996636199533337 := by
  unfold tailWord_6820448
  simp only [CollatzResearch.WordTrace]
  refine ⟨124381087597344605312938999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165841450129792807083918665 124381087597344605312938999)
  ·
    refine ⟨186571631396016907969408499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124381087597344605312938999 186571631396016907969408499)
    ·
      refine ⟨279857447094025361954112749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186571631396016907969408499 279857447094025361954112749)
      ·
        refine ⟨104946542660259510732792281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279857447094025361954112749 104946542660259510732792281)
        ·
          refine ⟨78709906995194633049594211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104946542660259510732792281 78709906995194633049594211)
          ·
            refine ⟨118064860492791949574391317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78709906995194633049594211 118064860492791949574391317)
            ·
              refine ⟨5534290335599622636299593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118064860492791949574391317 5534290335599622636299593)
              ·
                refine ⟨4150717751699716977224695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5534290335599622636299593 4150717751699716977224695)
                ·
                  refine ⟨6226076627549575465837043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150717751699716977224695 6226076627549575465837043)
                  ·
                    refine ⟨9339114941324363198755565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6226076627549575465837043 9339114941324363198755565)
                    ·
                      refine ⟨3502168102996636199533337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9339114941324363198755565 3502168102996636199533337)
                      ·
                        rfl

theorem cell23_6820448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_6820448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820448 prefixEnd_6820448 := by exact prefixLift 6820448
  have htrace : WordTrace (prefixWord ++ tailWord_6820448) baseStart_6820448 baseEnd_6820448 := by
    simpa [prefixWord, tailWord_6820448, baseEnd_6820448] using wordTrace_append hprefix tailTrace_6820448
  have hstable : (prefixWord ++ tailWord_6820448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820448).length < 2 ^ (prefixWord ++ tailWord_6820448).sum := by decide
  have hdescent : baseEnd_6820448 < baseStart_6820448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820464 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 1, 6]
def baseStart_6820464 : Nat := 118140960795 + 6820464 * 2 ^ 59
def prefixEnd_6820464 : Nat := 4983230072969 + 3 ^ 40 * 6820464 * 2
def baseEnd_6820464 : Nat := 1167392106229036045644421

theorem tailTrace_6820464 : CollatzResearch.WordTrace tailWord_6820464 prefixEnd_6820464 1167392106229036045644421 := by
  unfold tailWord_6820464
  simp only [CollatzResearch.WordTrace]
  refine ⟨124381379381315622679230223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165841839175087496905640297 124381379381315622679230223)
  ·
    refine ⟨186572069071973434018845335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124381379381315622679230223 186572069071973434018845335)
    ·
      refine ⟨279858103607960151028268003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186572069071973434018845335 279858103607960151028268003)
      ·
        refine ⟨419787155411940226542402005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279858103607960151028268003 419787155411940226542402005)
        ·
          refine ⟨9838761454967349059587547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 419787155411940226542402005 9838761454967349059587547)
          ·
            refine ⟨14758142182451023589381321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9838761454967349059587547 14758142182451023589381321)
            ·
              refine ⟨11068606636838267692035991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14758142182451023589381321 11068606636838267692035991)
              ·
                refine ⟨16602909955257401538053987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11068606636838267692035991 16602909955257401538053987)
                ·
                  refine ⟨24904364932886102307080981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16602909955257401538053987 24904364932886102307080981)
                  ·
                    refine ⟨1167392106229036045644421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24904364932886102307080981 1167392106229036045644421)
                    ·
                      rfl

theorem cell23_6820464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 6].length) (baseStart_6820464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820464 prefixEnd_6820464 := by exact prefixLift 6820464
  have htrace : WordTrace (prefixWord ++ tailWord_6820464) baseStart_6820464 baseEnd_6820464 := by
    simpa [prefixWord, tailWord_6820464, baseEnd_6820464] using wordTrace_append hprefix tailTrace_6820464
  have hstable : (prefixWord ++ tailWord_6820464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820464).length < 2 ^ (prefixWord ++ tailWord_6820464).sum := by decide
  have hdescent : baseEnd_6820464 < baseStart_6820464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820484 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_6820484 : Nat := 118140960795 + 6820484 * 2 ^ 59
def prefixEnd_6820484 : Nat := 4983230072969 + 3 ^ 40 * 6820484 * 2
def baseEnd_6820484 : Nat := 3502186588300198058683171

theorem tailTrace_6820484 : CollatzResearch.WordTrace tailWord_6820484 prefixEnd_6820484 3502186588300198058683171 := by
  unfold tailWord_6820484
  simp only [CollatzResearch.WordTrace]
  refine ⟨124381744111279394387094253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165842325481705859182792337 124381744111279394387094253)
  ·
    refine ⟨46643154041729772895160345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124381744111279394387094253 46643154041729772895160345)
    ·
      refine ⟨34982365531297329671370259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46643154041729772895160345 34982365531297329671370259)
      ·
        refine ⟨52473548296945994507055389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34982365531297329671370259 52473548296945994507055389)
        ·
          refine ⟨19677580611354747940145771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52473548296945994507055389 19677580611354747940145771)
          ·
            refine ⟨29516370917032121910218657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19677580611354747940145771 29516370917032121910218657)
            ·
              refine ⟨22137278187774091432663993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29516370917032121910218657 22137278187774091432663993)
              ·
                refine ⟨16602958640830568574497995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22137278187774091432663993 16602958640830568574497995)
                ·
                  refine ⟨24904437961245852861746993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16602958640830568574497995 24904437961245852861746993)
                  ·
                    refine ⟨18678328470934389646310245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24904437961245852861746993 18678328470934389646310245)
                    ·
                      refine ⟨3502186588300198058683171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18678328470934389646310245 3502186588300198058683171)
                      ·
                        rfl

theorem cell23_6820484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_6820484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820484 prefixEnd_6820484 := by exact prefixLift 6820484
  have htrace : WordTrace (prefixWord ++ tailWord_6820484) baseStart_6820484 baseEnd_6820484 := by
    simpa [prefixWord, tailWord_6820484, baseEnd_6820484] using wordTrace_append hprefix tailTrace_6820484
  have hstable : (prefixWord ++ tailWord_6820484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820484).length < 2 ^ (prefixWord ++ tailWord_6820484).sum := by decide
  have hdescent : baseEnd_6820484 < baseStart_6820484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820498 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_6820498 : Nat := 118140960795 + 6820498 * 2 ^ 59
def prefixEnd_6820498 : Nat := 4983230072969 + 3 ^ 40 * 6820498 * 2
def baseEnd_6820498 : Nat := 1167397925676453667969369

theorem tailTrace_6820498 : CollatzResearch.WordTrace tailWord_6820498 prefixEnd_6820498 1167397925676453667969369 := by
  unfold tailWord_6820498
  simp only [CollatzResearch.WordTrace]
  refine ⟨62190999711127017291299537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165842665896338712776798765 62190999711127017291299537)
  ·
    refine ⟨46643249783345262968474653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62190999711127017291299537 46643249783345262968474653)
    ·
      refine ⟨17491218668754473613177995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46643249783345262968474653 17491218668754473613177995)
      ·
        refine ⟨26236828003131710419766993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17491218668754473613177995 26236828003131710419766993)
        ·
          refine ⟨19677621002348782814825245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26236828003131710419766993 19677621002348782814825245)
          ·
            refine ⟨7379107875880793555559467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19677621002348782814825245 7379107875880793555559467)
            ·
              refine ⟨11068661813821190333339201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379107875880793555559467 11068661813821190333339201)
              ·
                refine ⟨8301496360365892750004401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11068661813821190333339201 8301496360365892750004401)
                ·
                  refine ⟨6226122270274419562503301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8301496360365892750004401 6226122270274419562503301)
                  ·
                    refine ⟨1167397925676453667969369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6226122270274419562503301 1167397925676453667969369)
                    ·
                      rfl

theorem cell23_6820498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_6820498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820498 prefixEnd_6820498 := by exact prefixLift 6820498
  have htrace : WordTrace (prefixWord ++ tailWord_6820498) baseStart_6820498 baseEnd_6820498 := by
    simpa [prefixWord, tailWord_6820498, baseEnd_6820498] using wordTrace_append hprefix tailTrace_6820498
  have hstable : (prefixWord ++ tailWord_6820498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820498).length < 2 ^ (prefixWord ++ tailWord_6820498).sum := by decide
  have hdescent : baseEnd_6820498 < baseStart_6820498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820531 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 1, 3, 2]
def baseStart_6820531 : Nat := 118140960795 + 6820531 * 2 ^ 59
def prefixEnd_6820531 : Nat := 4983230072969 + 3 ^ 40 * 6820531 * 2
def baseEnd_6820531 : Nat := 3502210721890959374795455

theorem tailTrace_6820531 : CollatzResearch.WordTrace tailWord_6820531 prefixEnd_6820531 3502210721890959374795455 := by
  unfold tailWord_6820531
  simp only [CollatzResearch.WordTrace]
  refine ⟨248765202453388515801149447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165843468302259010534099631 248765202453388515801149447)
  ·
    refine ⟨373147803680082773701724171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248765202453388515801149447 373147803680082773701724171)
    ·
      refine ⟨559721705520124160552586257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373147803680082773701724171 559721705520124160552586257)
      ·
        refine ⟨419791279140093120414439693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559721705520124160552586257 419791279140093120414439693)
        ·
          refine ⟨157421729677534920155414885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419791279140093120414439693 157421729677534920155414885)
          ·
            refine ⟨29516574314537797529140291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157421729677534920155414885 29516574314537797529140291)
            ·
              refine ⟨44274861471806696293710437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29516574314537797529140291 44274861471806696293710437)
              ·
                refine ⟨8301536525963755555070707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44274861471806696293710437 8301536525963755555070707)
                ·
                  refine ⟨12452304788945633332606061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8301536525963755555070707 12452304788945633332606061)
                  ·
                    refine ⟨4669614295854612499727273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12452304788945633332606061 4669614295854612499727273)
                    ·
                      refine ⟨3502210721890959374795455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669614295854612499727273 3502210721890959374795455)
                      ·
                        rfl

theorem cell23_6820531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 3, 2].length) (baseStart_6820531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820531 prefixEnd_6820531 := by exact prefixLift 6820531
  have htrace : WordTrace (prefixWord ++ tailWord_6820531) baseStart_6820531 baseEnd_6820531 := by
    simpa [prefixWord, tailWord_6820531, baseEnd_6820531] using wordTrace_append hprefix tailTrace_6820531
  have hstable : (prefixWord ++ tailWord_6820531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820531).length < 2 ^ (prefixWord ++ tailWord_6820531).sum := by decide
  have hdescent : baseEnd_6820531 < baseStart_6820531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820548 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_6820548 : Nat := 118140960795 + 6820548 * 2 ^ 59
def prefixEnd_6820548 : Nat := 4983230072969 + 3 ^ 40 * 6820548 * 2
def baseEnd_6820548 : Nat := 3502219451062085808282877

theorem tailTrace_6820548 : CollatzResearch.WordTrace tailWord_6820548 prefixEnd_6820548 3502219451062085808282877 := by
  unfold tailWord_6820548
  simp only [CollatzResearch.WordTrace]
  refine ⟨124382911247163463852259149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165843881662884618469678865 124382911247163463852259149)
  ·
    refine ⟨46643591717686298944597181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124382911247163463852259149 46643591717686298944597181)
    ·
      refine ⟨17491346894132362104223943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46643591717686298944597181 17491346894132362104223943)
      ·
        refine ⟨26237020341198543156335915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17491346894132362104223943 26237020341198543156335915)
        ·
          refine ⟨39355530511797814734503873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26237020341198543156335915 39355530511797814734503873)
          ·
            refine ⟨29516647883848361050877905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39355530511797814734503873 29516647883848361050877905)
            ·
              refine ⟨22137485912886270788158429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29516647883848361050877905 22137485912886270788158429)
              ·
                refine ⟨8301557217332351545559411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22137485912886270788158429 8301557217332351545559411)
                ·
                  refine ⟨12452335825998527318339117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8301557217332351545559411 12452335825998527318339117)
                  ·
                    refine ⟨4669625934749447744377169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12452335825998527318339117 4669625934749447744377169)
                    ·
                      refine ⟨3502219451062085808282877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669625934749447744377169 3502219451062085808282877)
                      ·
                        rfl

theorem cell23_6820548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_6820548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820548 prefixEnd_6820548 := by exact prefixLift 6820548
  have htrace : WordTrace (prefixWord ++ tailWord_6820548) baseStart_6820548 baseEnd_6820548 := by
    simpa [prefixWord, tailWord_6820548, baseEnd_6820548] using wordTrace_append hprefix tailTrace_6820548
  have hstable : (prefixWord ++ tailWord_6820548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820548).length < 2 ^ (prefixWord ++ tailWord_6820548).sum := by decide
  have hdescent : baseEnd_6820548 < baseStart_6820548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820561 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 4, 2, 2]
def baseStart_6820561 : Nat := 118140960795 + 6820561 * 2 ^ 59
def prefixEnd_6820561 : Nat := 4983230072969 + 3 ^ 40 * 6820561 * 2
def baseEnd_6820561 : Nat := 3502226126310594257420317

theorem tailTrace_6820561 : CollatzResearch.WordTrace tailWord_6820561 prefixEnd_6820561 3502226126310594257420317 := by
  unfold tailWord_6820561
  simp only [CollatzResearch.WordTrace]
  refine ⟨248766296643279830924741537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165844197762186553949827691 248766296643279830924741537)
  ·
    refine ⟨186574722482459873193556153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248766296643279830924741537 186574722482459873193556153)
    ·
      refine ⟨139931041861844904895167115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186574722482459873193556153 139931041861844904895167115)
      ·
        refine ⟨209896562792767357342750673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139931041861844904895167115 209896562792767357342750673)
        ·
          refine ⟨157422422094575518007063005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209896562792767357342750673 157422422094575518007063005)
          ·
            refine ⟨59033408285465819252648627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157422422094575518007063005 59033408285465819252648627)
            ·
              refine ⟨88550112428198728878972941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59033408285465819252648627 88550112428198728878972941)
              ·
                refine ⟨33206292160574523329614853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88550112428198728878972941 33206292160574523329614853)
                ·
                  refine ⟨6226179780107723124302785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33206292160574523329614853 6226179780107723124302785)
                  ·
                    refine ⟨4669634835080792343227089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6226179780107723124302785 4669634835080792343227089)
                    ·
                      refine ⟨3502226126310594257420317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669634835080792343227089 3502226126310594257420317)
                      ·
                        rfl

theorem cell23_6820561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 2, 2].length) (baseStart_6820561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820561 prefixEnd_6820561 := by exact prefixLift 6820561
  have htrace : WordTrace (prefixWord ++ tailWord_6820561) baseStart_6820561 baseEnd_6820561 := by
    simpa [prefixWord, tailWord_6820561, baseEnd_6820561] using wordTrace_append hprefix tailTrace_6820561
  have hstable : (prefixWord ++ tailWord_6820561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820561).length < 2 ^ (prefixWord ++ tailWord_6820561).sum := by decide
  have hdescent : baseEnd_6820561 < baseStart_6820561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820572 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_6820572 : Nat := 118140960795 + 6820572 * 2 ^ 59
def prefixEnd_6820572 : Nat := 4983230072969 + 3 ^ 40 * 6820572 * 2
def baseEnd_6820572 : Nat := 3502231774597793714382767

theorem tailTrace_6820572 : CollatzResearch.WordTrace tailWord_6820572 prefixEnd_6820572 3502231774597793714382767 := by
  unfold tailWord_6820572
  simp only [CollatzResearch.WordTrace]
  refine ⟨124383348923119989901695985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165844465230826653202261313 124383348923119989901695985)
  ·
    refine ⟨93287511692339992426271989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124383348923119989901695985 93287511692339992426271989)
    ·
      refine ⟨8745704221156874289962999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93287511692339992426271989 8745704221156874289962999)
      ·
        refine ⟨13118556331735311434944499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8745704221156874289962999 13118556331735311434944499)
        ·
          refine ⟨19677834497602967152416749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13118556331735311434944499 19677834497602967152416749)
          ·
            refine ⟨7379187936601112682156281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19677834497602967152416749 7379187936601112682156281)
            ·
              refine ⟨5534390952450834511617211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7379187936601112682156281 5534390952450834511617211)
              ·
                refine ⟨8301586428676251767425817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5534390952450834511617211 8301586428676251767425817)
                ·
                  refine ⟨6226189821507188825569363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8301586428676251767425817 6226189821507188825569363)
                  ·
                    refine ⟨9339284732260783238354045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6226189821507188825569363 9339284732260783238354045)
                    ·
                      refine ⟨3502231774597793714382767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9339284732260783238354045 3502231774597793714382767)
                      ·
                        rfl

theorem cell23_6820572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_6820572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820572 prefixEnd_6820572 := by exact prefixLift 6820572
  have htrace : WordTrace (prefixWord ++ tailWord_6820572) baseStart_6820572 baseEnd_6820572 := by
    simpa [prefixWord, tailWord_6820572, baseEnd_6820572] using wordTrace_append hprefix tailTrace_6820572
  have hstable : (prefixWord ++ tailWord_6820572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820572).length < 2 ^ (prefixWord ++ tailWord_6820572).sum := by decide
  have hdescent : baseEnd_6820572 < baseStart_6820572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820634 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_6820634 : Nat := 118140960795 + 6820634 * 2 ^ 59
def prefixEnd_6820634 : Nat := 4983230072969 + 3 ^ 40 * 6820634 * 2
def baseEnd_6820634 : Nat := 3502263610398372471807481

theorem tailTrace_6820634 : CollatzResearch.WordTrace tailWord_6820634 prefixEnd_6820634 3502263610398372471807481 := by
  unfold tailWord_6820634
  simp only [CollatzResearch.WordTrace]
  refine ⟨62192239793003841098037239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165845972781343576261432637 62192239793003841098037239)
  ·
    refine ⟨93288359689505761647055859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62192239793003841098037239 93288359689505761647055859)
    ·
      refine ⟨139932539534258642470583789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93288359689505761647055859 139932539534258642470583789)
      ·
        refine ⟨52474702325346990926468921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139932539534258642470583789 52474702325346990926468921)
        ·
          refine ⟨39356026744010243194851691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52474702325346990926468921 39356026744010243194851691)
          ·
            refine ⟨59034040116015364792277537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39356026744010243194851691 59034040116015364792277537)
            ·
              refine ⟨44275530087011523594208153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59034040116015364792277537 44275530087011523594208153)
              ·
                refine ⟨33206647565258642695656115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44275530087011523594208153 33206647565258642695656115)
                ·
                  refine ⟨49809971347887964043484173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33206647565258642695656115 49809971347887964043484173)
                  ·
                    refine ⟨18678739255457986516306565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49809971347887964043484173 18678739255457986516306565)
                    ·
                      refine ⟨3502263610398372471807481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18678739255457986516306565 3502263610398372471807481)
                      ·
                        rfl

theorem cell23_6820634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_6820634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820634 prefixEnd_6820634 := by exact prefixLift 6820634
  have htrace : WordTrace (prefixWord ++ tailWord_6820634) baseStart_6820634 baseEnd_6820634 := by
    simpa [prefixWord, tailWord_6820634, baseEnd_6820634] using wordTrace_append hprefix tailTrace_6820634
  have hstable : (prefixWord ++ tailWord_6820634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820634).length < 2 ^ (prefixWord ++ tailWord_6820634).sum := by decide
  have hdescent : baseEnd_6820634 < baseStart_6820634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820667 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 7]
def baseStart_6820667 : Nat := 118140960795 + 6820667 * 2 ^ 59
def prefixEnd_6820667 : Nat := 4983230072969 + 3 ^ 40 * 6820667 * 2
def baseEnd_6820667 : Nat := 3502280555259970842694829

theorem tailTrace_6820667 : CollatzResearch.WordTrace tailWord_6820667 prefixEnd_6820667 3502280555259970842694829 := by
  unfold tailWord_6820667
  simp only [CollatzResearch.WordTrace]
  refine ⟨248770162780895811028100255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165846775187263874018733503 248770162780895811028100255)
  ·
    refine ⟨373155244171343716542150383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248770162780895811028100255 373155244171343716542150383)
    ·
      refine ⟨559732866257015574813225575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373155244171343716542150383 559732866257015574813225575)
      ·
        refine ⟨839599299385523362219838363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559732866257015574813225575 839599299385523362219838363)
        ·
          refine ⟨1259398949078285043329757545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839599299385523362219838363 1259398949078285043329757545)
          ·
            refine ⟨944549211808713782497318159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259398949078285043329757545 944549211808713782497318159)
            ·
              refine ⟨1416823817713070673745977239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944549211808713782497318159 1416823817713070673745977239)
              ·
                refine ⟨2125235726569606010618965859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416823817713070673745977239 2125235726569606010618965859)
                ·
                  refine ⟨3187853589854409015928448789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125235726569606010618965859 3187853589854409015928448789)
                  ·
                    refine ⟨149430637024425422621646037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3187853589854409015928448789 149430637024425422621646037)
                    ·
                      refine ⟨3502280555259970842694829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149430637024425422621646037 3502280555259970842694829)
                      ·
                        rfl

theorem cell23_6820667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_6820667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820667 prefixEnd_6820667 := by exact prefixLift 6820667
  have htrace : WordTrace (prefixWord ++ tailWord_6820667) baseStart_6820667 baseEnd_6820667 := by
    simpa [prefixWord, tailWord_6820667, baseEnd_6820667] using wordTrace_append hprefix tailTrace_6820667
  have hstable : (prefixWord ++ tailWord_6820667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820667).length < 2 ^ (prefixWord ++ tailWord_6820667).sum := by decide
  have hdescent : baseEnd_6820667 < baseStart_6820667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820721 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 1, 5]
def baseStart_6820721 : Nat := 118140960795 + 6820721 * 2 ^ 59
def prefixEnd_6820721 : Nat := 4983230072969 + 3 ^ 40 * 6820721 * 2
def baseEnd_6820721 : Nat := 1167436094405104543806527

theorem tailTrace_6820721 : CollatzResearch.WordTrace tailWord_6820721 prefixEnd_6820721 1167436094405104543806527 := by
  unfold tailWord_6820721
  simp only [CollatzResearch.WordTrace]
  refine ⟨248772132322700178250566017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165848088215133452167044011 248772132322700178250566017)
  ·
    refine ⟨186579099242025133687924513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248772132322700178250566017 186579099242025133687924513)
    ·
      refine ⟨139934324431518850265943385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186579099242025133687924513 139934324431518850265943385)
      ·
        refine ⟨104950743323639137699457539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139934324431518850265943385 104950743323639137699457539)
        ·
          refine ⟨157426114985458706549186309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104950743323639137699457539 157426114985458706549186309)
          ·
            refine ⟨29517396559773507477972433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157426114985458706549186309 29517396559773507477972433)
            ·
              refine ⟨22138047419830130608479325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29517396559773507477972433 22138047419830130608479325)
              ·
                refine ⟨8301767782436298978179747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22138047419830130608479325 8301767782436298978179747)
                ·
                  refine ⟨12452651673654448467269621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8301767782436298978179747 12452651673654448467269621)
                  ·
                    refine ⟨1167436094405104543806527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12452651673654448467269621 1167436094405104543806527)
                    ·
                      rfl

theorem cell23_6820721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_6820721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820721 prefixEnd_6820721 := by exact prefixLift 6820721
  have htrace : WordTrace (prefixWord ++ tailWord_6820721) baseStart_6820721 baseEnd_6820721 := by
    simpa [prefixWord, tailWord_6820721, baseEnd_6820721] using wordTrace_append hprefix tailTrace_6820721
  have hstable : (prefixWord ++ tailWord_6820721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820721).length < 2 ^ (prefixWord ++ tailWord_6820721).sum := by decide
  have hdescent : baseEnd_6820721 < baseStart_6820721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820781 : List Nat := [1, 5, 2, 3, 12]
def baseStart_6820781 : Nat := 118140960795 + 6820781 * 2 ^ 59
def prefixEnd_6820781 : Nat := 4983230072969 + 3 ^ 40 * 6820781 * 2
def baseEnd_6820781 : Nat := 4804306024766232368545

theorem tailTrace_6820781 : CollatzResearch.WordTrace tailWord_6820781 prefixEnd_6820781 4804306024766232368545 := by
  unfold tailWord_6820781
  simp only [CollatzResearch.WordTrace]
  refine ⟨248774320702482808497750197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165849547134988538998500131 248774320702482808497750197)
  ·
    refine ⟨23322592565857763296664081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248774320702482808497750197 23322592565857763296664081)
    ·
      refine ⟨17491944424393322472498061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23322592565857763296664081 17491944424393322472498061)
      ·
        refine ⟨6559479159147495927186773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17491944424393322472498061 6559479159147495927186773)
        ·
          refine ⟨4804306024766232368545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6559479159147495927186773 4804306024766232368545)
          ·
            rfl

theorem cell23_6820781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 12].length) (baseStart_6820781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820781 prefixEnd_6820781 := by exact prefixLift 6820781
  have htrace : WordTrace (prefixWord ++ tailWord_6820781) baseStart_6820781 baseEnd_6820781 := by
    simpa [prefixWord, tailWord_6820781, baseEnd_6820781] using wordTrace_append hprefix tailTrace_6820781
  have hstable : (prefixWord ++ tailWord_6820781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820781).length < 2 ^ (prefixWord ++ tailWord_6820781).sum := by decide
  have hdescent : baseEnd_6820781 < baseStart_6820781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820785 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 2, 4]
def baseStart_6820785 : Nat := 118140960795 + 6820785 * 2 ^ 59
def prefixEnd_6820785 : Nat := 4983230072969 + 3 ^ 40 * 6820785 * 2
def baseEnd_6820785 : Nat := 1167447048659067127006429

theorem tailTrace_6820785 : CollatzResearch.WordTrace tailWord_6820785 prefixEnd_6820785 1167447048659067127006429 := by
  unfold tailWord_6820785
  simp only [CollatzResearch.WordTrace]
  refine ⟨248774466594468317180895809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165849644396312211453930539 248774466594468317180895809)
  ·
    refine ⟨186580849945851237885671857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248774466594468317180895809 186580849945851237885671857)
    ·
      refine ⟨139935637459388428414253893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186580849945851237885671857 139935637459388428414253893)
      ·
        refine ⟨26237932023635330327672605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139935637459388428414253893 26237932023635330327672605)
        ·
          refine ⟨9839224508863248872877227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26237932023635330327672605 9839224508863248872877227)
          ·
            refine ⟨14758836763294873309315841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9839224508863248872877227 14758836763294873309315841)
            ·
              refine ⟨11069127572471154981986881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14758836763294873309315841 11069127572471154981986881)
              ·
                refine ⟨8301845679353366236490161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11069127572471154981986881 8301845679353366236490161)
                ·
                  refine ⟨6226384259515024677367621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8301845679353366236490161 6226384259515024677367621)
                  ·
                    refine ⟨1167447048659067127006429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6226384259515024677367621 1167447048659067127006429)
                    ·
                      rfl

theorem cell23_6820785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_6820785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820785 prefixEnd_6820785 := by exact prefixLift 6820785
  have htrace : WordTrace (prefixWord ++ tailWord_6820785) baseStart_6820785 baseEnd_6820785 := by
    simpa [prefixWord, tailWord_6820785, baseEnd_6820785] using wordTrace_append hprefix tailTrace_6820785
  have hstable : (prefixWord ++ tailWord_6820785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820785).length < 2 ^ (prefixWord ++ tailWord_6820785).sum := by decide
  have hdescent : baseEnd_6820785 < baseStart_6820785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820792 : List Nat := [2, 1, 2, 1, 2, 5, 1, 4, 1, 2, 2]
def baseStart_6820792 : Nat := 118140960795 + 6820792 * 2 ^ 59
def prefixEnd_6820792 : Nat := 4983230072969 + 3 ^ 40 * 6820792 * 2
def baseEnd_6820792 : Nat := 3502344740341782853631755

theorem tailTrace_6820792 : CollatzResearch.WordTrace tailWord_6820792 prefixEnd_6820792 3502344740341782853631755 := by
  unfold tailWord_6820792
  simp only [CollatzResearch.WordTrace]
  refine ⟨124387360952721478688200315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165849814603628638250933753 124387360952721478688200315)
  ·
    refine ⟨186581041429082218032300473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124387360952721478688200315 186581041429082218032300473)
    ·
      refine ⟨139935781071811663524225355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186581041429082218032300473 139935781071811663524225355)
      ·
        refine ⟨209903671607717495286338033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139935781071811663524225355 209903671607717495286338033)
        ·
          refine ⟨157427753705788121464753525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209903671607717495286338033 157427753705788121464753525)
          ·
            refine ⟨14758851909917636387320643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157427753705788121464753525 14758851909917636387320643)
            ·
              refine ⟨22138277864876454580980965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14758851909917636387320643 22138277864876454580980965)
              ·
                refine ⟨4150927099664335233933931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22138277864876454580980965 4150927099664335233933931)
                ·
                  refine ⟨6226390649496502850900897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150927099664335233933931 6226390649496502850900897)
                  ·
                    refine ⟨4669792987122377138175673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6226390649496502850900897 4669792987122377138175673)
                    ·
                      refine ⟨3502344740341782853631755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669792987122377138175673 3502344740341782853631755)
                      ·
                        rfl

theorem cell23_6820792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 1, 2, 2].length) (baseStart_6820792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820792 prefixEnd_6820792 := by exact prefixLift 6820792
  have htrace : WordTrace (prefixWord ++ tailWord_6820792) baseStart_6820792 baseEnd_6820792 := by
    simpa [prefixWord, tailWord_6820792, baseEnd_6820792] using wordTrace_append hprefix tailTrace_6820792
  have hstable : (prefixWord ++ tailWord_6820792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820792).length < 2 ^ (prefixWord ++ tailWord_6820792).sum := by decide
  have hdescent : baseEnd_6820792 < baseStart_6820792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820794 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_6820794 : Nat := 118140960795 + 6820794 * 2 ^ 59
def prefixEnd_6820794 : Nat := 4983230072969 + 3 ^ 40 * 6820794 * 2
def baseEnd_6820794 : Nat := 1167448589101030615268915

theorem tailTrace_6820794 : CollatzResearch.WordTrace tailWord_6820794 prefixEnd_6820794 1167448589101030615268915 := by
  unfold tailWord_6820794
  simp only [CollatzResearch.WordTrace]
  refine ⟨62193698712858927929493359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165849863234290474478648957 62193698712858927929493359)
  ·
    refine ⟨93290548069288391894240039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62193698712858927929493359 93290548069288391894240039)
    ·
      refine ⟨139935822103932587841360059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93290548069288391894240039 139935822103932587841360059)
      ·
        refine ⟨209903733155898881762040089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139935822103932587841360059 209903733155898881762040089)
        ·
          refine ⟨157427799866924161321530067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209903733155898881762040089 157427799866924161321530067)
          ·
            refine ⟨236141699800386241982295101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157427799866924161321530067 236141699800386241982295101)
            ·
              refine ⟨88553137425144840743360663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236141699800386241982295101 88553137425144840743360663)
              ·
                refine ⟨132829706137717261115040995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88553137425144840743360663 132829706137717261115040995)
                ·
                  refine ⟨199244559206575891672561493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132829706137717261115040995 199244559206575891672561493)
                  ·
                    refine ⟨1167448589101030615268915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 199244559206575891672561493 1167448589101030615268915)
                    ·
                      rfl

theorem cell23_6820794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_6820794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820794 prefixEnd_6820794 := by exact prefixLift 6820794
  have htrace : WordTrace (prefixWord ++ tailWord_6820794) baseStart_6820794 baseEnd_6820794 := by
    simpa [prefixWord, tailWord_6820794, baseEnd_6820794] using wordTrace_append hprefix tailTrace_6820794
  have hstable : (prefixWord ++ tailWord_6820794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820794).length < 2 ^ (prefixWord ++ tailWord_6820794).sum := by decide
  have hdescent : baseEnd_6820794 < baseStart_6820794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820813 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6820813 : Nat := 118140960795 + 6820813 * 2 ^ 59
def prefixEnd_6820813 : Nat := 4983230072969 + 3 ^ 40 * 6820813 * 2
def baseEnd_6820813 : Nat := 3502355523435527271469159

theorem tailTrace_6820813 : CollatzResearch.WordTrace tailWord_6820813 prefixEnd_6820813 3502355523435527271469159 := by
  unfold tailWord_6820813
  simp only [CollatzResearch.WordTrace]
  refine ⟨248775487838366877962915093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165850325225577918641943395 248775487838366877962915093)
  ·
    refine ⟨11661350992423447404511645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248775487838366877962915093 11661350992423447404511645)
    ·
      refine ⟨4373006622158792776691867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11661350992423447404511645 4373006622158792776691867)
      ·
        refine ⟨6559509933238189165037801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4373006622158792776691867 6559509933238189165037801)
        ·
          refine ⟨4919632449928641873778351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6559509933238189165037801 4919632449928641873778351)
          ·
            refine ⟨7379448674892962810667527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919632449928641873778351 7379448674892962810667527)
            ·
              refine ⟨11069173012339444216001291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379448674892962810667527 11069173012339444216001291)
              ·
                refine ⟨16603759518509166324001937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11069173012339444216001291 16603759518509166324001937)
                ·
                  refine ⟨12452819638881874743001453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16603759518509166324001937 12452819638881874743001453)
                  ·
                    refine ⟨4669807364580703028625545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12452819638881874743001453 4669807364580703028625545)
                    ·
                      refine ⟨3502355523435527271469159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669807364580703028625545 3502355523435527271469159)
                      ·
                        rfl

theorem cell23_6820813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6820813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820813 prefixEnd_6820813 := by exact prefixLift 6820813
  have htrace : WordTrace (prefixWord ++ tailWord_6820813) baseStart_6820813 baseEnd_6820813 := by
    simpa [prefixWord, tailWord_6820813, baseEnd_6820813] using wordTrace_append hprefix tailTrace_6820813
  have hstable : (prefixWord ++ tailWord_6820813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820813).length < 2 ^ (prefixWord ++ tailWord_6820813).sum := by decide
  have hdescent : baseEnd_6820813 < baseStart_6820813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820835 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 1, 3, 2]
def baseStart_6820835 : Nat := 118140960795 + 6820835 * 2 ^ 59
def prefixEnd_6820835 : Nat := 4983230072969 + 3 ^ 40 * 6820835 * 2
def baseEnd_6820835 : Nat := 3502366820009926185394057

theorem tailTrace_6820835 : CollatzResearch.WordTrace tailWord_6820835 prefixEnd_6820835 3502366820009926185394057 := by
  unfold tailWord_6820835
  simp only [CollatzResearch.WordTrace]
  refine ⟨248776290244287175720215959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165850860162858117146810639 248776290244287175720215959)
  ·
    refine ⟨373164435366430763580323939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248776290244287175720215959 373164435366430763580323939)
    ·
      refine ⟨559746653049646145370485909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373164435366430763580323939 559746653049646145370485909)
      ·
        refine ⟨26238124361702163064241527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 559746653049646145370485909 26238124361702163064241527)
        ·
          refine ⟨39357186542553244596362291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26238124361702163064241527 39357186542553244596362291)
          ·
            refine ⟨59035779813829866894543437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39357186542553244596362291 59035779813829866894543437)
            ·
              refine ⟨22138417430186200085453789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59035779813829866894543437 22138417430186200085453789)
              ·
                refine ⟨8301906536319825032045171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22138417430186200085453789 8301906536319825032045171)
                ·
                  refine ⟨12452859804479737548067757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8301906536319825032045171 12452859804479737548067757)
                  ·
                    refine ⟨4669822426679901580525409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12452859804479737548067757 4669822426679901580525409)
                    ·
                      refine ⟨3502366820009926185394057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669822426679901580525409 3502366820009926185394057)
                      ·
                        rfl

theorem cell23_6820835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_6820835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820835 prefixEnd_6820835 := by exact prefixLift 6820835
  have htrace : WordTrace (prefixWord ++ tailWord_6820835) baseStart_6820835 baseEnd_6820835 := by
    simpa [prefixWord, tailWord_6820835, baseEnd_6820835] using wordTrace_append hprefix tailTrace_6820835
  have hstable : (prefixWord ++ tailWord_6820835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820835).length < 2 ^ (prefixWord ++ tailWord_6820835).sum := by decide
  have hdescent : baseEnd_6820835 < baseStart_6820835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820842 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_6820842 : Nat := 118140960795 + 6820842 * 2 ^ 59
def prefixEnd_6820842 : Nat := 4983230072969 + 3 ^ 40 * 6820842 * 2
def baseEnd_6820842 : Nat := 3502370414374507658006525

theorem tailTrace_6820842 : CollatzResearch.WordTrace tailWord_6820842 prefixEnd_6820842 3502370414374507658006525 := by
  unfold tailWord_6820842
  simp only [CollatzResearch.WordTrace]
  refine ⟨62194136388815453978930195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165851030370174543943813853 62194136388815453978930195)
  ·
    refine ⟨93291204583223180968395293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62194136388815453978930195 93291204583223180968395293)
    ·
      refine ⟨34984201718708692863148235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93291204583223180968395293 34984201718708692863148235)
      ·
        refine ⟨52476302578063039294722353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34984201718708692863148235 52476302578063039294722353)
        ·
          refine ⟨39357226933547279471041765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52476302578063039294722353 39357226933547279471041765)
          ·
            refine ⟨7379480050040114900820331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39357226933547279471041765 7379480050040114900820331)
            ·
              refine ⟨11069220075060172351230497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379480050040114900820331 11069220075060172351230497)
              ·
                refine ⟨8301915056295129263422873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11069220075060172351230497 8301915056295129263422873)
                ·
                  refine ⟨6226436292221346947567155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8301915056295129263422873 6226436292221346947567155)
                  ·
                    refine ⟨9339654438332020421350733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6226436292221346947567155 9339654438332020421350733)
                    ·
                      refine ⟨3502370414374507658006525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9339654438332020421350733 3502370414374507658006525)
                      ·
                        rfl

theorem cell23_6820842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_6820842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820842 prefixEnd_6820842 := by exact prefixLift 6820842
  have htrace : WordTrace (prefixWord ++ tailWord_6820842) baseStart_6820842 baseEnd_6820842 := by
    simpa [prefixWord, tailWord_6820842, baseEnd_6820842] using wordTrace_append hprefix tailTrace_6820842
  have hstable : (prefixWord ++ tailWord_6820842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820842).length < 2 ^ (prefixWord ++ tailWord_6820842).sum := by decide
  have hdescent : baseEnd_6820842 < baseStart_6820842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820865 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_6820865 : Nat := 118140960795 + 6820865 * 2 ^ 59
def prefixEnd_6820865 : Nat := 4983230072969 + 3 ^ 40 * 6820865 * 2
def baseEnd_6820865 : Nat := 3502382224429561068018919

theorem tailTrace_6820865 : CollatzResearch.WordTrace tailWord_6820865 prefixEnd_6820865 3502382224429561068018919 := by
  unfold tailWord_6820865
  simp only [CollatzResearch.WordTrace]
  refine ⟨248777384434178490843808049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165851589622785660562538699 248777384434178490843808049)
  ·
    refine ⟨186583038325633868132856037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248777384434178490843808049 186583038325633868132856037)
    ·
      refine ⟨34984319686056350274910507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186583038325633868132856037 34984319686056350274910507)
      ·
        refine ⟨52476479529084525412365761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34984319686056350274910507 52476479529084525412365761)
        ·
          refine ⟨39357359646813394059274321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52476479529084525412365761 39357359646813394059274321)
          ·
            refine ⟨29518019735110045544455741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39357359646813394059274321 29518019735110045544455741)
            ·
              refine ⟨11069257400666267079170903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29518019735110045544455741 11069257400666267079170903)
              ·
                refine ⟨16603886100999400618756355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11069257400666267079170903 16603886100999400618756355)
                ·
                  refine ⟨24905829151499100928134533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16603886100999400618756355 24905829151499100928134533)
                  ·
                    refine ⟨4669842965906081424025225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24905829151499100928134533 4669842965906081424025225)
                    ·
                      refine ⟨3502382224429561068018919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669842965906081424025225 3502382224429561068018919)
                      ·
                        rfl

theorem cell23_6820865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_6820865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820865 prefixEnd_6820865 := by exact prefixLift 6820865
  have htrace : WordTrace (prefixWord ++ tailWord_6820865) baseStart_6820865 baseEnd_6820865 := by
    simpa [prefixWord, tailWord_6820865, baseEnd_6820865] using wordTrace_append hprefix tailTrace_6820865
  have hstable : (prefixWord ++ tailWord_6820865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820865).length < 2 ^ (prefixWord ++ tailWord_6820865).sum := by decide
  have hdescent : baseEnd_6820865 < baseStart_6820865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820871 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 7]
def baseStart_6820871 : Nat := 118140960795 + 6820871 * 2 ^ 59
def prefixEnd_6820871 : Nat := 4983230072969 + 3 ^ 40 * 6820871 * 2
def baseEnd_6820871 : Nat := 389153922812609782727099

theorem tailTrace_6820871 : CollatzResearch.WordTrace tailWord_6820871 prefixEnd_6820871 389153922812609782727099 := by
  unfold tailWord_6820871
  simp only [CollatzResearch.WordTrace]
  refine ⟨248777603272156753868526467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165851735514771169245684311 248777603272156753868526467)
  ·
    refine ⟨373166404908235130802789701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248777603272156753868526467 373166404908235130802789701)
    ·
      refine ⟨69968700920294087025523069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373166404908235130802789701 69968700920294087025523069)
      ·
        refine ⟨26238262845110282634571151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69968700920294087025523069 26238262845110282634571151)
        ·
          refine ⟨39357394267665423951856727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26238262845110282634571151 39357394267665423951856727)
          ·
            refine ⟨59036091401498135927785091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39357394267665423951856727 59036091401498135927785091)
            ·
              refine ⟨88554137102247203891677637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59036091401498135927785091 88554137102247203891677637)
              ·
                refine ⟨16603900706671350729689557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88554137102247203891677637 16603900706671350729689557)
                ·
                  refine ⟨389153922812609782727099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16603900706671350729689557 389153922812609782727099)
                  ·
                    rfl

theorem cell23_6820871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 7].length) (baseStart_6820871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820871 prefixEnd_6820871 := by exact prefixLift 6820871
  have htrace : WordTrace (prefixWord ++ tailWord_6820871) baseStart_6820871 baseEnd_6820871 := by
    simpa [prefixWord, tailWord_6820871, baseEnd_6820871] using wordTrace_append hprefix tailTrace_6820871
  have hstable : (prefixWord ++ tailWord_6820871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820871).length < 2 ^ (prefixWord ++ tailWord_6820871).sum := by decide
  have hdescent : baseEnd_6820871 < baseStart_6820871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820881 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 3]
def baseStart_6820881 : Nat := 118140960795 + 6820881 * 2 ^ 59
def prefixEnd_6820881 : Nat := 4983230072969 + 3 ^ 40 * 6820881 * 2
def baseEnd_6820881 : Nat := 3502390440120033005418845

theorem tailTrace_6820881 : CollatzResearch.WordTrace tailWord_6820881 prefixEnd_6820881 3502390440120033005418845 := by
  unfold tailWord_6820881
  simp only [CollatzResearch.WordTrace]
  refine ⟨248777968002120525576390497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165851978668080350384260331 248777968002120525576390497)
  ·
    refine ⟨186583476001590394182292873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248777968002120525576390497 186583476001590394182292873)
    ·
      refine ⟨139937607001192795636719655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186583476001590394182292873 139937607001192795636719655)
      ·
        refine ⟨209906410501789193455079483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139937607001192795636719655 209906410501789193455079483)
        ·
          refine ⟨314859615752683790182619225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209906410501789193455079483 314859615752683790182619225)
          ·
            refine ⟨236144711814512842636964419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314859615752683790182619225 236144711814512842636964419)
            ·
              refine ⟨354217067721769263955446629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236144711814512842636964419 354217067721769263955446629)
              ·
                refine ⟨66415700197831736991646243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354217067721769263955446629 66415700197831736991646243)
                ·
                  refine ⟨99623550296747605487469365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66415700197831736991646243 99623550296747605487469365)
                  ·
                    refine ⟨9339707840320088014450253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99623550296747605487469365 9339707840320088014450253)
                    ·
                      refine ⟨3502390440120033005418845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9339707840320088014450253 3502390440120033005418845)
                      ·
                        rfl

theorem cell23_6820881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_6820881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820881 prefixEnd_6820881 := by exact prefixLift 6820881
  have htrace : WordTrace (prefixWord ++ tailWord_6820881) baseStart_6820881 baseEnd_6820881 := by
    simpa [prefixWord, tailWord_6820881, baseEnd_6820881] using wordTrace_append hprefix tailTrace_6820881
  have hstable : (prefixWord ++ tailWord_6820881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820881).length < 2 ^ (prefixWord ++ tailWord_6820881).sum := by decide
  have hdescent : baseEnd_6820881 < baseStart_6820881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820908 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 2, 5, 2]
def baseStart_6820908 : Nat := 118140960795 + 6820908 * 2 ^ 59
def prefixEnd_6820908 : Nat := 4983230072969 + 3 ^ 40 * 6820908 * 2
def baseEnd_6820908 : Nat := 3502404304097704399781221

theorem tailTrace_6820908 : CollatzResearch.WordTrace tailWord_6820908 prefixEnd_6820908 3502404304097704399781221 := by
  unfold tailWord_6820908
  simp only [CollatzResearch.WordTrace]
  refine ⟨124389476386511354593811689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165852635182015139458415585 124389476386511354593811689)
  ·
    refine ⟨93292107289883515945358767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124389476386511354593811689 93292107289883515945358767)
    ·
      refine ⟨139938160934825273918038151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93292107289883515945358767 139938160934825273918038151)
      ·
        refine ⟨209907241402237910877057227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139938160934825273918038151 209907241402237910877057227)
        ·
          refine ⟨314860862103356866315585841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209907241402237910877057227 314860862103356866315585841)
          ·
            refine ⟨236145646577517649736689381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314860862103356866315585841 236145646577517649736689381)
            ·
              refine ⟨44277308733284559325629259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236145646577517649736689381 44277308733284559325629259)
              ·
                refine ⟨66415963099926838988443889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44277308733284559325629259 66415963099926838988443889)
                ·
                  refine ⟨49811972324945129241332917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66415963099926838988443889 49811972324945129241332917)
                  ·
                    refine ⟨4669872405463605866374961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49811972324945129241332917 4669872405463605866374961)
                    ·
                      refine ⟨3502404304097704399781221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669872405463605866374961 3502404304097704399781221)
                      ·
                        rfl

theorem cell23_6820908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 5, 2].length) (baseStart_6820908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820908 prefixEnd_6820908 := by exact prefixLift 6820908
  have htrace : WordTrace (prefixWord ++ tailWord_6820908) baseStart_6820908 baseEnd_6820908 := by
    simpa [prefixWord, tailWord_6820908, baseEnd_6820908] using wordTrace_append hprefix tailTrace_6820908
  have hstable : (prefixWord ++ tailWord_6820908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820908).length < 2 ^ (prefixWord ++ tailWord_6820908).sum := by decide
  have hdescent : baseEnd_6820908 < baseStart_6820908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820916 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_6820916 : Nat := 118140960795 + 6820916 * 2 ^ 59
def prefixEnd_6820916 : Nat := 4983230072969 + 3 ^ 40 * 6820916 * 2
def baseEnd_6820916 : Nat := 3502408411942940368481185

theorem tailTrace_6820916 : CollatzResearch.WordTrace tailWord_6820916 prefixEnd_6820916 3502408411942940368481185 := by
  unfold tailWord_6820916
  simp only [CollatzResearch.WordTrace]
  refine ⟨124389622278496863276957301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165852829704662484369276401 124389622278496863276957301)
  ·
    refine ⟨11661527088609080932214747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124389622278496863276957301 11661527088609080932214747)
    ·
      refine ⟨17492290632913621398322121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11661527088609080932214747 17492290632913621398322121)
      ·
        refine ⟨13119217974685216048741591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17492290632913621398322121 13119217974685216048741591)
        ·
          refine ⟨19678826962027824073112387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13119217974685216048741591 19678826962027824073112387)
          ·
            refine ⟨29518240443041736109668581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19678826962027824073112387 29518240443041736109668581)
            ·
              refine ⟨5534670083070325520562859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29518240443041736109668581 5534670083070325520562859)
              ·
                refine ⟨8302005124605488280844289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5534670083070325520562859 8302005124605488280844289)
                ·
                  refine ⟨6226503843454116210633217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8302005124605488280844289 6226503843454116210633217)
                  ·
                    refine ⟨4669877882590587157974913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6226503843454116210633217 4669877882590587157974913)
                    ·
                      refine ⟨3502408411942940368481185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669877882590587157974913 3502408411942940368481185)
                      ·
                        rfl

theorem cell23_6820916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_6820916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820916 prefixEnd_6820916 := by exact prefixLift 6820916
  have htrace : WordTrace (prefixWord ++ tailWord_6820916) baseStart_6820916 baseEnd_6820916 := by
    simpa [prefixWord, tailWord_6820916, baseEnd_6820916] using wordTrace_append hprefix tailTrace_6820916
  have hstable : (prefixWord ++ tailWord_6820916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820916).length < 2 ^ (prefixWord ++ tailWord_6820916).sum := by decide
  have hdescent : baseEnd_6820916 < baseStart_6820916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820938 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_6820938 : Nat := 118140960795 + 6820938 * 2 ^ 59
def prefixEnd_6820938 : Nat := 4983230072969 + 3 ^ 40 * 6820938 * 2
def baseEnd_6820938 : Nat := 3502419708517339282406083

theorem tailTrace_6820938 : CollatzResearch.WordTrace tailWord_6820938 prefixEnd_6820938 3502419708517339282406083 := by
  unfold tailWord_6820938
  simp only [CollatzResearch.WordTrace]
  refine ⟨62195011740728506077803867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165853364641942682874143645 62195011740728506077803867)
  ·
    refine ⟨93292517611092759116705801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62195011740728506077803867 93292517611092759116705801)
    ·
      refine ⟨69969388208319569337529351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93292517611092759116705801 69969388208319569337529351)
      ·
        refine ⟨104954082312479354006294027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69969388208319569337529351 104954082312479354006294027)
        ·
          refine ⟨157431123468719031009441041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104954082312479354006294027 157431123468719031009441041)
          ·
            refine ⟨118073342601539273257080781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157431123468719031009441041 118073342601539273257080781)
            ·
              refine ⟨44277503475577227471405293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118073342601539273257080781 44277503475577227471405293)
              ·
                refine ⟨16604063803341460301776985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44277503475577227471405293 16604063803341460301776985)
                ·
                  refine ⟨12453047852506095226332739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16604063803341460301776985 12453047852506095226332739)
                  ·
                    refine ⟨18679571778759142839499109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12453047852506095226332739 18679571778759142839499109)
                    ·
                      refine ⟨3502419708517339282406083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18679571778759142839499109 3502419708517339282406083)
                      ·
                        rfl

theorem cell23_6820938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_6820938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820938 prefixEnd_6820938 := by exact prefixLift 6820938
  have htrace : WordTrace (prefixWord ++ tailWord_6820938) baseStart_6820938 baseEnd_6820938 := by
    simpa [prefixWord, tailWord_6820938, baseEnd_6820938] using wordTrace_append hprefix tailTrace_6820938
  have hstable : (prefixWord ++ tailWord_6820938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820938).length < 2 ^ (prefixWord ++ tailWord_6820938).sum := by decide
  have hdescent : baseEnd_6820938 < baseStart_6820938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820951 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_6820951 : Nat := 118140960795 + 6820951 * 2 ^ 59
def prefixEnd_6820951 : Nat := 4983230072969 + 3 ^ 40 * 6820951 * 2
def baseEnd_6820951 : Nat := 3502426383765847731543523

theorem tailTrace_6820951 : CollatzResearch.WordTrace tailWord_6820951 prefixEnd_6820951 3502426383765847731543523 := by
  unfold tailWord_6820951
  simp only [CollatzResearch.WordTrace]
  refine ⟨248780521111866927531438707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165853680741244618354292471 248780521111866927531438707)
  ·
    refine ⟨373170781667800391297158061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248780521111866927531438707 373170781667800391297158061)
    ·
      refine ⟨139939043125425146736434273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373170781667800391297158061 139939043125425146736434273)
      ·
        refine ⟨104954282344068860052325705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139939043125425146736434273 104954282344068860052325705)
        ·
          refine ⟨78715711758051645039244279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104954282344068860052325705 78715711758051645039244279)
          ·
            refine ⟨118073567637077467558866419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78715711758051645039244279 118073567637077467558866419)
            ·
              refine ⟨177110351455616201338299629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118073567637077467558866419 177110351455616201338299629)
              ·
                refine ⟨66416381795856075501862361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177110351455616201338299629 66416381795856075501862361)
                ·
                  refine ⟨49812286346892056626396771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66416381795856075501862361 49812286346892056626396771)
                  ·
                    refine ⟨74718429520338084939595157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49812286346892056626396771 74718429520338084939595157)
                    ·
                      refine ⟨3502426383765847731543523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74718429520338084939595157 3502426383765847731543523)
                      ·
                        rfl

theorem cell23_6820951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_6820951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820951 prefixEnd_6820951 := by exact prefixLift 6820951
  have htrace : WordTrace (prefixWord ++ tailWord_6820951) baseStart_6820951 baseEnd_6820951 := by
    simpa [prefixWord, tailWord_6820951, baseEnd_6820951] using wordTrace_append hprefix tailTrace_6820951
  have hstable : (prefixWord ++ tailWord_6820951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820951).length < 2 ^ (prefixWord ++ tailWord_6820951).sum := by decide
  have hdescent : baseEnd_6820951 < baseStart_6820951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820961 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 8]
def baseStart_6820961 : Nat := 118140960795 + 6820961 * 2 ^ 59
def prefixEnd_6820961 : Nat := 4983230072969 + 3 ^ 40 * 6820961 * 2
def baseEnd_6820961 : Nat := 389159057619154743602053

theorem tailTrace_6820961 : CollatzResearch.WordTrace tailWord_6820961 prefixEnd_6820961 389159057619154743602053 := by
  unfold tailWord_6820961
  simp only [CollatzResearch.WordTrace]
  refine ⟨248780885841830699239302737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165853923894553799492868491 248780885841830699239302737)
  ·
    refine ⟨186585664381373024429477053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248780885841830699239302737 186585664381373024429477053)
    ·
      refine ⟨69969624143014884161053895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186585664381373024429477053 69969624143014884161053895)
      ·
        refine ⟨104954436214522326241580843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69969624143014884161053895 104954436214522326241580843)
        ·
          refine ⟨157431654321783489362371265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104954436214522326241580843 157431654321783489362371265)
          ·
            refine ⟨118073740741337617021778449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157431654321783489362371265 118073740741337617021778449)
            ·
              refine ⟨88555305556003212766333837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118073740741337617021778449 88555305556003212766333837)
              ·
                refine ⟨33208239583501204787375189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88555305556003212766333837 33208239583501204787375189)
                ·
                  refine ⟨389159057619154743602053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33208239583501204787375189 389159057619154743602053)
                  ·
                    rfl

theorem cell23_6820961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 8].length) (baseStart_6820961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820961 prefixEnd_6820961 := by exact prefixLift 6820961
  have htrace : WordTrace (prefixWord ++ tailWord_6820961) baseStart_6820961 baseEnd_6820961 := by
    simpa [prefixWord, tailWord_6820961, baseEnd_6820961] using wordTrace_append hprefix tailTrace_6820961
  have hstable : (prefixWord ++ tailWord_6820961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820961).length < 2 ^ (prefixWord ++ tailWord_6820961).sum := by decide
  have hdescent : baseEnd_6820961 < baseStart_6820961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820978 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 6]
def baseStart_6820978 : Nat := 118140960795 + 6820978 * 2 ^ 59
def prefixEnd_6820978 : Nat := 4983230072969 + 3 ^ 40 * 6820978 * 2
def baseEnd_6820978 : Nat := 389160027527057680656211

theorem tailTrace_6820978 : CollatzResearch.WordTrace tailWord_6820978 prefixEnd_6820978 389160027527057680656211 := by
  unfold tailWord_6820978
  simp only [CollatzResearch.WordTrace]
  refine ⟨62195376470692277785667897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165854337255179407428447725 62195376470692277785667897)
  ·
    refine ⟨46646532353019208339250923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62195376470692277785667897 46646532353019208339250923)
    ·
      refine ⟨69969798529528812508876385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46646532353019208339250923 69969798529528812508876385)
      ·
        refine ⟨52477348897146609381657289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69969798529528812508876385 52477348897146609381657289)
        ·
          refine ⟨39358011672859957036242967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52477348897146609381657289 39358011672859957036242967)
          ·
            refine ⟨59037017509289935554364451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39358011672859957036242967 59037017509289935554364451)
            ·
              refine ⟨88555526263934903331546677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59037017509289935554364451 88555526263934903331546677)
              ·
                refine ⟨8302080587243897187332501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88555526263934903331546677 8302080587243897187332501)
                ·
                  refine ⟨389160027527057680656211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8302080587243897187332501 389160027527057680656211)
                  ·
                    rfl

theorem cell23_6820978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_6820978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6820978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6820978 prefixEnd_6820978 := by exact prefixLift 6820978
  have htrace : WordTrace (prefixWord ++ tailWord_6820978) baseStart_6820978 baseEnd_6820978 := by
    simpa [prefixWord, tailWord_6820978, baseEnd_6820978] using wordTrace_append hprefix tailTrace_6820978
  have hstable : (prefixWord ++ tailWord_6820978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820978).length < 2 ^ (prefixWord ++ tailWord_6820978).sum := by decide
  have hdescent : baseEnd_6820978 < baseStart_6820978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821056 : List Nat := [2, 1, 1, 2, 6, 2, 1, 3, 1, 1, 3]
def baseStart_6821056 : Nat := 118140960795 + 6821056 * 2 ^ 59
def prefixEnd_6821056 : Nat := 4983230072969 + 3 ^ 40 * 6821056 * 2
def baseEnd_6821056 : Nat := 3502480299234569820730541

theorem tailTrace_6821056 : CollatzResearch.WordTrace tailWord_6821056 prefixEnd_6821056 3502480299234569820730541 := by
  unfold tailWord_6821056
  simp only [CollatzResearch.WordTrace]
  refine ⟨124392175388243265232005511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165856233850991020309340681 124392175388243265232005511)
  ·
    refine ⟨186588263082364897848008267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124392175388243265232005511 186588263082364897848008267)
    ·
      refine ⟨279882394623547346772012401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186588263082364897848008267 279882394623547346772012401)
      ·
        refine ⟨209911795967660510079009301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279882394623547346772012401 209911795967660510079009301)
        ·
          refine ⟨9839615435984086409953561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 209911795967660510079009301 9839615435984086409953561)
          ·
            refine ⟨7379711576988064807465171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9839615435984086409953561 7379711576988064807465171)
            ·
              refine ⟨11069567365482097211197757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379711576988064807465171 11069567365482097211197757)
              ·
                refine ⟨4151087762055786454199159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11069567365482097211197757 4151087762055786454199159)
                ·
                  refine ⟨6226631643083679681298739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151087762055786454199159 6226631643083679681298739)
                  ·
                    refine ⟨9339947464625519521948109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6226631643083679681298739 9339947464625519521948109)
                    ·
                      refine ⟨3502480299234569820730541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9339947464625519521948109 3502480299234569820730541)
                      ·
                        rfl

theorem cell23_6821056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 1, 1, 3].length) (baseStart_6821056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821056 prefixEnd_6821056 := by exact prefixLift 6821056
  have htrace : WordTrace (prefixWord ++ tailWord_6821056) baseStart_6821056 baseEnd_6821056 := by
    simpa [prefixWord, tailWord_6821056, baseEnd_6821056] using wordTrace_append hprefix tailTrace_6821056
  have hstable : (prefixWord ++ tailWord_6821056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821056).length < 2 ^ (prefixWord ++ tailWord_6821056).sum := by decide
  have hdescent : baseEnd_6821056 < baseStart_6821056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821079 : List Nat := [1, 1, 3, 2, 1, 2, 2, 6, 1, 2, 2]
def baseStart_6821079 : Nat := 118140960795 + 6821079 * 2 ^ 59
def prefixEnd_6821079 : Nat := 4983230072969 + 3 ^ 40 * 6821079 * 2
def baseEnd_6821079 : Nat := 3502492109289623230742935

theorem tailTrace_6821079 : CollatzResearch.WordTrace tailWord_6821079 prefixEnd_6821079 3502492109289623230742935 := by
  unfold tailWord_6821079
  simp only [CollatzResearch.WordTrace]
  refine ⟨248785189655403205392098291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165856793103602136928065527 248785189655403205392098291)
  ·
    refine ⟨373177784483104808088147437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248785189655403205392098291 373177784483104808088147437)
    ·
      refine ⟨139941669181164303033055289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373177784483104808088147437 139941669181164303033055289)
      ·
        refine ⟨104956251885873227274791467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139941669181164303033055289 104956251885873227274791467)
        ·
          refine ⟨157434377828809840912187201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104956251885873227274791467 157434377828809840912187201)
          ·
            refine ⟨118075783371607380684140401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157434377828809840912187201 118075783371607380684140401)
            ·
              refine ⟨88556837528705535513105301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118075783371607380684140401 88556837528705535513105301)
              ·
                refine ⟨4151101759158071977176811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88556837528705535513105301 4151101759158071977176811)
                ·
                  refine ⟨6226652638737107965765217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151101759158071977176811 6226652638737107965765217)
                  ·
                    refine ⟨4669989479052830974323913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6226652638737107965765217 4669989479052830974323913)
                    ·
                      refine ⟨3502492109289623230742935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4669989479052830974323913 3502492109289623230742935)
                      ·
                        rfl

theorem cell23_6821079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_6821079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821079 prefixEnd_6821079 := by exact prefixLift 6821079
  have htrace : WordTrace (prefixWord ++ tailWord_6821079) baseStart_6821079 baseEnd_6821079 := by
    simpa [prefixWord, tailWord_6821079, baseEnd_6821079] using wordTrace_append hprefix tailTrace_6821079
  have hstable : (prefixWord ++ tailWord_6821079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821079).length < 2 ^ (prefixWord ++ tailWord_6821079).sum := by decide
  have hdescent : baseEnd_6821079 < baseStart_6821079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821089 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 2, 4]
def baseStart_6821089 : Nat := 118140960795 + 6821089 * 2 ^ 59
def prefixEnd_6821089 : Nat := 4983230072969 + 3 ^ 40 * 6821089 * 2
def baseEnd_6821089 : Nat := 1167499081365389397205963

theorem tailTrace_6821089 : CollatzResearch.WordTrace tailWord_6821089 prefixEnd_6821089 1167499081365389397205963 := by
  unfold tailWord_6821089
  simp only [CollatzResearch.WordTrace]
  refine ⟨248785554385366977099962321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165857036256911318066641547 248785554385366977099962321)
  ·
    refine ⟨186589165789025232824971741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248785554385366977099962321 186589165789025232824971741)
    ·
      refine ⟨69970937170884462309364403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186589165789025232824971741 69970937170884462309364403)
      ·
        refine ⟨104956405756326693464046605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69970937170884462309364403 104956405756326693464046605)
        ·
          refine ⟨39358652158622510049017477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104956405756326693464046605 39358652158622510049017477)
          ·
            refine ⟨7379747279741720634190777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39358652158622510049017477 7379747279741720634190777)
            ·
              refine ⟨5534810459806290475643083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7379747279741720634190777 5534810459806290475643083)
              ·
                refine ⟨8302215689709435713464625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5534810459806290475643083 8302215689709435713464625)
                ·
                  refine ⟨6226661767282076785098469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8302215689709435713464625 6226661767282076785098469)
                  ·
                    refine ⟨1167499081365389397205963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6226661767282076785098469 1167499081365389397205963)
                    ·
                      rfl

theorem cell23_6821089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_6821089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821089 prefixEnd_6821089 := by exact prefixLift 6821089
  have htrace : WordTrace (prefixWord ++ tailWord_6821089) baseStart_6821089 baseEnd_6821089 := by
    simpa [prefixWord, tailWord_6821089, baseEnd_6821089] using wordTrace_append hprefix tailTrace_6821089
  have hstable : (prefixWord ++ tailWord_6821089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821089).length < 2 ^ (prefixWord ++ tailWord_6821089).sum := by decide
  have hdescent : baseEnd_6821089 < baseStart_6821089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821205 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_6821205 : Nat := 118140960795 + 6821205 * 2 ^ 59
def prefixEnd_6821205 : Nat := 4983230072969 + 3 ^ 40 * 6821205 * 2
def baseEnd_6821205 : Nat := 1167518935950696579255785

theorem tailTrace_6821205 : CollatzResearch.WordTrace tailWord_6821205 prefixEnd_6821205 1167518935950696579255785 := by
  unfold tailWord_6821205
  simp only [CollatzResearch.WordTrace]
  refine ⟨248789785252946728911185069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165859856835297819274123379 248789785252946728911185069)
  ·
    refine ⟨93296169469855023341694401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248789785252946728911185069 93296169469855023341694401)
    ·
      refine ⟨69972127102391267506270801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93296169469855023341694401 69972127102391267506270801)
      ·
        refine ⟨52479095326793450629703101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69972127102391267506270801 52479095326793450629703101)
        ·
          refine ⟨19679660747547543986138663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52479095326793450629703101 19679660747547543986138663)
          ·
            refine ⟨29519491121321315979207995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19679660747547543986138663 29519491121321315979207995)
            ·
              refine ⟨44279236681981973968811993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29519491121321315979207995 44279236681981973968811993)
              ·
                refine ⟨33209427511486480476608995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44279236681981973968811993 33209427511486480476608995)
                ·
                  refine ⟨49814141267229720714913493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33209427511486480476608995 49814141267229720714913493)
                  ·
                    refine ⟨1167518935950696579255785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49814141267229720714913493 1167518935950696579255785)
                    ·
                      rfl

theorem cell23_6821205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_6821205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821205 prefixEnd_6821205 := by exact prefixLift 6821205
  have htrace : WordTrace (prefixWord ++ tailWord_6821205) baseStart_6821205 baseEnd_6821205 := by
    simpa [prefixWord, tailWord_6821205, baseEnd_6821205] using wordTrace_append hprefix tailTrace_6821205
  have hstable : (prefixWord ++ tailWord_6821205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821205).length < 2 ^ (prefixWord ++ tailWord_6821205).sum := by decide
  have hdescent : baseEnd_6821205 < baseStart_6821205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821226 : List Nat := [3, 1, 3, 3, 2, 2, 1, 3, 5]
def baseStart_6821226 : Nat := 118140960795 + 6821226 * 2 ^ 59
def prefixEnd_6821226 : Nat := 4983230072969 + 3 ^ 40 * 6821226 * 2
def baseEnd_6821226 : Nat := 389174176771759350622751

theorem tailTrace_6821226 : CollatzResearch.WordTrace tailWord_6821226 prefixEnd_6821226 389174176771759350622751 := by
  unfold tailWord_6821226
  simp only [CollatzResearch.WordTrace]
  refine ⟨62197637796467662374424883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165860367457247099665133021 62197637796467662374424883)
  ·
    refine ⟨93296456694701493561637325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62197637796467662374424883 93296456694701493561637325)
    ·
      refine ⟨34986171260513060085613997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93296456694701493561637325 34986171260513060085613997)
      ·
        refine ⟨13119814222692397532105249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34986171260513060085613997 13119814222692397532105249)
        ·
          refine ⟨9839860667019298149078937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13119814222692397532105249 9839860667019298149078937)
          ·
            refine ⟨7379895500264473611809203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9839860667019298149078937 7379895500264473611809203)
            ·
              refine ⟨11069843250396710417713805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379895500264473611809203 11069843250396710417713805)
              ·
                refine ⟨4151191218898766406642677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11069843250396710417713805 4151191218898766406642677)
                ·
                  refine ⟨389174176771759350622751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4151191218898766406642677 389174176771759350622751)
                  ·
                    rfl

theorem cell23_6821226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_6821226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821226 prefixEnd_6821226 := by exact prefixLift 6821226
  have htrace : WordTrace (prefixWord ++ tailWord_6821226) baseStart_6821226 baseEnd_6821226 := by
    simpa [prefixWord, tailWord_6821226, baseEnd_6821226] using wordTrace_append hprefix tailTrace_6821226
  have hstable : (prefixWord ++ tailWord_6821226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821226).length < 2 ^ (prefixWord ++ tailWord_6821226).sum := by decide
  have hdescent : baseEnd_6821226 < baseStart_6821226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821265 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 6]
def baseStart_6821265 : Nat := 118140960795 + 6821265 * 2 ^ 59
def prefixEnd_6821265 : Nat := 4983230072969 + 3 ^ 40 * 6821265 * 2
def baseEnd_6821265 : Nat := 389176401854595500335231

theorem tailTrace_6821265 : CollatzResearch.WordTrace tailWord_6821265 prefixEnd_6821265 389176401854595500335231 := by
  unfold tailWord_6821265
  simp only [CollatzResearch.WordTrace]
  refine ⟨248791973632729359158369249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165861315755152906105579499 248791973632729359158369249)
  ·
    refine ⟨186593980224547019368776937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248791973632729359158369249 186593980224547019368776937)
    ·
      refine ⟨139945485168410264526582703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186593980224547019368776937 139945485168410264526582703)
      ·
        refine ⟨209918227752615396789874055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139945485168410264526582703 209918227752615396789874055)
        ·
          refine ⟨314877341628923095184811083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209918227752615396789874055 314877341628923095184811083)
          ·
            refine ⟨472316012443384642777216625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314877341628923095184811083 472316012443384642777216625)
            ·
              refine ⟨354237009332538482082912469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472316012443384642777216625 354237009332538482082912469)
              ·
                refine ⟨8302429906231370673818261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 354237009332538482082912469 8302429906231370673818261)
                ·
                  refine ⟨389176401854595500335231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8302429906231370673818261 389176401854595500335231)
                  ·
                    rfl

theorem cell23_6821265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 6].length) (baseStart_6821265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821265 prefixEnd_6821265 := by exact prefixLift 6821265
  have htrace : WordTrace (prefixWord ++ tailWord_6821265) baseStart_6821265 baseEnd_6821265 := by
    simpa [prefixWord, tailWord_6821265, baseEnd_6821265] using wordTrace_append hprefix tailTrace_6821265
  have hstable : (prefixWord ++ tailWord_6821265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821265).length < 2 ^ (prefixWord ++ tailWord_6821265).sum := by decide
  have hdescent : baseEnd_6821265 < baseStart_6821265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821276 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6821276 : Nat := 118140960795 + 6821276 * 2 ^ 59
def prefixEnd_6821276 : Nat := 4983230072969 + 3 ^ 40 * 6821276 * 2
def baseEnd_6821276 : Nat := 3502593264978558959979529

theorem tailTrace_6821276 : CollatzResearch.WordTrace tailWord_6821276 prefixEnd_6821276 3502593264978558959979529 := by
  unfold tailWord_6821276
  simp only [CollatzResearch.WordTrace]
  refine ⟨124396187417844754018509841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165861583223793005358013121 124396187417844754018509841)
  ·
    refine ⟨93297140563383565513882381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124396187417844754018509841 93297140563383565513882381)
    ·
      refine ⟨34986427711268837067705893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93297140563383565513882381 34986427711268837067705893)
      ·
        refine ⟨6559955195862906950194855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34986427711268837067705893 6559955195862906950194855)
        ·
          refine ⟨9839932793794360425292283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6559955195862906950194855 9839932793794360425292283)
          ·
            refine ⟨14759899190691540637938425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9839932793794360425292283 14759899190691540637938425)
            ·
              refine ⟨11069924393018655478453819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14759899190691540637938425 11069924393018655478453819)
              ·
                refine ⟨16604886589527983217680729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11069924393018655478453819 16604886589527983217680729)
                ·
                  refine ⟨12453664942145987413260547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16604886589527983217680729 12453664942145987413260547)
                  ·
                    refine ⟨18680497413218981119890821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12453664942145987413260547 18680497413218981119890821)
                    ·
                      refine ⟨3502593264978558959979529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18680497413218981119890821 3502593264978558959979529)
                      ·
                        rfl

theorem cell23_6821276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6821276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821276 prefixEnd_6821276 := by exact prefixLift 6821276
  have htrace : WordTrace (prefixWord ++ tailWord_6821276) baseStart_6821276 baseEnd_6821276 := by
    simpa [prefixWord, tailWord_6821276, baseEnd_6821276] using wordTrace_append hprefix tailTrace_6821276
  have hstable : (prefixWord ++ tailWord_6821276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821276).length < 2 ^ (prefixWord ++ tailWord_6821276).sum := by decide
  have hdescent : baseEnd_6821276 < baseStart_6821276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821279 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 3]
def baseStart_6821279 : Nat := 118140960795 + 6821279 * 2 ^ 59
def prefixEnd_6821279 : Nat := 4983230072969 + 3 ^ 40 * 6821279 * 2
def baseEnd_6821279 : Nat := 3502594805420522448242015

theorem tailTrace_6821279 : CollatzResearch.WordTrace tailWord_6821279 prefixEnd_6821279 3502594805420522448242015 := by
  unfold tailWord_6821279
  simp only [CollatzResearch.WordTrace]
  refine ⟨248792484254678639549378891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165861656169785759699585927 248792484254678639549378891)
  ·
    refine ⟨373188726382017959324068337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248792484254678639549378891 373188726382017959324068337)
    ·
      refine ⟨279891544786513469493051253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373188726382017959324068337 279891544786513469493051253)
      ·
        refine ⟨26239832323735637764973555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279891544786513469493051253 26239832323735637764973555)
        ·
          refine ⟨39359748485603456647460333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26239832323735637764973555 39359748485603456647460333)
          ·
            refine ⟨14759905682101296242797625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39359748485603456647460333 14759905682101296242797625)
            ·
              refine ⟨11069929261575972182098219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14759905682101296242797625 11069929261575972182098219)
              ·
                refine ⟨16604893892363958273147329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11069929261575972182098219 16604893892363958273147329)
                ·
                  refine ⟨12453670419272968704860497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16604893892363958273147329 12453670419272968704860497)
                  ·
                    refine ⟨9340252814454726528645373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12453670419272968704860497 9340252814454726528645373)
                    ·
                      refine ⟨3502594805420522448242015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9340252814454726528645373 3502594805420522448242015)
                      ·
                        rfl

theorem cell23_6821279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_6821279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821279 prefixEnd_6821279 := by exact prefixLift 6821279
  have htrace : WordTrace (prefixWord ++ tailWord_6821279) baseStart_6821279 baseEnd_6821279 := by
    simpa [prefixWord, tailWord_6821279, baseEnd_6821279] using wordTrace_append hprefix tailTrace_6821279
  have hstable : (prefixWord ++ tailWord_6821279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821279).length < 2 ^ (prefixWord ++ tailWord_6821279).sum := by decide
  have hdescent : baseEnd_6821279 < baseStart_6821279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821309 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_6821309 : Nat := 118140960795 + 6821309 * 2 ^ 59
def prefixEnd_6821309 : Nat := 4983230072969 + 3 ^ 40 * 6821309 * 2
def baseEnd_6821309 : Nat := 3502610209840157330866877

theorem tailTrace_6821309 : CollatzResearch.WordTrace tailWord_6821309 prefixEnd_6821309 3502610209840157330866877 := by
  unfold tailWord_6821309
  simp only [CollatzResearch.WordTrace]
  refine ⟨248793578444569954672970981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165862385629713303115313987 248793578444569954672970981)
  ·
    refine ⟨46648795958356866501182059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248793578444569954672970981 46648795958356866501182059)
    ·
      refine ⟨69973193937535299751773089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46648795958356866501182059 69973193937535299751773089)
      ·
        refine ⟨52479895453151474813829817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69973193937535299751773089 52479895453151474813829817)
        ·
          refine ⟨39359921589863606110372363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52479895453151474813829817 39359921589863606110372363)
          ·
            refine ⟨59039882384795409165558545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39359921589863606110372363 59039882384795409165558545)
            ·
              refine ⟨44279911788596556874168909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59039882384795409165558545 44279911788596556874168909)
              ·
                refine ⟨16604966920723708827813341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44279911788596556874168909 16604966920723708827813341)
                ·
                  refine ⟨6226862595271390810430003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16604966920723708827813341 6226862595271390810430003)
                  ·
                    refine ⟨9340293892907086215645005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6226862595271390810430003 9340293892907086215645005)
                    ·
                      refine ⟨3502610209840157330866877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9340293892907086215645005 3502610209840157330866877)
                      ·
                        rfl

theorem cell23_6821309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_6821309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821309 prefixEnd_6821309 := by exact prefixLift 6821309
  have htrace : WordTrace (prefixWord ++ tailWord_6821309) baseStart_6821309 baseEnd_6821309 := by
    simpa [prefixWord, tailWord_6821309, baseEnd_6821309] using wordTrace_append hprefix tailTrace_6821309
  have hstable : (prefixWord ++ tailWord_6821309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821309).length < 2 ^ (prefixWord ++ tailWord_6821309).sum := by decide
  have hdescent : baseEnd_6821309 < baseStart_6821309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821352 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6821352 : Nat := 118140960795 + 6821352 * 2 ^ 59
def prefixEnd_6821352 : Nat := 4983230072969 + 3 ^ 40 * 6821352 * 2
def baseEnd_6821352 : Nat := 3502632289508300662629179

theorem tailTrace_6821352 : CollatzResearch.WordTrace tailWord_6821352 prefixEnd_6821352 3502632289508300662629179 := by
  unfold tailWord_6821352
  simp only [CollatzResearch.WordTrace]
  refine ⟨124397573391707086508393155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165863431188942782011190873 124397573391707086508393155)
  ·
    refine ⟨186596360087560629762589733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124397573391707086508393155 186596360087560629762589733)
    ·
      refine ⟨34986817516417618080485575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186596360087560629762589733 34986817516417618080485575)
      ·
        refine ⟨52480226274626427120728363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34986817516417618080485575 52480226274626427120728363)
        ·
          refine ⟨78720339411939640681092545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52480226274626427120728363 78720339411939640681092545)
          ·
            refine ⟨59040254558954730510819409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78720339411939640681092545 59040254558954730510819409)
            ·
              refine ⟨44280190919216047883114557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59040254558954730510819409 44280190919216047883114557)
              ·
                refine ⟨16605071594706017956167959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44280190919216047883114557 16605071594706017956167959)
                ·
                  refine ⟨24907607392059026934251939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16605071594706017956167959 24907607392059026934251939)
                  ·
                    refine ⟨37361411088088540401377909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24907607392059026934251939 37361411088088540401377909)
                    ·
                      refine ⟨3502632289508300662629179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37361411088088540401377909 3502632289508300662629179)
                      ·
                        rfl

theorem cell23_6821352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6821352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821352 prefixEnd_6821352 := by exact prefixLift 6821352
  have htrace : WordTrace (prefixWord ++ tailWord_6821352) baseStart_6821352 baseEnd_6821352 := by
    simpa [prefixWord, tailWord_6821352, baseEnd_6821352] using wordTrace_append hprefix tailTrace_6821352
  have hstable : (prefixWord ++ tailWord_6821352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821352).length < 2 ^ (prefixWord ++ tailWord_6821352).sum := by decide
  have hdescent : baseEnd_6821352 < baseStart_6821352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821359 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 2, 4]
def baseStart_6821359 : Nat := 118140960795 + 6821359 * 2 ^ 59
def prefixEnd_6821359 : Nat := 4983230072969 + 3 ^ 40 * 6821359 * 2
def baseEnd_6821359 : Nat := 1167545294624294045080549

theorem tailTrace_6821359 : CollatzResearch.WordTrace tailWord_6821359 prefixEnd_6821359 1167545294624294045080549 := by
  unfold tailWord_6821359
  simp only [CollatzResearch.WordTrace]
  refine ⟨248795402094388813212291131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165863601396259208808194087 248795402094388813212291131)
  ·
    refine ⟨373193103141583219818436697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248795402094388813212291131 373193103141583219818436697)
    ·
      refine ⟨279894827356187414863827523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373193103141583219818436697 279894827356187414863827523)
      ·
        refine ⟨419842241034281122295741285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279894827356187414863827523 419842241034281122295741285)
        ·
          refine ⟨78720420193927710430451491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 419842241034281122295741285 78720420193927710430451491)
          ·
            refine ⟨118080630290891565645677237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78720420193927710430451491 118080630290891565645677237)
            ·
              refine ⟨11070059089771084279282241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118080630290891565645677237 11070059089771084279282241)
              ·
                refine ⟨8302544317328313209461681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11070059089771084279282241 8302544317328313209461681)
                ·
                  refine ⟨6226908237996234907096261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8302544317328313209461681 6226908237996234907096261)
                  ·
                    refine ⟨1167545294624294045080549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6226908237996234907096261 1167545294624294045080549)
                    ·
                      rfl

theorem cell23_6821359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 4].length) (baseStart_6821359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821359 prefixEnd_6821359 := by exact prefixLift 6821359
  have htrace : WordTrace (prefixWord ++ tailWord_6821359) baseStart_6821359 baseEnd_6821359 := by
    simpa [prefixWord, tailWord_6821359, baseEnd_6821359] using wordTrace_append hprefix tailTrace_6821359
  have hstable : (prefixWord ++ tailWord_6821359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821359).length < 2 ^ (prefixWord ++ tailWord_6821359).sum := by decide
  have hdescent : baseEnd_6821359 < baseStart_6821359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821375 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_6821375 : Nat := 118140960795 + 6821375 * 2 ^ 59
def prefixEnd_6821375 : Nat := 4983230072969 + 3 ^ 40 * 6821375 * 2
def baseEnd_6821375 : Nat := 3502644099563354072641573

theorem tailTrace_6821375 : CollatzResearch.WordTrace tailWord_6821375 prefixEnd_6821375 3502644099563354072641573 := by
  unfold tailWord_6821375
  simp only [CollatzResearch.WordTrace]
  refine ⟨248795985662330847944873579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165863990441553898629915719 248795985662330847944873579)
  ·
    refine ⟨373193978493496271917310369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248795985662330847944873579 373193978493496271917310369)
    ·
      refine ⟨279895483870122203937982777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373193978493496271917310369 279895483870122203937982777)
      ·
        refine ⟨209921612902591652953487083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279895483870122203937982777 209921612902591652953487083)
        ·
          refine ⟨314882419353887479430230625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209921612902591652953487083 314882419353887479430230625)
          ·
            refine ⟨236161814515415609572672969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314882419353887479430230625 236161814515415609572672969)
            ·
              refine ⟨177121360886561707179504727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236161814515415609572672969 177121360886561707179504727)
              ·
                refine ⟨265682041329842560769257091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177121360886561707179504727 265682041329842560769257091)
                ·
                  refine ⟨398523061994763841153885637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265682041329842560769257091 398523061994763841153885637)
                  ·
                    refine ⟨74723074124018220216353557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 398523061994763841153885637 74723074124018220216353557)
                    ·
                      refine ⟨3502644099563354072641573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74723074124018220216353557 3502644099563354072641573)
                      ·
                        rfl

theorem cell23_6821375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_6821375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821375 prefixEnd_6821375 := by exact prefixLift 6821375
  have htrace : WordTrace (prefixWord ++ tailWord_6821375) baseStart_6821375 baseEnd_6821375 := by
    simpa [prefixWord, tailWord_6821375, baseEnd_6821375] using wordTrace_append hprefix tailTrace_6821375
  have hstable : (prefixWord ++ tailWord_6821375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821375).length < 2 ^ (prefixWord ++ tailWord_6821375).sum := by decide
  have hdescent : baseEnd_6821375 < baseStart_6821375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821386 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_6821386 : Nat := 118140960795 + 6821386 * 2 ^ 59
def prefixEnd_6821386 : Nat := 4983230072969 + 3 ^ 40 * 6821386 * 2
def baseEnd_6821386 : Nat := 3502649747850553529604023

theorem tailTrace_6821386 : CollatzResearch.WordTrace tailWord_6821386 prefixEnd_6821386 3502649747850553529604023 := by
  unfold tailWord_6821386
  simp only [CollatzResearch.WordTrace]
  refine ⟨62199096716322749205881003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165864257910193997882349341 62199096716322749205881003)
  ·
    refine ⟨93298645074484123808821505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62199096716322749205881003 93298645074484123808821505)
    ·
      refine ⟨69973983805863092856616129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93298645074484123808821505 69973983805863092856616129)
      ·
        refine ⟨52480487854397319642462097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69973983805863092856616129 52480487854397319642462097)
        ·
          refine ⟨39360365890797989731846573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52480487854397319642462097 39360365890797989731846573)
          ·
            refine ⟨14760137209049246149442465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39360365890797989731846573 14760137209049246149442465)
            ·
              refine ⟨11070102906786934612081849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14760137209049246149442465 11070102906786934612081849)
              ·
                refine ⟨8302577180090200959061387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11070102906786934612081849 8302577180090200959061387)
                ·
                  refine ⟨12453865770135301438592081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8302577180090200959061387 12453865770135301438592081)
                  ·
                    refine ⟨9340399327601476078944061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12453865770135301438592081 9340399327601476078944061)
                    ·
                      refine ⟨3502649747850553529604023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9340399327601476078944061 3502649747850553529604023)
                      ·
                        rfl

theorem cell23_6821386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_6821386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821386 prefixEnd_6821386 := by exact prefixLift 6821386
  have htrace : WordTrace (prefixWord ++ tailWord_6821386) baseStart_6821386 baseEnd_6821386 := by
    simpa [prefixWord, tailWord_6821386, baseEnd_6821386] using wordTrace_append hprefix tailTrace_6821386
  have hstable : (prefixWord ++ tailWord_6821386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821386).length < 2 ^ (prefixWord ++ tailWord_6821386).sum := by decide
  have hdescent : baseEnd_6821386 < baseStart_6821386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821433 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 2, 1, 3]
def baseStart_6821433 : Nat := 118140960795 + 6821433 * 2 ^ 59
def prefixEnd_6821433 : Nat := 4983230072969 + 3 ^ 40 * 6821433 * 2
def baseEnd_6821433 : Nat := 3502673881441314845716307

theorem tailTrace_6821433 : CollatzResearch.WordTrace tailWord_6821433 prefixEnd_6821433 3502673881441314845716307 := by
  unfold tailWord_6821433
  simp only [CollatzResearch.WordTrace]
  refine ⟨248798101096120723850484953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165865400730747149233656635 248798101096120723850484953)
  ·
    refine ⟨186598575822090542887863715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248798101096120723850484953 186598575822090542887863715)
    ·
      refine ⟨279897863733135814331795573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186598575822090542887863715 279897863733135814331795573)
      ·
        refine ⟨26240424724981482593605835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279897863733135814331795573 26240424724981482593605835)
        ·
          refine ⟨39360637087472223890408753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26240424724981482593605835 39360637087472223890408753)
          ·
            refine ⟨29520477815604167917806565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39360637087472223890408753 29520477815604167917806565)
            ·
              refine ⟨5535089590425781484588731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29520477815604167917806565 5535089590425781484588731)
              ·
                refine ⟨8302634385638672226883097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535089590425781484588731 8302634385638672226883097)
                ·
                  refine ⟨6226975789229004170162323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8302634385638672226883097 6226975789229004170162323)
                  ·
                    refine ⟨9340463683843506255243485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6226975789229004170162323 9340463683843506255243485)
                    ·
                      refine ⟨3502673881441314845716307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9340463683843506255243485 3502673881441314845716307)
                      ·
                        rfl

theorem cell23_6821433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_6821433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821433 prefixEnd_6821433 := by exact prefixLift 6821433
  have htrace : WordTrace (prefixWord ++ tailWord_6821433) baseStart_6821433 baseEnd_6821433 := by
    simpa [prefixWord, tailWord_6821433, baseEnd_6821433] using wordTrace_append hprefix tailTrace_6821433
  have hstable : (prefixWord ++ tailWord_6821433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821433).length < 2 ^ (prefixWord ++ tailWord_6821433).sum := by decide
  have hdescent : baseEnd_6821433 < baseStart_6821433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821473 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 2, 2, 2]
def baseStart_6821473 : Nat := 118140960795 + 6821473 * 2 ^ 59
def prefixEnd_6821473 : Nat := 4983230072969 + 3 ^ 40 * 6821473 * 2
def baseEnd_6821473 : Nat := 3502694420667494689216123

theorem tailTrace_6821473 : CollatzResearch.WordTrace tailWord_6821473 prefixEnd_6821473 3502694420667494689216123 := by
  unfold tailWord_6821473
  simp only [CollatzResearch.WordTrace]
  refine ⟨248799560015975810681941073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165866373343983873787960715 248799560015975810681941073)
  ·
    refine ⟨186599670011981858011455805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248799560015975810681941073 186599670011981858011455805)
    ·
      refine ⟨69974876254493196754295927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186599670011981858011455805 69974876254493196754295927)
      ·
        refine ⟨104962314381739795131443891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69974876254493196754295927 104962314381739795131443891)
        ·
          refine ⟨157443471572609692697165837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104962314381739795131443891 157443471572609692697165837)
          ·
            refine ⟨59041301839728634761437189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157443471572609692697165837 59041301839728634761437189)
            ·
              refine ⟨11070244094949119017769473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59041301839728634761437189 11070244094949119017769473)
              ·
                refine ⟨8302683071211839263327105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11070244094949119017769473 8302683071211839263327105)
                ·
                  refine ⟨6227012303408879447495329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8302683071211839263327105 6227012303408879447495329)
                  ·
                    refine ⟨4670259227556659585621497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6227012303408879447495329 4670259227556659585621497)
                    ·
                      refine ⟨3502694420667494689216123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4670259227556659585621497 3502694420667494689216123)
                      ·
                        rfl

theorem cell23_6821473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_6821473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821473 prefixEnd_6821473 := by exact prefixLift 6821473
  have htrace : WordTrace (prefixWord ++ tailWord_6821473) baseStart_6821473 baseEnd_6821473 := by
    simpa [prefixWord, tailWord_6821473, baseEnd_6821473] using wordTrace_append hprefix tailTrace_6821473
  have hstable : (prefixWord ++ tailWord_6821473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821473).length < 2 ^ (prefixWord ++ tailWord_6821473).sum := by decide
  have hdescent : baseEnd_6821473 < baseStart_6821473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821486 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_6821486 : Nat := 118140960795 + 6821486 * 2 ^ 59
def prefixEnd_6821486 : Nat := 4983230072969 + 3 ^ 40 * 6821486 * 2
def baseEnd_6821486 : Nat := 3502701095916003138353563

theorem tailTrace_6821486 : CollatzResearch.WordTrace tailWord_6821486 prefixEnd_6821486 3502701095916003138353563 := by
  unfold tailWord_6821486
  simp only [CollatzResearch.WordTrace]
  refine ⟨31100004270616089237770539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165866689443285809268109541 31100004270616089237770539)
  ·
    refine ⟨46650006405924133856655809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31100004270616089237770539 46650006405924133856655809)
    ·
      refine ⟨34987504804443100392491857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46650006405924133856655809 34987504804443100392491857)
      ·
        refine ⟨26240628603332325294368893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34987504804443100392491857 26240628603332325294368893)
        ·
          refine ⟨9840235726249621985388335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26240628603332325294368893 9840235726249621985388335)
          ·
            refine ⟨14760353589374432978082503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9840235726249621985388335 14760353589374432978082503)
            ·
              refine ⟨22140530384061649467123755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14760353589374432978082503 22140530384061649467123755)
              ·
                refine ⟨33210795576092474200685633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22140530384061649467123755 33210795576092474200685633)
                ·
                  refine ⟨24908096682069355650514225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33210795576092474200685633 24908096682069355650514225)
                  ·
                    refine ⟨18681072511552016737885669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24908096682069355650514225 18681072511552016737885669)
                    ·
                      refine ⟨3502701095916003138353563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18681072511552016737885669 3502701095916003138353563)
                      ·
                        rfl

theorem cell23_6821486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_6821486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821486 prefixEnd_6821486 := by exact prefixLift 6821486
  have htrace : WordTrace (prefixWord ++ tailWord_6821486) baseStart_6821486 baseEnd_6821486 := by
    simpa [prefixWord, tailWord_6821486, baseEnd_6821486] using wordTrace_append hprefix tailTrace_6821486
  have hstable : (prefixWord ++ tailWord_6821486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821486).length < 2 ^ (prefixWord ++ tailWord_6821486).sum := by decide
  have hdescent : baseEnd_6821486 < baseStart_6821486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821499 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 2, 5, 2]
def baseStart_6821499 : Nat := 118140960795 + 6821499 * 2 ^ 59
def prefixEnd_6821499 : Nat := 4983230072969 + 3 ^ 40 * 6821499 * 2
def baseEnd_6821499 : Nat := 3502707771164511587491003

theorem tailTrace_6821499 : CollatzResearch.WordTrace tailWord_6821499 prefixEnd_6821499 3502707771164511587491003 := by
  unfold tailWord_6821499
  simp only [CollatzResearch.WordTrace]
  refine ⟨248800508313881617122387551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165867005542587744748258367 248800508313881617122387551)
  ·
    refine ⟨373200762470822425683581327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248800508313881617122387551 373200762470822425683581327)
    ·
      refine ⟨559801143706233638525371991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373200762470822425683581327 559801143706233638525371991)
      ·
        refine ⟨839701715559350457788057987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559801143706233638525371991 839701715559350457788057987)
        ·
          refine ⟨1259552573339025686682086981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839701715559350457788057987 1259552573339025686682086981)
          ·
            refine ⟨236166107501067316252891309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1259552573339025686682086981 236166107501067316252891309)
            ·
              refine ⟨88562290312900243594834241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236166107501067316252891309 88562290312900243594834241)
              ·
                refine ⟨66421717734675182696125681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88562290312900243594834241 66421717734675182696125681)
                ·
                  refine ⟨49816288301006387022094261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66421717734675182696125681 49816288301006387022094261)
                  ·
                    refine ⟨4670277028219348783321337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49816288301006387022094261 4670277028219348783321337)
                    ·
                      refine ⟨3502707771164511587491003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4670277028219348783321337 3502707771164511587491003)
                      ·
                        rfl

theorem cell23_6821499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 5, 2].length) (baseStart_6821499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821499 prefixEnd_6821499 := by exact prefixLift 6821499
  have htrace : WordTrace (prefixWord ++ tailWord_6821499) baseStart_6821499 baseEnd_6821499 := by
    simpa [prefixWord, tailWord_6821499, baseEnd_6821499] using wordTrace_append hprefix tailTrace_6821499
  have hstable : (prefixWord ++ tailWord_6821499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821499).length < 2 ^ (prefixWord ++ tailWord_6821499).sum := by decide
  have hdescent : baseEnd_6821499 < baseStart_6821499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821524 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_6821524 : Nat := 118140960795 + 6821524 * 2 ^ 59
def prefixEnd_6821524 : Nat := 4983230072969 + 3 ^ 40 * 6821524 * 2
def baseEnd_6821524 : Nat := 3502720608180873989678389

theorem tailTrace_6821524 : CollatzResearch.WordTrace tailWord_6821524 prefixEnd_6821524 3502720608180873989678389 := by
  unfold tailWord_6821524
  simp only [CollatzResearch.WordTrace]
  refine ⟨124400710069395523196023813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165867613425860697594698417 124400710069395523196023813)
  ·
    refine ⟨23325133138011660599254465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124400710069395523196023813 23325133138011660599254465)
    ·
      refine ⟨17493849853508745449440849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23325133138011660599254465 17493849853508745449440849)
      ·
        refine ⟨13120387390131559087080637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17493849853508745449440849 13120387390131559087080637)
        ·
          refine ⟨4920145271299334657655239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13120387390131559087080637 4920145271299334657655239)
          ·
            refine ⟨7380217906949001986482859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920145271299334657655239 7380217906949001986482859)
            ·
              refine ⟨11070326860423502979724289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7380217906949001986482859 11070326860423502979724289)
              ·
                refine ⟨8302745145317627234793217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11070326860423502979724289 8302745145317627234793217)
                ·
                  refine ⟨6227058858988220426094913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8302745145317627234793217 6227058858988220426094913)
                  ·
                    refine ⟨4670294144241165319571185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6227058858988220426094913 4670294144241165319571185)
                    ·
                      refine ⟨3502720608180873989678389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4670294144241165319571185 3502720608180873989678389)
                      ·
                        rfl

theorem cell23_6821524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_6821524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821524 prefixEnd_6821524 := by exact prefixLift 6821524
  have htrace : WordTrace (prefixWord ++ tailWord_6821524) baseStart_6821524 baseEnd_6821524 := by
    simpa [prefixWord, tailWord_6821524, baseEnd_6821524] using wordTrace_append hprefix tailTrace_6821524
  have hstable : (prefixWord ++ tailWord_6821524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821524).length < 2 ^ (prefixWord ++ tailWord_6821524).sum := by decide
  have hdescent : baseEnd_6821524 < baseStart_6821524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821566 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_6821566 : Nat := 118140960795 + 6821566 * 2 ^ 59
def prefixEnd_6821566 : Nat := 4983230072969 + 3 ^ 40 * 6821566 * 2
def baseEnd_6821566 : Nat := 3502742174368362825353195

theorem tailTrace_6821566 : CollatzResearch.WordTrace tailWord_6821566 prefixEnd_6821566 3502742174368362825353195 := by
  unfold tailWord_6821566
  simp only [CollatzResearch.WordTrace]
  refine ⟨31100369000579860945634569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165868634669759258376717701 31100369000579860945634569)
  ·
    refine ⟨23325276750434895709225927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31100369000579860945634569 23325276750434895709225927)
    ·
      refine ⟨34987915125652343563838891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23325276750434895709225927 34987915125652343563838891)
      ·
        refine ⟨52481872688478515345758337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34987915125652343563838891 52481872688478515345758337)
        ·
          refine ⟨39361404516358886509318753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52481872688478515345758337 39361404516358886509318753)
          ·
            refine ⟨29521053387269164881989065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39361404516358886509318753 29521053387269164881989065)
            ·
              refine ⟨22140790040451873661491799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29521053387269164881989065 22140790040451873661491799)
              ·
                refine ⟨33211185060677810492237699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22140790040451873661491799 33211185060677810492237699)
                ·
                  refine ⟨49816777591016715738356549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33211185060677810492237699 49816777591016715738356549)
                  ·
                    refine ⟨9340645798315634200941853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49816777591016715738356549 9340645798315634200941853)
                    ·
                      refine ⟨3502742174368362825353195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9340645798315634200941853 3502742174368362825353195)
                      ·
                        rfl

theorem cell23_6821566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_6821566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821566 prefixEnd_6821566 := by exact prefixLift 6821566
  have htrace : WordTrace (prefixWord ++ tailWord_6821566) baseStart_6821566 baseEnd_6821566 := by
    simpa [prefixWord, tailWord_6821566, baseEnd_6821566] using wordTrace_append hprefix tailTrace_6821566
  have hstable : (prefixWord ++ tailWord_6821566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821566).length < 2 ^ (prefixWord ++ tailWord_6821566).sum := by decide
  have hdescent : baseEnd_6821566 < baseStart_6821566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821599 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 3, 5]
def baseStart_6821599 : Nat := 118140960795 + 6821599 * 2 ^ 59
def prefixEnd_6821599 : Nat := 4983230072969 + 3 ^ 40 * 6821599 * 2
def baseEnd_6821599 : Nat := 1167586373076653732080181

theorem tailTrace_6821599 : CollatzResearch.WordTrace tailWord_6821599 prefixEnd_6821599 1167586373076653732080181 := by
  unfold tailWord_6821599
  simp only [CollatzResearch.WordTrace]
  refine ⟨248804155613519334201027851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165869437075679556134018567 248804155613519334201027851)
  ·
    refine ⟨373206233420279001301541777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248804155613519334201027851 373206233420279001301541777)
    ·
      refine ⟨279904675065209250976156333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373206233420279001301541777 279904675065209250976156333)
      ·
        refine ⟨104964253149453469116058625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279904675065209250976156333 104964253149453469116058625)
        ·
          refine ⟨78723189862090101837043969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104964253149453469116058625 78723189862090101837043969)
          ·
            refine ⟨59042392396567576377782977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78723189862090101837043969 59042392396567576377782977)
            ·
              refine ⟨44281794297425682283337233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59042392396567576377782977 44281794297425682283337233)
              ·
                refine ⟨33211345723069261712502925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44281794297425682283337233 33211345723069261712502925)
                ·
                  refine ⟨12454254646150973142188597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33211345723069261712502925 12454254646150973142188597)
                  ·
                    refine ⟨1167586373076653732080181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12454254646150973142188597 1167586373076653732080181)
                    ·
                      rfl

theorem cell23_6821599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_6821599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821599 prefixEnd_6821599 := by exact prefixLift 6821599
  have htrace : WordTrace (prefixWord ++ tailWord_6821599) baseStart_6821599 baseEnd_6821599 := by
    simpa [prefixWord, tailWord_6821599, baseEnd_6821599] using wordTrace_append hprefix tailTrace_6821599
  have hstable : (prefixWord ++ tailWord_6821599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821599).length < 2 ^ (prefixWord ++ tailWord_6821599).sum := by decide
  have hdescent : baseEnd_6821599 < baseStart_6821599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821646 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_6821646 : Nat := 118140960795 + 6821646 * 2 ^ 59
def prefixEnd_6821646 : Nat := 4983230072969 + 3 ^ 40 * 6821646 * 2
def baseEnd_6821646 : Nat := 1167594417606907504117609

theorem tailTrace_6821646 : CollatzResearch.WordTrace tailWord_6821646 prefixEnd_6821646 1167594417606907504117609 := by
  unfold tailWord_6821646
  simp only [CollatzResearch.WordTrace]
  refine ⟨31100733730543632653498599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165870579896232707485325861 31100733730543632653498599)
  ·
    refine ⟨46651100595815448980247899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31100733730543632653498599 46651100595815448980247899)
    ·
      refine ⟨69976650893723173470371849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46651100595815448980247899 69976650893723173470371849)
      ·
        refine ⟨52482488170292380102778887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69976650893723173470371849 52482488170292380102778887)
        ·
          refine ⟨78723732255438570154168331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52482488170292380102778887 78723732255438570154168331)
          ·
            refine ⟨118085598383157855231252497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78723732255438570154168331 118085598383157855231252497)
            ·
              refine ⟨88564198787368391423439373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118085598383157855231252497 88564198787368391423439373)
              ·
                refine ⟨33211574545263146783789765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88564198787368391423439373 33211574545263146783789765)
                ·
                  refine ⟨6227170227236840021960581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33211574545263146783789765 6227170227236840021960581)
                  ·
                    refine ⟨1167594417606907504117609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6227170227236840021960581 1167594417606907504117609)
                    ·
                      rfl

theorem cell23_6821646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_6821646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821646 prefixEnd_6821646 := by exact prefixLift 6821646
  have htrace : WordTrace (prefixWord ++ tailWord_6821646) baseStart_6821646 baseEnd_6821646 := by
    simpa [prefixWord, tailWord_6821646, baseEnd_6821646] using wordTrace_append hprefix tailTrace_6821646
  have hstable : (prefixWord ++ tailWord_6821646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821646).length < 2 ^ (prefixWord ++ tailWord_6821646).sum := by decide
  have hdescent : baseEnd_6821646 < baseStart_6821646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821649 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_6821649 : Nat := 118140960795 + 6821649 * 2 ^ 59
def prefixEnd_6821649 : Nat := 4983230072969 + 3 ^ 40 * 6821649 * 2
def baseEnd_6821649 : Nat := 3502784793262686000615313

theorem tailTrace_6821649 : CollatzResearch.WordTrace tailWord_6821649 prefixEnd_6821649 3502784793262686000615313 := by
  unfold tailWord_6821649
  simp only [CollatzResearch.WordTrace]
  refine ⟨248805979263338192740348001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165870652842225461826898667 248805979263338192740348001)
  ·
    refine ⟨186604484447503644555261001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248805979263338192740348001 186604484447503644555261001)
    ·
      refine ⟨139953363335627733416445751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186604484447503644555261001 139953363335627733416445751)
      ·
        refine ⟨209930045003441600124668627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139953363335627733416445751 209930045003441600124668627)
        ·
          refine ⟨314895067505162400187002941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209930045003441600124668627 314895067505162400187002941)
          ·
            refine ⟨118085650314435900070126103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314895067505162400187002941 118085650314435900070126103)
            ·
              refine ⟨177128475471653850105189155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118085650314435900070126103 177128475471653850105189155)
              ·
                refine ⟨265692713207480775157783733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177128475471653850105189155 265692713207480775157783733)
                ·
                  refine ⟨24908691863201322671042225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 265692713207480775157783733 24908691863201322671042225)
                  ·
                    refine ⟨18681518897400992003281669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24908691863201322671042225 18681518897400992003281669)
                    ·
                      refine ⟨3502784793262686000615313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18681518897400992003281669 3502784793262686000615313)
                      ·
                        rfl

theorem cell23_6821649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_6821649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821649 prefixEnd_6821649 := by exact prefixLift 6821649
  have htrace : WordTrace (prefixWord ++ tailWord_6821649) baseStart_6821649 baseEnd_6821649 := by
    simpa [prefixWord, tailWord_6821649, baseEnd_6821649] using wordTrace_append hprefix tailTrace_6821649
  have hstable : (prefixWord ++ tailWord_6821649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821649).length < 2 ^ (prefixWord ++ tailWord_6821649).sum := by decide
  have hdescent : baseEnd_6821649 < baseStart_6821649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821656 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 3, 2, 3]
def baseStart_6821656 : Nat := 118140960795 + 6821656 * 2 ^ 59
def prefixEnd_6821656 : Nat := 4983230072969 + 3 ^ 40 * 6821656 * 2
def baseEnd_6821656 : Nat := 3502788387627267473227781

theorem tailTrace_6821656 : CollatzResearch.WordTrace tailWord_6821656 prefixEnd_6821656 3502788387627267473227781 := by
  unfold tailWord_6821656
  simp only [CollatzResearch.WordTrace]
  refine ⟨124403117287156416467926411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165870823049541888623901881 124403117287156416467926411)
  ·
    refine ⟨186604675930734624701889617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124403117287156416467926411 186604675930734624701889617)
    ·
      refine ⟨139953506948050968526417213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186604675930734624701889617 139953506948050968526417213)
      ·
        refine ⟨52482565105519113197406455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139953506948050968526417213 52482565105519113197406455)
        ·
          refine ⟨78723847658278669796109683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52482565105519113197406455 78723847658278669796109683)
          ·
            refine ⟨118085771487418004694164525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78723847658278669796109683 118085771487418004694164525)
            ·
              refine ⟨44282164307781751760311697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118085771487418004694164525 44282164307781751760311697)
              ·
                refine ⟨33211623230836313820233773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44282164307781751760311697 33211623230836313820233773)
                ·
                  refine ⟨12454358711563617682587665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33211623230836313820233773 12454358711563617682587665)
                  ·
                    refine ⟨9340769033672713261940749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12454358711563617682587665 9340769033672713261940749)
                    ·
                      refine ⟨3502788387627267473227781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9340769033672713261940749 3502788387627267473227781)
                      ·
                        rfl

theorem cell23_6821656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_6821656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821656 prefixEnd_6821656 := by exact prefixLift 6821656
  have htrace : WordTrace (prefixWord ++ tailWord_6821656) baseStart_6821656 baseEnd_6821656 := by
    simpa [prefixWord, tailWord_6821656, baseEnd_6821656] using wordTrace_append hprefix tailTrace_6821656
  have hstable : (prefixWord ++ tailWord_6821656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821656).length < 2 ^ (prefixWord ++ tailWord_6821656).sum := by decide
  have hdescent : baseEnd_6821656 < baseStart_6821656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821676 : List Nat := [2, 2, 1, 1, 1, 6, 3, 7]
def baseStart_6821676 : Nat := 118140960795 + 6821676 * 2 ^ 59
def prefixEnd_6821676 : Nat := 4983230072969 + 3 ^ 40 * 6821676 * 2
def baseEnd_6821676 : Nat := 129733283601494718332507

theorem tailTrace_6821676 : CollatzResearch.WordTrace tailWord_6821676 prefixEnd_6821676 129733283601494718332507 := by
  unfold tailWord_6821676
  simp only [CollatzResearch.WordTrace]
  refine ⟨124403482017120188175790441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165871309356160250901053921 124403482017120188175790441)
  ·
    refine ⟨93302611512840141131842831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124403482017120188175790441 93302611512840141131842831)
    ·
      refine ⟨139953917269260211697764247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93302611512840141131842831 139953917269260211697764247)
      ·
        refine ⟨209930875903890317546646371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139953917269260211697764247 209930875903890317546646371)
        ·
          refine ⟨314896313855835476319969557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209930875903890317546646371 314896313855835476319969557)
          ·
            refine ⟨14760764711992287952498573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 314896313855835476319969557 14760764711992287952498573)
            ·
              refine ⟨5535286766997107982186965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14760764711992287952498573 5535286766997107982186965)
              ·
                refine ⟨129733283601494718332507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5535286766997107982186965 129733283601494718332507)
                ·
                  rfl

theorem cell23_6821676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 7].length) (baseStart_6821676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821676 prefixEnd_6821676 := by exact prefixLift 6821676
  have htrace : WordTrace (prefixWord ++ tailWord_6821676) baseStart_6821676 baseEnd_6821676 := by
    simpa [prefixWord, tailWord_6821676, baseEnd_6821676] using wordTrace_append hprefix tailTrace_6821676
  have hstable : (prefixWord ++ tailWord_6821676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821676).length < 2 ^ (prefixWord ++ tailWord_6821676).sum := by decide
  have hdescent : baseEnd_6821676 < baseStart_6821676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821690 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3]
def baseStart_6821690 : Nat := 118140960795 + 6821690 * 2 ^ 59
def prefixEnd_6821690 : Nat := 4983230072969 + 3 ^ 40 * 6821690 * 2
def baseEnd_6821690 : Nat := 3502805845969520340202625

theorem tailTrace_6821690 : CollatzResearch.WordTrace tailWord_6821690 prefixEnd_6821690 3502805845969520340202625 := by
  unfold tailWord_6821690
  simp only [CollatzResearch.WordTrace]
  refine ⟨62201868664047414185647631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165871649770793104495060349 62201868664047414185647631)
  ·
    refine ⟨93302802996071121278471447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62201868664047414185647631 93302802996071121278471447)
    ·
      refine ⟨139954204494106681917707171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93302802996071121278471447 139954204494106681917707171)
      ·
        refine ⟨209931306741160022876560757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139954204494106681917707171 209931306741160022876560757)
        ·
          refine ⟨19681060006983752144677571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209931306741160022876560757 19681060006983752144677571)
          ·
            refine ⟨29521590010475628217016357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19681060006983752144677571 29521590010475628217016357)
            ·
              refine ⟨5535298126964180290690567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29521590010475628217016357 5535298126964180290690567)
              ·
                refine ⟨8302947190446270436035851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535298126964180290690567 8302947190446270436035851)
                ·
                  refine ⟨12454420785669405654053777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8302947190446270436035851 12454420785669405654053777)
                  ·
                    refine ⟨9340815589252054240540333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12454420785669405654053777 9340815589252054240540333)
                    ·
                      refine ⟨3502805845969520340202625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9340815589252054240540333 3502805845969520340202625)
                      ·
                        rfl

theorem cell23_6821690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3].length) (baseStart_6821690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821690 prefixEnd_6821690 := by exact prefixLift 6821690
  have htrace : WordTrace (prefixWord ++ tailWord_6821690) baseStart_6821690 baseEnd_6821690 := by
    simpa [prefixWord, tailWord_6821690, baseEnd_6821690] using wordTrace_append hprefix tailTrace_6821690
  have hstable : (prefixWord ++ tailWord_6821690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821690).length < 2 ^ (prefixWord ++ tailWord_6821690).sum := by decide
  have hdescent : baseEnd_6821690 < baseStart_6821690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821738 : List Nat := [3, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_6821738 : Nat := 118140960795 + 6821738 * 2 ^ 59
def prefixEnd_6821738 : Nat := 4983230072969 + 3 ^ 40 * 6821738 * 2
def baseEnd_6821738 : Nat := 3502830493040936152402405

theorem tailTrace_6821738 : CollatzResearch.WordTrace tailWord_6821738 prefixEnd_6821738 3502830493040936152402405 := by
  unfold tailWord_6821738
  simp only [CollatzResearch.WordTrace]
  refine ⟨62202306340003940235084467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165872816906677173960225245 62202306340003940235084467)
  ·
    refine ⟨93303459510005910352626701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62202306340003940235084467 93303459510005910352626701)
    ·
      refine ⟨34988797316252216382235013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93303459510005910352626701 34988797316252216382235013)
      ·
        refine ⟨6560399496797290571669065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34988797316252216382235013 6560399496797290571669065)
        ·
          refine ⟨4920299622597967928751799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6560399496797290571669065 4920299622597967928751799)
          ·
            refine ⟨7380449433896951893127699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920299622597967928751799 7380449433896951893127699)
            ·
              refine ⟨11070674150845427839691549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7380449433896951893127699 11070674150845427839691549)
              ·
                refine ⟨4151502806567035439884331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11070674150845427839691549 4151502806567035439884331)
                ·
                  refine ⟨6227254209850553159826497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151502806567035439884331 6227254209850553159826497)
                  ·
                    refine ⟨4670440657387914869869873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6227254209850553159826497 4670440657387914869869873)
                    ·
                      refine ⟨3502830493040936152402405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4670440657387914869869873 3502830493040936152402405)
                      ·
                        rfl

theorem cell23_6821738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_6821738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821738 prefixEnd_6821738 := by exact prefixLift 6821738
  have htrace : WordTrace (prefixWord ++ tailWord_6821738) baseStart_6821738 baseEnd_6821738 := by
    simpa [prefixWord, tailWord_6821738, baseEnd_6821738] using wordTrace_append hprefix tailTrace_6821738
  have hstable : (prefixWord ++ tailWord_6821738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821738).length < 2 ^ (prefixWord ++ tailWord_6821738).sum := by decide
  have hdescent : baseEnd_6821738 < baseStart_6821738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821746 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_6821746 : Nat := 118140960795 + 6821746 * 2 ^ 59
def prefixEnd_6821746 : Nat := 4983230072969 + 3 ^ 40 * 6821746 * 2
def baseEnd_6821746 : Nat := 3502834600886172121102367

theorem tailTrace_6821746 : CollatzResearch.WordTrace tailWord_6821746 prefixEnd_6821746 3502834600886172121102367 := by
  unfold tailWord_6821746
  simp only [CollatzResearch.WordTrace]
  refine ⟨62202379285996694576657273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165873011429324518871086061 62202379285996694576657273)
  ·
    refine ⟨46651784464497520932492955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62202379285996694576657273 46651784464497520932492955)
    ·
      refine ⟨69977676696746281398739433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46651784464497520932492955 69977676696746281398739433)
      ·
        refine ⟨52483257522559711049054575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69977676696746281398739433 52483257522559711049054575)
        ·
          refine ⟨78724886283839566573581863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52483257522559711049054575 78724886283839566573581863)
          ·
            refine ⟨118087329425759349860372795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78724886283839566573581863 118087329425759349860372795)
            ·
              refine ⟨177130994138639024790559193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118087329425759349860372795 177130994138639024790559193)
              ·
                refine ⟨132848245603979268592919395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177130994138639024790559193 132848245603979268592919395)
                ·
                  refine ⟨199272368405968902889379093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132848245603979268592919395 199272368405968902889379093)
                  ·
                    refine ⟨9340892269029792322939645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 199272368405968902889379093 9340892269029792322939645)
                    ·
                      refine ⟨3502834600886172121102367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9340892269029792322939645 3502834600886172121102367)
                      ·
                        rfl

theorem cell23_6821746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_6821746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821746 prefixEnd_6821746 := by exact prefixLift 6821746
  have htrace : WordTrace (prefixWord ++ tailWord_6821746) baseStart_6821746 baseEnd_6821746 := by
    simpa [prefixWord, tailWord_6821746, baseEnd_6821746] using wordTrace_append hprefix tailTrace_6821746
  have hstable : (prefixWord ++ tailWord_6821746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821746).length < 2 ^ (prefixWord ++ tailWord_6821746).sum := by decide
  have hdescent : baseEnd_6821746 < baseStart_6821746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821759 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_6821759 : Nat := 118140960795 + 6821759 * 2 ^ 59
def prefixEnd_6821759 : Nat := 4983230072969 + 3 ^ 40 * 6821759 * 2
def baseEnd_6821759 : Nat := 3502841276134680570239807

theorem tailTrace_6821759 : CollatzResearch.WordTrace tailWord_6821759 prefixEnd_6821759 3502841276134680570239807 := by
  unfold tailWord_6821759
  simp only [CollatzResearch.WordTrace]
  refine ⟨248809991292939681526852331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165873327528626454351234887 248809991292939681526852331)
  ·
    refine ⟨373214986939409522290278497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248809991292939681526852331 373214986939409522290278497)
    ·
      refine ⟨279911240204557141717708873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373214986939409522290278497 279911240204557141717708873)
      ·
        refine ⟨209933430153417856288281655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279911240204557141717708873 209933430153417856288281655)
        ·
          refine ⟨314900145230126784432422483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209933430153417856288281655 314900145230126784432422483)
          ·
            refine ⟨472350217845190176648633725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314900145230126784432422483 472350217845190176648633725)
            ·
              refine ⟨177131331691946316243237647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472350217845190176648633725 177131331691946316243237647)
              ·
                refine ⟨265696997537919474364856471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177131331691946316243237647 265696997537919474364856471)
                ·
                  refine ⟨398545496306879211547284707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265696997537919474364856471 398545496306879211547284707)
                  ·
                    refine ⟨597818244460318817320927061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 398545496306879211547284707 597818244460318817320927061)
                    ·
                      refine ⟨3502841276134680570239807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 597818244460318817320927061 3502841276134680570239807)
                      ·
                        rfl

theorem cell23_6821759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_6821759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821759 prefixEnd_6821759 := by exact prefixLift 6821759
  have htrace : WordTrace (prefixWord ++ tailWord_6821759) baseStart_6821759 baseEnd_6821759 := by
    simpa [prefixWord, tailWord_6821759, baseEnd_6821759] using wordTrace_append hprefix tailTrace_6821759
  have hstable : (prefixWord ++ tailWord_6821759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821759).length < 2 ^ (prefixWord ++ tailWord_6821759).sum := by decide
  have hdescent : baseEnd_6821759 < baseStart_6821759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821760 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 2, 2, 2]
def baseStart_6821760 : Nat := 118140960795 + 6821760 * 2 ^ 59
def prefixEnd_6821760 : Nat := 4983230072969 + 3 ^ 40 * 6821760 * 2
def baseEnd_6821760 : Nat := 3502841789615335066327303

theorem tailTrace_6821760 : CollatzResearch.WordTrace tailWord_6821760 prefixEnd_6821760 3502841789615335066327303 := by
  unfold tailWord_6821760
  simp only [CollatzResearch.WordTrace]
  refine ⟨124405013882968029348819367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165873351843957372465092489 124405013882968029348819367)
  ·
    refine ⟨186607520824452044023229051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124405013882968029348819367 186607520824452044023229051)
    ·
      refine ⟨279911281236678066034843577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186607520824452044023229051 279911281236678066034843577)
      ·
        refine ⟨209933460927508549526132683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279911281236678066034843577 209933460927508549526132683)
        ·
          refine ⟨314900191391262824289199025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209933460927508549526132683 314900191391262824289199025)
          ·
            refine ⟨236175143543447118216899269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314900191391262824289199025 236175143543447118216899269)
            ·
              refine ⟨44282839414396334665668613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236175143543447118216899269 44282839414396334665668613)
              ·
                refine ⟨8303032390199312749812865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44282839414396334665668613 8303032390199312749812865)
                ·
                  refine ⟨6227274292649484562359649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8303032390199312749812865 6227274292649484562359649)
                  ·
                    refine ⟨4670455719487113421769737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6227274292649484562359649 4670455719487113421769737)
                    ·
                      refine ⟨3502841789615335066327303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4670455719487113421769737 3502841789615335066327303)
                      ·
                        rfl

theorem cell23_6821760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 2, 2, 2].length) (baseStart_6821760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821760 prefixEnd_6821760 := by exact prefixLift 6821760
  have htrace : WordTrace (prefixWord ++ tailWord_6821760) baseStart_6821760 baseEnd_6821760 := by
    simpa [prefixWord, tailWord_6821760, baseEnd_6821760] using wordTrace_append hprefix tailTrace_6821760
  have hstable : (prefixWord ++ tailWord_6821760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821760).length < 2 ^ (prefixWord ++ tailWord_6821760).sum := by decide
  have hdescent : baseEnd_6821760 < baseStart_6821760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821777 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 2, 2, 2]
def baseStart_6821777 : Nat := 118140960795 + 6821777 * 2 ^ 59
def prefixEnd_6821777 : Nat := 4983230072969 + 3 ^ 40 * 6821777 * 2
def baseEnd_6821777 : Nat := 3502850518786461499814725

theorem tailTrace_6821777 : CollatzResearch.WordTrace tailWord_6821777 prefixEnd_6821777 3502850518786461499814725 := by
  unfold tailWord_6821777
  simp only [CollatzResearch.WordTrace]
  refine ⟨248810647806874470601007585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165873765204582980400671723 248810647806874470601007585)
  ·
    refine ⟨186607985855155852950755689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248810647806874470601007585 186607985855155852950755689)
    ·
      refine ⟨139955989391366889713066767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186607985855155852950755689 139955989391366889713066767)
      ·
        refine ⟨209933984087050334569600151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139955989391366889713066767 209933984087050334569600151)
        ·
          refine ⟨314900976130575501854400227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209933984087050334569600151 314900976130575501854400227)
          ·
            refine ⟨472351464195863252781600341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314900976130575501854400227 472351464195863252781600341)
            ·
              refine ⟨5535368721045272493534379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 472351464195863252781600341 5535368721045272493534379)
              ·
                refine ⟨8303053081567908740301569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535368721045272493534379 8303053081567908740301569)
                ·
                  refine ⟨6227289811175931555226177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8303053081567908740301569 6227289811175931555226177)
                  ·
                    refine ⟨4670467358381948666419633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6227289811175931555226177 4670467358381948666419633)
                    ·
                      refine ⟨3502850518786461499814725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4670467358381948666419633 3502850518786461499814725)
                      ·
                        rfl

theorem cell23_6821777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 2, 2, 2].length) (baseStart_6821777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821777 prefixEnd_6821777 := by exact prefixLift 6821777
  have htrace : WordTrace (prefixWord ++ tailWord_6821777) baseStart_6821777 baseEnd_6821777 := by
    simpa [prefixWord, tailWord_6821777, baseEnd_6821777] using wordTrace_append hprefix tailTrace_6821777
  have hstable : (prefixWord ++ tailWord_6821777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821777).length < 2 ^ (prefixWord ++ tailWord_6821777).sum := by decide
  have hdescent : baseEnd_6821777 < baseStart_6821777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821813 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_6821813 : Nat := 118140960795 + 6821813 * 2 ^ 59
def prefixEnd_6821813 : Nat := 4983230072969 + 3 ^ 40 * 6821813 * 2
def baseEnd_6821813 : Nat := 1167623001363341119654853

theorem tailTrace_6821813 : CollatzResearch.WordTrace tailWord_6821813 prefixEnd_6821813 1167623001363341119654853 := by
  unfold tailWord_6821813
  simp only [CollatzResearch.WordTrace]
  refine ⟨248811960834744048749318093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165874640556496032499545395 248811960834744048749318093)
  ·
    refine ⟨93304485313029018280994285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248811960834744048749318093 93304485313029018280994285)
    ·
      refine ⟨34989181992385881855372857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93304485313029018280994285 34989181992385881855372857)
      ·
        refine ⟨26241886494289411391529643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34989181992385881855372857 26241886494289411391529643)
        ·
          refine ⟨39362829741434117087294465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26241886494289411391529643 39362829741434117087294465)
          ·
            refine ⟨29522122306075587815470849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39362829741434117087294465 29522122306075587815470849)
            ·
              refine ⟨22141591729556690861603137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29522122306075587815470849 22141591729556690861603137)
              ·
                refine ⟨16606193797167518146202353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22141591729556690861603137 16606193797167518146202353)
                ·
                  refine ⟨12454645347875638609651765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16606193797167518146202353 12454645347875638609651765)
                  ·
                    refine ⟨1167623001363341119654853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12454645347875638609651765 1167623001363341119654853)
                    ·
                      rfl

theorem cell23_6821813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_6821813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821813 prefixEnd_6821813 := by exact prefixLift 6821813
  have htrace : WordTrace (prefixWord ++ tailWord_6821813) baseStart_6821813 baseEnd_6821813 := by
    simpa [prefixWord, tailWord_6821813, baseEnd_6821813] using wordTrace_append hprefix tailTrace_6821813
  have hstable : (prefixWord ++ tailWord_6821813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821813).length < 2 ^ (prefixWord ++ tailWord_6821813).sum := by decide
  have hdescent : baseEnd_6821813 < baseStart_6821813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821833 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 2, 4, 2]
def baseStart_6821833 : Nat := 118140960795 + 6821833 * 2 ^ 59
def prefixEnd_6821833 : Nat := 4983230072969 + 3 ^ 40 * 6821833 * 2
def baseEnd_6821833 : Nat := 3502879273703113280714467

theorem tailTrace_6821833 : CollatzResearch.WordTrace tailWord_6821833 prefixEnd_6821833 3502879273703113280714467 := by
  unfold tailWord_6821833
  simp only [CollatzResearch.WordTrace]
  refine ⟨248812690294671592165046153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165875126863114394776697435 248812690294671592165046153)
  ·
    refine ⟨186609517721003694123784615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248812690294671592165046153 186609517721003694123784615)
    ·
      refine ⟨279914276581505541185676923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186609517721003694123784615 279914276581505541185676923)
      ·
        refine ⟨419871414872258311778515385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279914276581505541185676923 419871414872258311778515385)
        ·
          refine ⟨314903561154193733833886539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419871414872258311778515385 314903561154193733833886539)
          ·
            refine ⟨472355341731290600750829809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314903561154193733833886539 472355341731290600750829809)
            ·
              refine ⟨354266506298467950563122357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472355341731290600750829809 354266506298467950563122357)
              ·
                refine ⟨33212484965481370365292721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 354266506298467950563122357 33212484965481370365292721)
                ·
                  refine ⟨24909363724111027773969541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33212484965481370365292721 24909363724111027773969541)
                  ·
                    refine ⟨4670505698270817707619289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24909363724111027773969541 4670505698270817707619289)
                    ·
                      refine ⟨3502879273703113280714467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4670505698270817707619289 3502879273703113280714467)
                      ·
                        rfl

theorem cell23_6821833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 4, 2].length) (baseStart_6821833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821833 prefixEnd_6821833 := by exact prefixLift 6821833
  have htrace : WordTrace (prefixWord ++ tailWord_6821833) baseStart_6821833 baseEnd_6821833 := by
    simpa [prefixWord, tailWord_6821833, baseEnd_6821833] using wordTrace_append hprefix tailTrace_6821833
  have hstable : (prefixWord ++ tailWord_6821833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821833).length < 2 ^ (prefixWord ++ tailWord_6821833).sum := by decide
  have hdescent : baseEnd_6821833 < baseStart_6821833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821873 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 8]
def baseStart_6821873 : Nat := 118140960795 + 6821873 * 2 ^ 59
def prefixEnd_6821873 : Nat := 4983230072969 + 3 ^ 40 * 6821873 * 2
def baseEnd_6821873 : Nat := 389211090325477013801587

theorem tailTrace_6821873 : CollatzResearch.WordTrace tailWord_6821873 prefixEnd_6821873 389211090325477013801587 := by
  unfold tailWord_6821873
  simp only [CollatzResearch.WordTrace]
  refine ⟨248814149214526678996502273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165876099476351119331001515 248814149214526678996502273)
  ·
    refine ⟨186610611910895009247376705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248814149214526678996502273 186610611910895009247376705)
    ·
      refine ⟨139957958933171256935532529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186610611910895009247376705 139957958933171256935532529)
      ·
        refine ⟨104968469199878442701649397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139957958933171256935532529 104968469199878442701649397)
        ·
          refine ⟨9840793987488604003279631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104968469199878442701649397 9840793987488604003279631)
          ·
            refine ⟨14761190981232906004919447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9840793987488604003279631 14761190981232906004919447)
            ·
              refine ⟨22141786471849359007379171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14761190981232906004919447 22141786471849359007379171)
              ·
                refine ⟨33212679707774038511068757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22141786471849359007379171 33212679707774038511068757)
                ·
                  refine ⟨389211090325477013801587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33212679707774038511068757 389211090325477013801587)
                  ·
                    rfl

theorem cell23_6821873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 8].length) (baseStart_6821873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821873 prefixEnd_6821873 := by exact prefixLift 6821873
  have htrace : WordTrace (prefixWord ++ tailWord_6821873) baseStart_6821873 baseEnd_6821873 := by
    simpa [prefixWord, tailWord_6821873, baseEnd_6821873] using wordTrace_append hprefix tailTrace_6821873
  have hstable : (prefixWord ++ tailWord_6821873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821873).length < 2 ^ (prefixWord ++ tailWord_6821873).sum := by decide
  have hdescent : baseEnd_6821873 < baseStart_6821873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821900 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 3, 1, 3]
def baseStart_6821900 : Nat := 118140960795 + 6821900 * 2 ^ 59
def prefixEnd_6821900 : Nat := 4983230072969 + 3 ^ 40 * 6821900 * 2
def baseEnd_6821900 : Nat := 3502913676906964518576659

theorem tailTrace_6821900 : CollatzResearch.WordTrace tailWord_6821900 prefixEnd_6821900 3502913676906964518576659 := by
  unfold tailWord_6821900
  simp only [CollatzResearch.WordTrace]
  refine ⟨124407566992714431303867577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165876755990285908405156769 124407566992714431303867577)
  ·
    refine ⟨93305675244535823477900683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124407566992714431303867577 93305675244535823477900683)
    ·
      refine ⟨139958512866803735216851025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93305675244535823477900683 139958512866803735216851025)
      ·
        refine ⟨104968884650102801412638269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139958512866803735216851025 104968884650102801412638269)
        ·
          refine ⟨39363331743788550529739351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104968884650102801412638269 39363331743788550529739351)
          ·
            refine ⟨59044997615682825794609027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39363331743788550529739351 59044997615682825794609027)
            ·
              refine ⟨88567496423524238691913541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59044997615682825794609027 88567496423524238691913541)
              ·
                refine ⟨16606405579410794754733789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88567496423524238691913541 16606405579410794754733789)
                ·
                  refine ⟨6227402092279048033025171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16606405579410794754733789 6227402092279048033025171)
                  ·
                    refine ⟨9341103138418572049537757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6227402092279048033025171 9341103138418572049537757)
                    ·
                      refine ⟨3502913676906964518576659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9341103138418572049537757 3502913676906964518576659)
                      ·
                        rfl

theorem cell23_6821900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_6821900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821900 prefixEnd_6821900 := by exact prefixLift 6821900
  have htrace : WordTrace (prefixWord ++ tailWord_6821900) baseStart_6821900 baseEnd_6821900 := by
    simpa [prefixWord, tailWord_6821900, baseEnd_6821900] using wordTrace_append hprefix tailTrace_6821900
  have hstable : (prefixWord ++ tailWord_6821900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821900).length < 2 ^ (prefixWord ++ tailWord_6821900).sum := by decide
  have hdescent : baseEnd_6821900 < baseStart_6821900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821911 : List Nat := [1, 1, 3, 5, 3, 1, 1, 3, 1, 4]
def baseStart_6821911 : Nat := 118140960795 + 6821911 * 2 ^ 59
def prefixEnd_6821911 : Nat := 4983230072969 + 3 ^ 40 * 6821911 * 2
def baseEnd_6821911 : Nat := 1167639775064721325179703

theorem tailTrace_6821911 : CollatzResearch.WordTrace tailWord_6821911 prefixEnd_6821911 1167639775064721325179703 := by
  unfold tailWord_6821911
  simp only [CollatzResearch.WordTrace]
  refine ⟨248815535188389011486385587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165877023458926007657590391 248815535188389011486385587)
  ·
    refine ⟨373223302782583517229578381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248815535188389011486385587 373223302782583517229578381)
    ·
      refine ⟨139958738543468818961091893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373223302782583517229578381 139958738543468818961091893)
      ·
        refine ⟨13121131738450201777602365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139958738543468818961091893 13121131738450201777602365)
        ·
          refine ⟨4920424401918825666600887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13121131738450201777602365 4920424401918825666600887)
          ·
            refine ⟨7380636602878238499901331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920424401918825666600887 7380636602878238499901331)
            ·
              refine ⟨11070954904317357749851997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7380636602878238499901331 11070954904317357749851997)
              ·
                refine ⟨4151608089119009156194499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11070954904317357749851997 4151608089119009156194499)
                ·
                  refine ⟨6227412133678513734291749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151608089119009156194499 6227412133678513734291749)
                  ·
                    refine ⟨1167639775064721325179703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6227412133678513734291749 1167639775064721325179703)
                    ·
                      rfl

theorem cell23_6821911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_6821911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821911 prefixEnd_6821911 := by exact prefixLift 6821911
  have htrace : WordTrace (prefixWord ++ tailWord_6821911) baseStart_6821911 baseEnd_6821911 := by
    simpa [prefixWord, tailWord_6821911, baseEnd_6821911] using wordTrace_append hprefix tailTrace_6821911
  have hstable : (prefixWord ++ tailWord_6821911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821911).length < 2 ^ (prefixWord ++ tailWord_6821911).sum := by decide
  have hdescent : baseEnd_6821911 < baseStart_6821911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821934 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_6821934 : Nat := 118140960795 + 6821934 * 2 ^ 59
def prefixEnd_6821934 : Nat := 4983230072969 + 3 ^ 40 * 6821934 * 2
def baseEnd_6821934 : Nat := 3502931135249217385551503

theorem tailTrace_6821934 : CollatzResearch.WordTrace tailWord_6821934 prefixEnd_6821934 3502931135249217385551503 := by
  unfold tailWord_6821934
  simp only [CollatzResearch.WordTrace]
  refine ⟨31102046758413210801809107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165877582711537124276315237 31102046758413210801809107)
  ·
    refine ⟨46653070137619816202713661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31102046758413210801809107 46653070137619816202713661)
    ·
      refine ⟨17494901301607431076017623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46653070137619816202713661 17494901301607431076017623)
      ·
        refine ⟨26242351952411146614026435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17494901301607431076017623 26242351952411146614026435)
        ·
          refine ⟨39363527928616719921039653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26242351952411146614026435 39363527928616719921039653)
          ·
            refine ⟨7380661486615634985194935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39363527928616719921039653 7380661486615634985194935)
            ·
              refine ⟨11070992229923452477792403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7380661486615634985194935 11070992229923452477792403)
              ·
                refine ⟨16606488344885178716688605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11070992229923452477792403 16606488344885178716688605)
                ·
                  refine ⟨6227433129331942018758227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16606488344885178716688605 6227433129331942018758227)
                  ·
                    refine ⟨9341149693997913028137341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6227433129331942018758227 9341149693997913028137341)
                    ·
                      refine ⟨3502931135249217385551503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9341149693997913028137341 3502931135249217385551503)
                      ·
                        rfl

theorem cell23_6821934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_6821934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821934 prefixEnd_6821934 := by exact prefixLift 6821934
  have htrace : WordTrace (prefixWord ++ tailWord_6821934) baseStart_6821934 baseEnd_6821934 := by
    simpa [prefixWord, tailWord_6821934, baseEnd_6821934] using wordTrace_append hprefix tailTrace_6821934
  have hstable : (prefixWord ++ tailWord_6821934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821934).length < 2 ^ (prefixWord ++ tailWord_6821934).sum := by decide
  have hdescent : baseEnd_6821934 < baseStart_6821934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821943 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_6821943 : Nat := 118140960795 + 6821943 * 2 ^ 59
def prefixEnd_6821943 : Nat := 4983230072969 + 3 ^ 40 * 6821943 * 2
def baseEnd_6821943 : Nat := 3502935756575107850338961

theorem tailTrace_6821943 : CollatzResearch.WordTrace tailWord_6821943 prefixEnd_6821943 3502935756575107850338961 := by
  unfold tailWord_6821943
  simp only [CollatzResearch.WordTrace]
  refine ⟨248816702324273080951550483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165877801549515387301033655 248816702324273080951550483)
  ·
    refine ⟨373225053486409621427325725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248816702324273080951550483 373225053486409621427325725)
    ·
      refine ⟨139959395057403608035247147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373225053486409621427325725 139959395057403608035247147)
      ·
        refine ⟨209939092586105412052870721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139959395057403608035247147 209939092586105412052870721)
        ·
          refine ⟨157454319439579059039653041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209939092586105412052870721 157454319439579059039653041)
          ·
            refine ⟨118090739579684294279739781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157454319439579059039653041 118090739579684294279739781)
            ·
              refine ⟨22142013671190805177451209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118090739579684294279739781 22142013671190805177451209)
              ·
                refine ⟨16606510253393103883088407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22142013671190805177451209 16606510253393103883088407)
                ·
                  refine ⟨24909765380089655824632611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16606510253393103883088407 24909765380089655824632611)
                  ·
                    refine ⟨37364648070134483736948917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24909765380089655824632611 37364648070134483736948917)
                    ·
                      refine ⟨3502935756575107850338961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37364648070134483736948917 3502935756575107850338961)
                      ·
                        rfl

theorem cell23_6821943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_6821943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821943 prefixEnd_6821943 := by exact prefixLift 6821943
  have htrace : WordTrace (prefixWord ++ tailWord_6821943) baseStart_6821943 baseEnd_6821943 := by
    simpa [prefixWord, tailWord_6821943, baseEnd_6821943] using wordTrace_append hprefix tailTrace_6821943
  have hstable : (prefixWord ++ tailWord_6821943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821943).length < 2 ^ (prefixWord ++ tailWord_6821943).sum := by decide
  have hdescent : baseEnd_6821943 < baseStart_6821943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821960 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_6821960 : Nat := 118140960795 + 6821960 * 2 ^ 59
def prefixEnd_6821960 : Nat := 4983230072969 + 3 ^ 40 * 6821960 * 2
def baseEnd_6821960 : Nat := 3502944485746234283826383

theorem tailTrace_6821960 : CollatzResearch.WordTrace tailWord_6821960 prefixEnd_6821960 3502944485746234283826383 := by
  unfold tailWord_6821960
  simp only [CollatzResearch.WordTrace]
  refine ⟨124408661182605746427459667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165878214910140995236612889 124408661182605746427459667)
  ·
    refine ⟨186612991773908619641189501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124408661182605746427459667 186612991773908619641189501)
    ·
      refine ⟨69979871915215732365446063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186612991773908619641189501 69979871915215732365446063)
      ·
        refine ⟨104969807872823598548169095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69979871915215732365446063 104969807872823598548169095)
        ·
          refine ⟨157454711809235397822253643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104969807872823598548169095 157454711809235397822253643)
          ·
            refine ⟨236182067713853096733380465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157454711809235397822253643 236182067713853096733380465)
            ·
              refine ⟨177136550785389822550035349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236182067713853096733380465 177136550785389822550035349)
              ·
                refine ⟨8303275818065147932032907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177136550785389822550035349 8303275818065147932032907)
                ·
                  refine ⟨12454913727097721898049361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8303275818065147932032907 12454913727097721898049361)
                  ·
                    refine ⟨9341185295323291423537021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12454913727097721898049361 9341185295323291423537021)
                    ·
                      refine ⟨3502944485746234283826383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9341185295323291423537021 3502944485746234283826383)
                      ·
                        rfl

theorem cell23_6821960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_6821960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821960 prefixEnd_6821960 := by exact prefixLift 6821960
  have htrace : WordTrace (prefixWord ++ tailWord_6821960) baseStart_6821960 baseEnd_6821960 := by
    simpa [prefixWord, tailWord_6821960, baseEnd_6821960] using wordTrace_append hprefix tailTrace_6821960
  have hstable : (prefixWord ++ tailWord_6821960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821960).length < 2 ^ (prefixWord ++ tailWord_6821960).sum := by decide
  have hdescent : baseEnd_6821960 < baseStart_6821960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6821977 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 1, 2, 3]
def baseStart_6821977 : Nat := 118140960795 + 6821977 * 2 ^ 59
def prefixEnd_6821977 : Nat := 4983230072969 + 3 ^ 40 * 6821977 * 2
def baseEnd_6821977 : Nat := 3502953214917360717313805

theorem tailTrace_6821977 : CollatzResearch.WordTrace tailWord_6821977 prefixEnd_6821977 3502953214917360717313805 := by
  unfold tailWord_6821977
  simp only [CollatzResearch.WordTrace]
  refine ⟨248817942406149904758288185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165878628270766603172192123 248817942406149904758288185)
  ·
    refine ⟨186613456804612428568716139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248817942406149904758288185 186613456804612428568716139)
    ·
      refine ⟨279920185206918642853074209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186613456804612428568716139 279920185206918642853074209)
      ·
        refine ⟨209940138905188982139805657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279920185206918642853074209 209940138905188982139805657)
        ·
          refine ⟨157455104178891736604854243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209940138905188982139805657 157455104178891736604854243)
          ·
            refine ⟨236182656268337604907281365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157455104178891736604854243 236182656268337604907281365)
            ·
              refine ⟨5535531006289162615014407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 236182656268337604907281365 5535531006289162615014407)
              ·
                refine ⟨8303296509433743922521611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535531006289162615014407 8303296509433743922521611)
                ·
                  refine ⟨12454944764150615883782417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8303296509433743922521611 12454944764150615883782417)
                  ·
                    refine ⟨9341208573112961912836813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12454944764150615883782417 9341208573112961912836813)
                    ·
                      refine ⟨3502953214917360717313805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9341208573112961912836813 3502953214917360717313805)
                      ·
                        rfl

theorem cell23_6821977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 2, 3].length) (baseStart_6821977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6821977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6821977 prefixEnd_6821977 := by exact prefixLift 6821977
  have htrace : WordTrace (prefixWord ++ tailWord_6821977) baseStart_6821977 baseEnd_6821977 := by
    simpa [prefixWord, tailWord_6821977, baseEnd_6821977] using wordTrace_append hprefix tailTrace_6821977
  have hstable : (prefixWord ++ tailWord_6821977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6821977).length < 2 ^ (prefixWord ++ tailWord_6821977).sum := by decide
  have hdescent : baseEnd_6821977 < baseStart_6821977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6821977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822007 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 2, 1, 3]
def baseStart_6822007 : Nat := 118140960795 + 6822007 * 2 ^ 59
def prefixEnd_6822007 : Nat := 4983230072969 + 3 ^ 40 * 6822007 * 2
def baseEnd_6822007 : Nat := 3502968619336995599938667

theorem tailTrace_6822007 : CollatzResearch.WordTrace tailWord_6822007 prefixEnd_6822007 3502968619336995599938667 := by
  unfold tailWord_6822007
  simp only [CollatzResearch.WordTrace]
  refine ⟨248819036596041219881880275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165879357730694146587920183 248819036596041219881880275)
  ·
    refine ⟨373228554894061829822820413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248819036596041219881880275 373228554894061829822820413)
    ·
      refine ⟨139960708085273186183557655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373228554894061829822820413 139960708085273186183557655)
      ·
        refine ⟨209941062127909779275336483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139960708085273186183557655 209941062127909779275336483)
        ·
          refine ⟨314911593191864668913004725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209941062127909779275336483 314911593191864668913004725)
          ·
            refine ⟨29522961861737312710594193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 314911593191864668913004725 29522961861737312710594193)
            ·
              refine ⟨22142221396302984532945645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29522961861737312710594193 22142221396302984532945645)
              ·
                refine ⟨8303333023613619199854617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22142221396302984532945645 8303333023613619199854617)
                ·
                  refine ⟨6227499767710214399890963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8303333023613619199854617 6227499767710214399890963)
                  ·
                    refine ⟨9341249651565321599836445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6227499767710214399890963 9341249651565321599836445)
                    ·
                      refine ⟨3502968619336995599938667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9341249651565321599836445 3502968619336995599938667)
                      ·
                        rfl

theorem cell23_6822007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_6822007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822007 prefixEnd_6822007 := by exact prefixLift 6822007
  have htrace : WordTrace (prefixWord ++ tailWord_6822007) baseStart_6822007 baseEnd_6822007 := by
    simpa [prefixWord, tailWord_6822007, baseEnd_6822007] using wordTrace_append hprefix tailTrace_6822007
  have hstable : (prefixWord ++ tailWord_6822007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822007).length < 2 ^ (prefixWord ++ tailWord_6822007).sum := by decide
  have hdescent : baseEnd_6822007 < baseStart_6822007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822034 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_6822034 : Nat := 118140960795 + 6822034 * 2 ^ 59
def prefixEnd_6822034 : Nat := 4983230072969 + 3 ^ 40 * 6822034 * 2
def baseEnd_6822034 : Nat := 3502982483314666994301043

theorem tailTrace_6822034 : CollatzResearch.WordTrace tailWord_6822034 prefixEnd_6822034 3502982483314666994301043 := by
  unfold tailWord_6822034
  simp only [CollatzResearch.WordTrace]
  refine ⟨62205005341735850873278289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165880014244628935662075437 62205005341735850873278289)
  ·
    refine ⟨46653754006301888154958717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62205005341735850873278289 46653754006301888154958717)
    ·
      refine ⟨17495157752363208058109519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46653754006301888154958717 17495157752363208058109519)
      ·
        refine ⟨26242736628544812087164279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17495157752363208058109519 26242736628544812087164279)
        ·
          refine ⟨39364104942817218130746419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26242736628544812087164279 39364104942817218130746419)
          ·
            refine ⟨59046157414225827196119629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39364104942817218130746419 59046157414225827196119629)
            ·
              refine ⟨22142309030334685198544861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59046157414225827196119629 22142309030334685198544861)
              ·
                refine ⟨8303365886375506949454323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22142309030334685198544861 8303365886375506949454323)
                ·
                  refine ⟨12455048829563260424181485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8303365886375506949454323 12455048829563260424181485)
                  ·
                    refine ⟨4670643311086222659068057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12455048829563260424181485 4670643311086222659068057)
                    ·
                      refine ⟨3502982483314666994301043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4670643311086222659068057 3502982483314666994301043)
                      ·
                        rfl

theorem cell23_6822034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_6822034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822034 prefixEnd_6822034 := by exact prefixLift 6822034
  have htrace : WordTrace (prefixWord ++ tailWord_6822034) baseStart_6822034 baseEnd_6822034 := by
    simpa [prefixWord, tailWord_6822034, baseEnd_6822034] using wordTrace_append hprefix tailTrace_6822034
  have hstable : (prefixWord ++ tailWord_6822034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822034).length < 2 ^ (prefixWord ++ tailWord_6822034).sum := by decide
  have hdescent : baseEnd_6822034 < baseStart_6822034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822043 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 4]
def baseStart_6822043 : Nat := 118140960795 + 6822043 * 2 ^ 59
def prefixEnd_6822043 : Nat := 4983230072969 + 3 ^ 40 * 6822043 * 2
def baseEnd_6822043 : Nat := 3502987104640557459088501

theorem tailTrace_6822043 : CollatzResearch.WordTrace tailWord_6822043 prefixEnd_6822043 3502987104640557459088501 := by
  unfold tailWord_6822043
  simp only [CollatzResearch.WordTrace]
  refine ⟨248820349623910798030190783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165880233082607198686793855 248820349623910798030190783)
  ·
    refine ⟨373230524435866197045286175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248820349623910798030190783 373230524435866197045286175)
    ·
      refine ⟨559845786653799295567929263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373230524435866197045286175 559845786653799295567929263)
      ·
        refine ⟨839768679980698943351893895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559845786653799295567929263 839768679980698943351893895)
        ·
          refine ⟨1259653019971048415027840843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839768679980698943351893895 1259653019971048415027840843)
          ·
            refine ⟨1889479529956572622541761265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259653019971048415027840843 1889479529956572622541761265)
            ·
              refine ⟨1417109647467429466906320949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1889479529956572622541761265 1417109647467429466906320949)
              ·
                refine ⟨132854029450071512522467589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1417109647467429466906320949 132854029450071512522467589)
                ·
                  refine ⟨24910130521888408597962673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132854029450071512522467589 24910130521888408597962673)
                  ·
                    refine ⟨18682597891416306448472005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24910130521888408597962673 18682597891416306448472005)
                    ·
                      refine ⟨3502987104640557459088501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18682597891416306448472005 3502987104640557459088501)
                      ·
                        rfl

theorem cell23_6822043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 4].length) (baseStart_6822043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822043 prefixEnd_6822043 := by exact prefixLift 6822043
  have htrace : WordTrace (prefixWord ++ tailWord_6822043) baseStart_6822043 baseEnd_6822043 := by
    simpa [prefixWord, tailWord_6822043, baseEnd_6822043] using wordTrace_append hprefix tailTrace_6822043
  have hstable : (prefixWord ++ tailWord_6822043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822043).length < 2 ^ (prefixWord ++ tailWord_6822043).sum := by decide
  have hdescent : baseEnd_6822043 < baseStart_6822043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822058 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6822058 : Nat := 118140960795 + 6822058 * 2 ^ 59
def prefixEnd_6822058 : Nat := 4983230072969 + 3 ^ 40 * 6822058 * 2
def baseEnd_6822058 : Nat := 3502994806850374900400933

theorem tailTrace_6822058 : CollatzResearch.WordTrace tailWord_6822058 prefixEnd_6822058 3502994806850374900400933 := by
  unfold tailWord_6822058
  simp only [CollatzResearch.WordTrace]
  refine ⟨62205224179714113897996707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165880597812570970394657885 62205224179714113897996707)
  ·
    refine ⟨93307836269571170846995061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62205224179714113897996707 93307836269571170846995061)
    ·
      refine ⟨8747609650272297266905787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93307836269571170846995061 8747609650272297266905787)
      ·
        refine ⟨13121414475408445900358681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8747609650272297266905787 13121414475408445900358681)
        ·
          refine ⟨9841060856556334425269011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13121414475408445900358681 9841060856556334425269011)
          ·
            refine ⟨14761591284834501637903517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9841060856556334425269011 14761591284834501637903517)
            ·
              refine ⟨5535596731812938114213819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14761591284834501637903517 5535596731812938114213819)
              ·
                refine ⟨8303395097719407171320729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535596731812938114213819 8303395097719407171320729)
                ·
                  refine ⟨6227546323289555378490547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8303395097719407171320729 6227546323289555378490547)
                  ·
                    refine ⟨9341319484934333067735821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6227546323289555378490547 9341319484934333067735821)
                    ·
                      refine ⟨3502994806850374900400933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9341319484934333067735821 3502994806850374900400933)
                      ·
                        rfl

theorem cell23_6822058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6822058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822058 prefixEnd_6822058 := by exact prefixLift 6822058
  have htrace : WordTrace (prefixWord ++ tailWord_6822058) baseStart_6822058 baseEnd_6822058 := by
    simpa [prefixWord, tailWord_6822058, baseEnd_6822058] using wordTrace_append hprefix tailTrace_6822058
  have hstable : (prefixWord ++ tailWord_6822058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822058).length < 2 ^ (prefixWord ++ tailWord_6822058).sum := by decide
  have hdescent : baseEnd_6822058 < baseStart_6822058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822104 : List Nat := [2, 1, 2, 2, 4, 2, 3, 2, 5]
def baseStart_6822104 : Nat := 118140960795 + 6822104 * 2 ^ 59
def prefixEnd_6822104 : Nat := 4983230072969 + 3 ^ 40 * 6822104 * 2
def baseEnd_6822104 : Nat := 389224269662275746713969

theorem tailTrace_6822104 : CollatzResearch.WordTrace tailWord_6822104 prefixEnd_6822104 389224269662275746713969 := by
  unfold tailWord_6822104
  simp only [CollatzResearch.WordTrace]
  refine ⟨124411287238344902724080683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165881716317793203632107577 124411287238344902724080683)
  ·
    refine ⟨186616930857517354086121025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124411287238344902724080683 186616930857517354086121025)
    ·
      refine ⟨139962698143138015564590769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186616930857517354086121025 139962698143138015564590769)
      ·
        refine ⟨104972023607353511673443077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139962698143138015564590769 104972023607353511673443077)
        ·
          refine ⟨19682254426378783438770577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104972023607353511673443077 19682254426378783438770577)
          ·
            refine ⟨14761690819784087579077933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19682254426378783438770577 14761690819784087579077933)
            ·
              refine ⟨5535634057419032842154225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14761690819784087579077933 5535634057419032842154225)
              ·
                refine ⟨4151725543064274631615669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5535634057419032842154225 4151725543064274631615669)
                ·
                  refine ⟨389224269662275746713969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4151725543064274631615669 389224269662275746713969)
                  ·
                    rfl

theorem cell23_6822104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 5].length) (baseStart_6822104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822104 prefixEnd_6822104 := by exact prefixLift 6822104
  have htrace : WordTrace (prefixWord ++ tailWord_6822104) baseStart_6822104 baseEnd_6822104 := by
    simpa [prefixWord, tailWord_6822104, baseEnd_6822104] using wordTrace_append hprefix tailTrace_6822104
  have hstable : (prefixWord ++ tailWord_6822104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822104).length < 2 ^ (prefixWord ++ tailWord_6822104).sum := by decide
  have hdescent : baseEnd_6822104 < baseStart_6822104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822115 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6822115 : Nat := 118140960795 + 6822115 * 2 ^ 59
def prefixEnd_6822115 : Nat := 4983230072969 + 3 ^ 40 * 6822115 * 2
def baseEnd_6822115 : Nat := 3503024075247681177388171

theorem tailTrace_6822115 : CollatzResearch.WordTrace tailWord_6822115 prefixEnd_6822115 3503024075247681177388171 := by
  unfold tailWord_6822115
  simp only [CollatzResearch.WordTrace]
  refine ⟨248822975679649954326811799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165881983786433302884541199 248822975679649954326811799)
  ·
    refine ⟨373234463519474931490217699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248822975679649954326811799 373234463519474931490217699)
    ·
      refine ⟨559851695279212397235326549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373234463519474931490217699 559851695279212397235326549)
      ·
        refine ⟨6560762054053270280101483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 559851695279212397235326549 6560762054053270280101483)
        ·
          refine ⟨9841143081079905420152225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6560762054053270280101483 9841143081079905420152225)
          ·
            refine ⟨7380857310809929065114169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9841143081079905420152225 7380857310809929065114169)
            ·
              refine ⟨5535642983107446798835627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7380857310809929065114169 5535642983107446798835627)
              ·
                refine ⟨8303464474661170198253441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535642983107446798835627 8303464474661170198253441)
                ·
                  refine ⟨6227598355995877648690081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8303464474661170198253441 6227598355995877648690081)
                  ·
                    refine ⟨4670698766996908236517561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6227598355995877648690081 4670698766996908236517561)
                    ·
                      refine ⟨3503024075247681177388171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4670698766996908236517561 3503024075247681177388171)
                      ·
                        rfl

theorem cell23_6822115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6822115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822115 prefixEnd_6822115 := by exact prefixLift 6822115
  have htrace : WordTrace (prefixWord ++ tailWord_6822115) baseStart_6822115 baseEnd_6822115 := by
    simpa [prefixWord, tailWord_6822115, baseEnd_6822115] using wordTrace_append hprefix tailTrace_6822115
  have hstable : (prefixWord ++ tailWord_6822115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822115).length < 2 ^ (prefixWord ++ tailWord_6822115).sum := by decide
  have hdescent : baseEnd_6822115 < baseStart_6822115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822207 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 1, 5]
def baseStart_6822207 : Nat := 118140960795 + 6822207 * 2 ^ 59
def prefixEnd_6822207 : Nat := 4983230072969 + 3 ^ 40 * 6822207 * 2
def baseEnd_6822207 : Nat := 1167690438489298272479249

theorem tailTrace_6822207 : CollatzResearch.WordTrace tailWord_6822207 prefixEnd_6822207 1167690438489298272479249 := by
  unfold tailWord_6822207
  simp only [CollatzResearch.WordTrace]
  refine ⟨248826331195316654039160875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165884220796877769359440583 248826331195316654039160875)
  ·
    refine ⟨373239496792974981058741313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248826331195316654039160875 373239496792974981058741313)
    ·
      refine ⟨279929622594731235794055985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373239496792974981058741313 279929622594731235794055985)
      ·
        refine ⟨209947216946048426845541989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279929622594731235794055985 209947216946048426845541989)
        ·
          refine ⟨39365103177384080033539123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209947216946048426845541989 39365103177384080033539123)
          ·
            refine ⟨59047654766076120050308685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39365103177384080033539123 59047654766076120050308685)
            ·
              refine ⟨22142870537278545018865757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59047654766076120050308685 22142870537278545018865757)
              ·
                refine ⟨8303576451479454382074659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22142870537278545018865757 8303576451479454382074659)
                ·
                  refine ⟨12455364677219181573111989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8303576451479454382074659 12455364677219181573111989)
                  ·
                    refine ⟨1167690438489298272479249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12455364677219181573111989 1167690438489298272479249)
                    ·
                      rfl

theorem cell23_6822207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 5].length) (baseStart_6822207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822207 prefixEnd_6822207 := by exact prefixLift 6822207
  have htrace : WordTrace (prefixWord ++ tailWord_6822207) baseStart_6822207 baseEnd_6822207 := by
    simpa [prefixWord, tailWord_6822207, baseEnd_6822207] using wordTrace_append hprefix tailTrace_6822207
  have hstable : (prefixWord ++ tailWord_6822207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822207).length < 2 ^ (prefixWord ++ tailWord_6822207).sum := by decide
  have hdescent : baseEnd_6822207 < baseStart_6822207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822244 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_6822244 : Nat := 118140960795 + 6822244 * 2 ^ 59
def prefixEnd_6822244 : Nat := 4983230072969 + 3 ^ 40 * 6822244 * 2
def baseEnd_6822244 : Nat := 3503090314252111172675077

theorem tailTrace_6822244 : CollatzResearch.WordTrace tailWord_6822244 prefixEnd_6822244 3503090314252111172675077 := by
  unfold tailWord_6822244
  simp only [CollatzResearch.WordTrace]
  refine ⟨124413840348091304679128893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165885120464121739572171857 124413840348091304679128893)
  ·
    refine ⟨46655190130534239254673335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124413840348091304679128893 46655190130534239254673335)
    ·
      refine ⟨69982785195801358882010003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46655190130534239254673335 69982785195801358882010003)
      ·
        refine ⟨104974177793702038323015005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69982785195801358882010003 104974177793702038323015005)
        ·
          refine ⟨39365316672638264371130627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104974177793702038323015005 39365316672638264371130627)
          ·
            refine ⟨59047975008957396556695941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39365316672638264371130627 59047975008957396556695941)
            ·
              refine ⟨11071495314179511854380489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59047975008957396556695941 11071495314179511854380489)
              ·
                refine ⟨8303621485634633890785367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11071495314179511854380489 8303621485634633890785367)
                ·
                  refine ⟨12455432228451950836178051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8303621485634633890785367 12455432228451950836178051)
                  ·
                    refine ⟨18683148342677926254267077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12455432228451950836178051 18683148342677926254267077)
                    ·
                      refine ⟨3503090314252111172675077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18683148342677926254267077 3503090314252111172675077)
                      ·
                        rfl

theorem cell23_6822244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_6822244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822244 prefixEnd_6822244 := by exact prefixLift 6822244
  have htrace : WordTrace (prefixWord ++ tailWord_6822244) baseStart_6822244 baseEnd_6822244 := by
    simpa [prefixWord, tailWord_6822244, baseEnd_6822244] using wordTrace_append hprefix tailTrace_6822244
  have hstable : (prefixWord ++ tailWord_6822244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822244).length < 2 ^ (prefixWord ++ tailWord_6822244).sum := by decide
  have hdescent : baseEnd_6822244 < baseStart_6822244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822357 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 9]
def baseStart_6822357 : Nat := 118140960795 + 6822357 * 2 ^ 59
def prefixEnd_6822357 : Nat := 4983230072969 + 3 ^ 40 * 6822357 * 2
def baseEnd_6822357 : Nat := 389238704174007692284673

theorem tailTrace_6822357 : CollatzResearch.WordTrace tailWord_6822357 prefixEnd_6822357 389238704174007692284673 := by
  unfold tailWord_6822357
  simp only [CollatzResearch.WordTrace]
  refine ⟨248831802144773229657121325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165887868096515486438080883 248831802144773229657121325)
  ·
    refine ⟨93311925804289961121420497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248831802144773229657121325 93311925804289961121420497)
    ·
      refine ⟨69983944353217470841065373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93311925804289961121420497 69983944353217470841065373)
      ·
        refine ⟨26243979132456551565399515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69983944353217470841065373 26243979132456551565399515)
        ·
          refine ⟨39365968698684827348099273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26243979132456551565399515 39365968698684827348099273)
          ·
            refine ⟨29524476524013620511074455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39365968698684827348099273 29524476524013620511074455)
            ·
              refine ⟨44286714786020430766611683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29524476524013620511074455 44286714786020430766611683)
              ·
                refine ⟨66430072179030646149917525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44286714786020430766611683 66430072179030646149917525)
                ·
                  refine ⟨389238704174007692284673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66430072179030646149917525 389238704174007692284673)
                  ·
                    rfl

theorem cell23_6822357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_6822357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822357 prefixEnd_6822357 := by exact prefixLift 6822357
  have htrace : WordTrace (prefixWord ++ tailWord_6822357) baseStart_6822357 baseEnd_6822357 := by
    simpa [prefixWord, tailWord_6822357, baseEnd_6822357] using wordTrace_append hprefix tailTrace_6822357
  have hstable : (prefixWord ++ tailWord_6822357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822357).length < 2 ^ (prefixWord ++ tailWord_6822357).sum := by decide
  have hdescent : baseEnd_6822357 < baseStart_6822357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822387 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 4, 5]
def baseStart_6822387 : Nat := 118140960795 + 6822387 * 2 ^ 59
def prefixEnd_6822387 : Nat := 4983230072969 + 3 ^ 40 * 6822387 * 2
def baseEnd_6822387 : Nat := 1167721247328568037728973

theorem tailTrace_6822387 : CollatzResearch.WordTrace tailWord_6822387 prefixEnd_6822387 1167721247328568037728973 := by
  unfold tailWord_6822387
  simp only [CollatzResearch.WordTrace]
  refine ⟨248832896334664544780713415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165888597556443029853808943 248832896334664544780713415)
  ·
    refine ⟨373249344501996817171070123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248832896334664544780713415 373249344501996817171070123)
    ·
      refine ⟨559874016752995225756605185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373249344501996817171070123 559874016752995225756605185)
      ·
        refine ⟨419905512564746419317453889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559874016752995225756605185 419905512564746419317453889)
        ·
          refine ⟨314929134423559814488090417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419905512564746419317453889 314929134423559814488090417)
          ·
            refine ⟨236196850817669860866067813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314929134423559814488090417 236196850817669860866067813)
            ·
              refine ⟨44286909528313098912387715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236196850817669860866067813 44286909528313098912387715)
              ·
                refine ⟨66430364292469648368581573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44286909528313098912387715 66430364292469648368581573)
                ·
                  refine ⟨12455693304838059069109045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66430364292469648368581573 12455693304838059069109045)
                  ·
                    refine ⟨1167721247328568037728973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12455693304838059069109045 1167721247328568037728973)
                    ·
                      rfl

theorem cell23_6822387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 5].length) (baseStart_6822387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822387 prefixEnd_6822387 := by exact prefixLift 6822387
  have htrace : WordTrace (prefixWord ++ tailWord_6822387) baseStart_6822387 baseEnd_6822387 := by
    simpa [prefixWord, tailWord_6822387, baseEnd_6822387] using wordTrace_append hprefix tailTrace_6822387
  have hstable : (prefixWord ++ tailWord_6822387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822387).length < 2 ^ (prefixWord ++ tailWord_6822387).sum := by decide
  have hdescent : baseEnd_6822387 < baseStart_6822387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822394 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2]
def baseStart_6822394 : Nat := 118140960795 + 6822394 * 2 ^ 59
def prefixEnd_6822394 : Nat := 4983230072969 + 3 ^ 40 * 6822394 * 2
def baseEnd_6822394 : Nat := 3503167336350285585799387

theorem tailTrace_6822394 : CollatzResearch.WordTrace tailWord_6822394 prefixEnd_6822394 3503167336350285585799387 := by
  unfold tailWord_6822394
  simp only [CollatzResearch.WordTrace]
  refine ⟨62208287911409796244054559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165888767763759456650812157 62208287911409796244054559)
  ·
    refine ⟨93312431867114694366081839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62208287911409796244054559 93312431867114694366081839)
    ·
      refine ⟨139968647800672041549122759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93312431867114694366081839 139968647800672041549122759)
      ·
        refine ⟨209952971701008062323684139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139968647800672041549122759 209952971701008062323684139)
        ·
          refine ⟨314929457551512093485526209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209952971701008062323684139 314929457551512093485526209)
          ·
            refine ⟨236197093163634070114144657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314929457551512093485526209 236197093163634070114144657)
            ·
              refine ⟨177147819872725552585608493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236197093163634070114144657 177147819872725552585608493)
              ·
                refine ⟨66430432452272082219603185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177147819872725552585608493 66430432452272082219603185)
                ·
                  refine ⟨49822824339204061664702389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66430432452272082219603185 49822824339204061664702389)
                  ·
                    refine ⟨4670889781800380781065849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49822824339204061664702389 4670889781800380781065849)
                    ·
                      refine ⟨3503167336350285585799387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4670889781800380781065849 3503167336350285585799387)
                      ·
                        rfl

theorem cell23_6822394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2].length) (baseStart_6822394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822394 prefixEnd_6822394 := by exact prefixLift 6822394
  have htrace : WordTrace (prefixWord ++ tailWord_6822394) baseStart_6822394 baseEnd_6822394 := by
    simpa [prefixWord, tailWord_6822394, baseEnd_6822394] using wordTrace_append hprefix tailTrace_6822394
  have hstable : (prefixWord ++ tailWord_6822394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822394).length < 2 ^ (prefixWord ++ tailWord_6822394).sum := by decide
  have hdescent : baseEnd_6822394 < baseStart_6822394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822397 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_6822397 : Nat := 118140960795 + 6822397 * 2 ^ 59
def prefixEnd_6822397 : Nat := 4983230072969 + 3 ^ 40 * 6822397 * 2
def baseEnd_6822397 : Nat := 3503168876792249074061873

theorem tailTrace_6822397 : CollatzResearch.WordTrace tailWord_6822397 prefixEnd_6822397 3503168876792249074061873 := by
  unfold tailWord_6822397
  simp only [CollatzResearch.WordTrace]
  refine ⟨248833261064628316488577445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165888840709752210992384963 248833261064628316488577445)
  ·
    refine ⟨46656236449617809341608271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248833261064628316488577445 46656236449617809341608271)
    ·
      refine ⟨69984354674426714012412407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46656236449617809341608271 69984354674426714012412407)
      ·
        refine ⟨104976532011640071018618611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69984354674426714012412407 104976532011640071018618611)
        ·
          refine ⟨157464798017460106527927917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104976532011640071018618611 157464798017460106527927917)
          ·
            refine ⟨59049299256547539947972969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157464798017460106527927917 59049299256547539947972969)
            ·
              refine ⟨44286974442410654960979727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59049299256547539947972969 44286974442410654960979727)
              ·
                refine ⟨66430461663615982441469591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44286974442410654960979727 66430461663615982441469591)
                ·
                  refine ⟨99645692495423973662204387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66430461663615982441469591 99645692495423973662204387)
                  ·
                    refine ⟨149468538743135960493306581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99645692495423973662204387 149468538743135960493306581)
                    ·
                      refine ⟨3503168876792249074061873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149468538743135960493306581 3503168876792249074061873)
                      ·
                        rfl

theorem cell23_6822397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_6822397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822397 prefixEnd_6822397 := by exact prefixLift 6822397
  have htrace : WordTrace (prefixWord ++ tailWord_6822397) baseStart_6822397 baseEnd_6822397 := by
    simpa [prefixWord, tailWord_6822397, baseEnd_6822397] using wordTrace_append hprefix tailTrace_6822397
  have hstable : (prefixWord ++ tailWord_6822397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822397).length < 2 ^ (prefixWord ++ tailWord_6822397).sum := by decide
  have hdescent : baseEnd_6822397 < baseStart_6822397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822402 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_6822402 : Nat := 118140960795 + 6822402 * 2 ^ 59
def prefixEnd_6822402 : Nat := 4983230072969 + 3 ^ 40 * 6822402 * 2
def baseEnd_6822402 : Nat := 3503171444195521554499351

theorem tailTrace_6822402 : CollatzResearch.WordTrace tailWord_6822402 prefixEnd_6822402 3503171444195521554499351 := by
  unfold tailWord_6822402
  simp only [CollatzResearch.WordTrace]
  refine ⟨62208360857402550585627365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165888962286406801561672973 62208360857402550585627365)
  ·
    refine ⟨11664067660762978234805131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62208360857402550585627365 11664067660762978234805131)
    ·
      refine ⟨17496101491144467352207697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11664067660762978234805131 17496101491144467352207697)
      ·
        refine ⟨13122076118358350514155773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17496101491144467352207697 13122076118358350514155773)
        ·
          refine ⟨4920778544384381442808415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13122076118358350514155773 4920778544384381442808415)
          ·
            refine ⟨7381167816576572164212623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920778544384381442808415 7381167816576572164212623)
            ·
              refine ⟨11071751724864858246318935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381167816576572164212623 11071751724864858246318935)
              ·
                refine ⟨16607627587297287369478403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11071751724864858246318935 16607627587297287369478403)
                ·
                  refine ⟨24911441380945931054217605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16607627587297287369478403 24911441380945931054217605)
                  ·
                    refine ⟨4670895258927362072665801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24911441380945931054217605 4670895258927362072665801)
                    ·
                      refine ⟨3503171444195521554499351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4670895258927362072665801 3503171444195521554499351)
                      ·
                        rfl

theorem cell23_6822402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_6822402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822402 prefixEnd_6822402 := by exact prefixLift 6822402
  have htrace : WordTrace (prefixWord ++ tailWord_6822402) baseStart_6822402 baseEnd_6822402 := by
    simpa [prefixWord, tailWord_6822402, baseEnd_6822402] using wordTrace_append hprefix tailTrace_6822402
  have hstable : (prefixWord ++ tailWord_6822402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822402).length < 2 ^ (prefixWord ++ tailWord_6822402).sum := by decide
  have hdescent : baseEnd_6822402 < baseStart_6822402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822404 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_6822404 : Nat := 118140960795 + 6822404 * 2 ^ 59
def prefixEnd_6822404 : Nat := 4983230072969 + 3 ^ 40 * 6822404 * 2
def baseEnd_6822404 : Nat := 1167724157052276848891447

theorem tailTrace_6822404 : CollatzResearch.WordTrace tailWord_6822404 prefixEnd_6822404 1167724157052276848891447 := by
  unfold tailWord_6822404
  simp only [CollatzResearch.WordTrace]
  refine ⟨124416758187801478342041133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165889010917068637789388177 124416758187801478342041133)
  ·
    refine ⟨46656284320425554378265425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124416758187801478342041133 46656284320425554378265425)
    ·
      refine ⟨34992213240319165783699069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46656284320425554378265425 34992213240319165783699069)
      ·
        refine ⟨13122079965119687168887151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34992213240319165783699069 13122079965119687168887151)
        ·
          refine ⟨19683119947679530753330727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13122079965119687168887151 19683119947679530753330727)
          ·
            refine ⟨29524679921519296129996091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19683119947679530753330727 29524679921519296129996091)
            ·
              refine ⟨44287019882278944194994137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29524679921519296129996091 44287019882278944194994137)
              ·
                refine ⟨33215264911709208146245603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44287019882278944194994137 33215264911709208146245603)
                ·
                  refine ⟨49822897367563812219368405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33215264911709208146245603 49822897367563812219368405)
                  ·
                    refine ⟨1167724157052276848891447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49822897367563812219368405 1167724157052276848891447)
                    ·
                      rfl

theorem cell23_6822404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_6822404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822404 prefixEnd_6822404 := by exact prefixLift 6822404
  have htrace : WordTrace (prefixWord ++ tailWord_6822404) baseStart_6822404 baseEnd_6822404 := by
    simpa [prefixWord, tailWord_6822404, baseEnd_6822404] using wordTrace_append hprefix tailTrace_6822404
  have hstable : (prefixWord ++ tailWord_6822404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822404).length < 2 ^ (prefixWord ++ tailWord_6822404).sum := by decide
  have hdescent : baseEnd_6822404 < baseStart_6822404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822424 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_6822424 : Nat := 118140960795 + 6822424 * 2 ^ 59
def prefixEnd_6822424 : Nat := 4983230072969 + 3 ^ 40 * 6822424 * 2
def baseEnd_6822424 : Nat := 3503182740769920468424249

theorem tailTrace_6822424 : CollatzResearch.WordTrace tailWord_6822424 prefixEnd_6822424 3503182740769920468424249 := by
  unfold tailWord_6822424
  simp only [CollatzResearch.WordTrace]
  refine ⟨124417122917765250049905163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165889497223687000066540217 124417122917765250049905163)
  ·
    refine ⟨186625684376647875074857745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124417122917765250049905163 186625684376647875074857745)
    ·
      refine ⟨139969263282485906306143309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186625684376647875074857745 139969263282485906306143309)
      ·
        refine ⟨52488473730932214864803741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139969263282485906306143309 52488473730932214864803741)
        ·
          refine ⟨19683177649099580574301403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52488473730932214864803741 19683177649099580574301403)
          ·
            refine ⟨29524766473649370861452105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19683177649099580574301403 29524766473649370861452105)
            ·
              refine ⟨22143574855237028146089079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29524766473649370861452105 22143574855237028146089079)
              ·
                refine ⟨33215362282855542219133619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22143574855237028146089079 33215362282855542219133619)
                ·
                  refine ⟨49823043424283313328700429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33215362282855542219133619 49823043424283313328700429)
                  ·
                    refine ⟨18683641284106242498262661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49823043424283313328700429 18683641284106242498262661)
                    ·
                      refine ⟨3503182740769920468424249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18683641284106242498262661 3503182740769920468424249)
                      ·
                        rfl

theorem cell23_6822424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_6822424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822424 prefixEnd_6822424 := by exact prefixLift 6822424
  have htrace : WordTrace (prefixWord ++ tailWord_6822424) baseStart_6822424 baseEnd_6822424 := by
    simpa [prefixWord, tailWord_6822424, baseEnd_6822424] using wordTrace_append hprefix tailTrace_6822424
  have hstable : (prefixWord ++ tailWord_6822424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822424).length < 2 ^ (prefixWord ++ tailWord_6822424).sum := by decide
  have hdescent : baseEnd_6822424 < baseStart_6822424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822437 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_6822437 : Nat := 118140960795 + 6822437 * 2 ^ 59
def prefixEnd_6822437 : Nat := 4983230072969 + 3 ^ 40 * 6822437 * 2
def baseEnd_6822437 : Nat := 3503189416018428917561689

theorem tailTrace_6822437 : CollatzResearch.WordTrace tailWord_6822437 prefixEnd_6822437 3503189416018428917561689 := by
  unfold tailWord_6822437
  simp only [CollatzResearch.WordTrace]
  refine ⟨248834719984483403320033565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165889813322988935546689043 248834719984483403320033565)
  ·
    refine ⟨93313019994181276245012587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248834719984483403320033565 93313019994181276245012587)
    ·
      refine ⟨139969529991271914367518881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93313019994181276245012587 139969529991271914367518881)
      ·
        refine ⟨104977147493453935775639161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139969529991271914367518881 104977147493453935775639161)
        ·
          refine ⟨78732860620090451831729371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104977147493453935775639161 78732860620090451831729371)
          ·
            refine ⟨118099290930135677747594057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78732860620090451831729371 118099290930135677747594057)
            ·
              refine ⟨88574468197601758310695543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118099290930135677747594057 88574468197601758310695543)
              ·
                refine ⟨132861702296402637466043315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88574468197601758310695543 132861702296402637466043315)
                ·
                  refine ⟨199292553444603956199064973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132861702296402637466043315 199292553444603956199064973)
                  ·
                    refine ⟨74734707541726483574649365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199292553444603956199064973 74734707541726483574649365)
                    ·
                      refine ⟨3503189416018428917561689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74734707541726483574649365 3503189416018428917561689)
                      ·
                        rfl

theorem cell23_6822437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_6822437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822437 prefixEnd_6822437 := by exact prefixLift 6822437
  have htrace : WordTrace (prefixWord ++ tailWord_6822437) baseStart_6822437 baseEnd_6822437 := by
    simpa [prefixWord, tailWord_6822437, baseEnd_6822437] using wordTrace_append hprefix tailTrace_6822437
  have hstable : (prefixWord ++ tailWord_6822437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822437).length < 2 ^ (prefixWord ++ tailWord_6822437).sum := by decide
  have hdescent : baseEnd_6822437 < baseStart_6822437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822467 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 6]
def baseStart_6822467 : Nat := 118140960795 + 6822467 * 2 ^ 59
def prefixEnd_6822467 : Nat := 4983230072969 + 3 ^ 40 * 6822467 * 2
def baseEnd_6822467 : Nat := 3503204820438063800186551

theorem tailTrace_6822467 : CollatzResearch.WordTrace tailWord_6822467 prefixEnd_6822467 3503204820438063800186551 := by
  unfold tailWord_6822467
  simp only [CollatzResearch.WordTrace]
  refine ⟨248835814174374718443625655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165890542782916478962417103 248835814174374718443625655)
  ·
    refine ⟨373253721261562077665438483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248835814174374718443625655 373253721261562077665438483)
    ·
      refine ⟨559880581892343116498157725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373253721261562077665438483 559880581892343116498157725)
      ·
        refine ⟨209955218209628668686809147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559880581892343116498157725 209955218209628668686809147)
        ·
          refine ⟨314932827314443003030213721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209955218209628668686809147 314932827314443003030213721)
          ·
            refine ⟨236199620485832252272660291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314932827314443003030213721 236199620485832252272660291)
            ·
              refine ⟨354299430728748378408990437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236199620485832252272660291 354299430728748378408990437)
              ·
                refine ⟨66431143261640320951685707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354299430728748378408990437 66431143261640320951685707)
                ·
                  refine ⟨99646714892460481427528561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66431143261640320951685707 99646714892460481427528561)
                  ·
                    refine ⟨74735036169345361070646421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99646714892460481427528561 74735036169345361070646421)
                    ·
                      refine ⟨3503204820438063800186551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74735036169345361070646421 3503204820438063800186551)
                      ·
                        rfl

theorem cell23_6822467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_6822467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822467 prefixEnd_6822467 := by exact prefixLift 6822467
  have htrace : WordTrace (prefixWord ++ tailWord_6822467) baseStart_6822467 baseEnd_6822467 := by
    simpa [prefixWord, tailWord_6822467, baseEnd_6822467] using wordTrace_append hprefix tailTrace_6822467
  have hstable : (prefixWord ++ tailWord_6822467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822467).length < 2 ^ (prefixWord ++ tailWord_6822467).sum := by decide
  have hdescent : baseEnd_6822467 < baseStart_6822467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822524 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_6822524 : Nat := 118140960795 + 6822524 * 2 ^ 59
def prefixEnd_6822524 : Nat := 4983230072969 + 3 ^ 40 * 6822524 * 2
def baseEnd_6822524 : Nat := 1167744696278456692391263

theorem tailTrace_6822524 : CollatzResearch.WordTrace tailWord_6822524 prefixEnd_6822524 1167744696278456692391263 := by
  unfold tailWord_6822524
  simp only [CollatzResearch.WordTrace]
  refine ⟨124418946567584108589225313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165891928756778811452300417 124418946567584108589225313)
  ·
    refine ⟨93314209925688081441918985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124418946567584108589225313 93314209925688081441918985)
    ·
      refine ⟨69985657444266061081439239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93314209925688081441918985 69985657444266061081439239)
      ·
        refine ⟨104978486166399091622158859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69985657444266061081439239 104978486166399091622158859)
        ·
          refine ⟨157467729249598637433238289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104978486166399091622158859 157467729249598637433238289)
          ·
            refine ⟨118100796937198978074928717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157467729249598637433238289 118100796937198978074928717)
            ·
              refine ⟨44287798851449616778098269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118100796937198978074928717 44287798851449616778098269)
              ·
                refine ⟨16607924569293606291786851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44287798851449616778098269 16607924569293606291786851)
                ·
                  refine ⟨24911886853940409437680277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16607924569293606291786851 24911886853940409437680277)
                  ·
                    refine ⟨1167744696278456692391263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24911886853940409437680277 1167744696278456692391263)
                    ·
                      rfl

theorem cell23_6822524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_6822524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822524 prefixEnd_6822524 := by exact prefixLift 6822524
  have htrace : WordTrace (prefixWord ++ tailWord_6822524) baseStart_6822524 baseEnd_6822524 := by
    simpa [prefixWord, tailWord_6822524, baseEnd_6822524] using wordTrace_append hprefix tailTrace_6822524
  have hstable : (prefixWord ++ tailWord_6822524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822524).length < 2 ^ (prefixWord ++ tailWord_6822524).sum := by decide
  have hdescent : baseEnd_6822524 < baseStart_6822524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822558 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_6822558 : Nat := 118140960795 + 6822558 * 2 ^ 59
def prefixEnd_6822558 : Nat := 4983230072969 + 3 ^ 40 * 6822558 * 2
def baseEnd_6822558 : Nat := 1167750515725874314716211

theorem tailTrace_6822558 : CollatzResearch.WordTrace tailWord_6822558 prefixEnd_6822558 1167750515725874314716211 := by
  unfold tailWord_6822558
  simp only [CollatzResearch.WordTrace]
  refine ⟨31104891652130630123148541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165892755478030027323458885 31104891652130630123148541)
  ·
    refine ⟨11664334369548986296180703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31104891652130630123148541 11664334369548986296180703)
    ·
      refine ⟨17496501554323479444271055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11664334369548986296180703 17496501554323479444271055)
      ·
        refine ⟨26244752331485219166406583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17496501554323479444271055 26244752331485219166406583)
        ·
          refine ⟨39367128497227828749609875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26244752331485219166406583 39367128497227828749609875)
          ·
            refine ⟨59050692745841743124414813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39367128497227828749609875 59050692745841743124414813)
            ·
              refine ⟨22144009779690653671655555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59050692745841743124414813 22144009779690653671655555)
              ·
                refine ⟨33216014669535980507483333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22144009779690653671655555 33216014669535980507483333)
                ·
                  refine ⟨6228002750537996345153125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33216014669535980507483333 6228002750537996345153125)
                  ·
                    refine ⟨1167750515725874314716211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6228002750537996345153125 1167750515725874314716211)
                    ·
                      rfl

theorem cell23_6822558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_6822558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822558 prefixEnd_6822558 := by exact prefixLift 6822558
  have htrace : WordTrace (prefixWord ++ tailWord_6822558) baseStart_6822558 baseEnd_6822558 := by
    simpa [prefixWord, tailWord_6822558, baseEnd_6822558] using wordTrace_append hprefix tailTrace_6822558
  have hstable : (prefixWord ++ tailWord_6822558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822558).length < 2 ^ (prefixWord ++ tailWord_6822558).sum := by decide
  have hdescent : baseEnd_6822558 < baseStart_6822558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822582 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_6822582 : Nat := 118140960795 + 6822582 * 2 ^ 59
def prefixEnd_6822582 : Nat := 4983230072969 + 3 ^ 40 * 6822582 * 2
def baseEnd_6822582 : Nat := 3503263870713330850248523

theorem tailTrace_6822582 : CollatzResearch.WordTrace tailWord_6822582 prefixEnd_6822582 3503263870713330850248523 := by
  unfold tailWord_6822582
  simp only [CollatzResearch.WordTrace]
  refine ⟨15552500535559880817753875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165893339045972062056041333 15552500535559880817753875)
  ·
    refine ⟨23328750803339821226630813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15552500535559880817753875 23328750803339821226630813)
    ·
      refine ⟨8748281551252432959986555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23328750803339821226630813 8748281551252432959986555)
      ·
        refine ⟨13122422326878649439979833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8748281551252432959986555 13122422326878649439979833)
        ·
          refine ⟨9841816745158987079984875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13122422326878649439979833 9841816745158987079984875)
          ·
            refine ⟨14762725117738480619977313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9841816745158987079984875 14762725117738480619977313)
            ·
              refine ⟨11072043838303860464982985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14762725117738480619977313 11072043838303860464982985)
              ·
                refine ⟨8304032878727895348737239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11072043838303860464982985 8304032878727895348737239)
                ·
                  refine ⟨12456049318091843023105859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8304032878727895348737239 12456049318091843023105859)
                  ·
                    refine ⟨18684073977137764534658789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12456049318091843023105859 18684073977137764534658789)
                    ·
                      refine ⟨3503263870713330850248523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18684073977137764534658789 3503263870713330850248523)
                      ·
                        rfl

theorem cell23_6822582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_6822582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822582 prefixEnd_6822582 := by exact prefixLift 6822582
  have htrace : WordTrace (prefixWord ++ tailWord_6822582) baseStart_6822582 baseEnd_6822582 := by
    simpa [prefixWord, tailWord_6822582, baseEnd_6822582] using wordTrace_append hprefix tailTrace_6822582
  have hstable : (prefixWord ++ tailWord_6822582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822582).length < 2 ^ (prefixWord ++ tailWord_6822582).sum := by decide
  have hdescent : baseEnd_6822582 < baseStart_6822582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822605 : List Nat := [1, 6, 2, 1, 3, 1, 9]
def baseStart_6822605 : Nat := 118140960795 + 6822605 * 2 ^ 59
def prefixEnd_6822605 : Nat := 4983230072969 + 3 ^ 40 * 6822605 * 2
def baseEnd_6822605 : Nat := 43250317046523262472357

theorem tailTrace_6822605 : CollatzResearch.WordTrace tailWord_6822605 prefixEnd_6822605 43250317046523262472357 := by
  unfold tailWord_6822605
  simp only [CollatzResearch.WordTrace]
  refine ⟨248840847447874768012149269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165893898298583178674766179 248840847447874768012149269)
  ·
    refine ⟨11664414724119129750569497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248840847447874768012149269 11664414724119129750569497)
    ·
      refine ⟨8748311043089347312927123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11664414724119129750569497 8748311043089347312927123)
      ·
        refine ⟨13122466564634020969390685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8748311043089347312927123 13122466564634020969390685)
        ·
          refine ⟨4920924961737757863521507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13122466564634020969390685 4920924961737757863521507)
          ·
            refine ⟨7381387442606636795282261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920924961737757863521507 7381387442606636795282261)
            ·
              refine ⟨43250317046523262472357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7381387442606636795282261 43250317046523262472357)
              ·
                rfl

theorem cell23_6822605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 9].length) (baseStart_6822605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822605 prefixEnd_6822605 := by exact prefixLift 6822605
  have htrace : WordTrace (prefixWord ++ tailWord_6822605) baseStart_6822605 baseEnd_6822605 := by
    simpa [prefixWord, tailWord_6822605, baseEnd_6822605] using wordTrace_append hprefix tailTrace_6822605
  have hstable : (prefixWord ++ tailWord_6822605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822605).length < 2 ^ (prefixWord ++ tailWord_6822605).sum := by decide
  have hdescent : baseEnd_6822605 < baseStart_6822605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822624 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_6822624 : Nat := 118140960795 + 6822624 * 2 ^ 59
def prefixEnd_6822624 : Nat := 4983230072969 + 3 ^ 40 * 6822624 * 2
def baseEnd_6822624 : Nat := 3503285436900819685923329

theorem tailTrace_6822624 : CollatzResearch.WordTrace tailWord_6822624 prefixEnd_6822624 3503285436900819685923329 := by
  unfold tailWord_6822624
  simp only [CollatzResearch.WordTrace]
  refine ⟨124420770217402967128545463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165894360289870622838060617 124420770217402967128545463)
  ·
    refine ⟨186631155326104450692818195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124420770217402967128545463 186631155326104450692818195)
    ·
      refine ⟨279946732989156676039227293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186631155326104450692818195 279946732989156676039227293)
      ·
        refine ⟨104980024870933753514710235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279946732989156676039227293 104980024870933753514710235)
        ·
          refine ⟨157470037306400630272065353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104980024870933753514710235 157470037306400630272065353)
          ·
            refine ⟨118102527979800472704049015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157470037306400630272065353 118102527979800472704049015)
            ·
              refine ⟨177153791969700709056073523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118102527979800472704049015 177153791969700709056073523)
              ·
                refine ⟨265730687954551063584110285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177153791969700709056073523 265730687954551063584110285)
                ·
                  refine ⟨99649007982956648844041357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265730687954551063584110285 99649007982956648844041357)
                  ·
                    refine ⟨37368377993608743316515509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99649007982956648844041357 37368377993608743316515509)
                    ·
                      refine ⟨3503285436900819685923329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37368377993608743316515509 3503285436900819685923329)
                      ·
                        rfl

theorem cell23_6822624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_6822624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822624 prefixEnd_6822624 := by exact prefixLift 6822624
  have htrace : WordTrace (prefixWord ++ tailWord_6822624) baseStart_6822624 baseEnd_6822624 := by
    simpa [prefixWord, tailWord_6822624, baseEnd_6822624] using wordTrace_append hprefix tailTrace_6822624
  have hstable : (prefixWord ++ tailWord_6822624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822624).length < 2 ^ (prefixWord ++ tailWord_6822624).sum := by decide
  have hdescent : baseEnd_6822624 < baseStart_6822624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822642 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 1, 3, 2]
def baseStart_6822642 : Nat := 118140960795 + 6822642 * 2 ^ 59
def prefixEnd_6822642 : Nat := 4983230072969 + 3 ^ 40 * 6822642 * 2
def baseEnd_6822642 : Nat := 3503294679552600615498247

theorem tailTrace_6822642 : CollatzResearch.WordTrace tailWord_6822642 prefixEnd_6822642 3503294679552600615498247 := by
  unfold tailWord_6822642
  simp only [CollatzResearch.WordTrace]
  refine ⟨62210549237185180832811545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165894797965827148887497453 62210549237185180832811545)
  ·
    refine ⟨46657911927888885624608659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62210549237185180832811545 46657911927888885624608659)
    ·
      refine ⟨69986867891833328436912989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46657911927888885624608659 69986867891833328436912989)
      ·
        refine ⟨26245075459437498163842371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69986867891833328436912989 26245075459437498163842371)
        ·
          refine ⟨39367613189156247245763557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26245075459437498163842371 39367613189156247245763557)
          ·
            refine ⟨7381427472966796358580667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39367613189156247245763557 7381427472966796358580667)
            ·
              refine ⟨11072141209450194537871001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381427472966796358580667 11072141209450194537871001)
              ·
                refine ⟨8304105907087645903403251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11072141209450194537871001 8304105907087645903403251)
                ·
                  refine ⟨12456158860631468855104877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8304105907087645903403251 12456158860631468855104877)
                  ·
                    refine ⟨4671059572736800820664329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12456158860631468855104877 4671059572736800820664329)
                    ·
                      refine ⟨3503294679552600615498247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671059572736800820664329 3503294679552600615498247)
                      ·
                        rfl

theorem cell23_6822642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_6822642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822642 prefixEnd_6822642 := by exact prefixLift 6822642
  have htrace : WordTrace (prefixWord ++ tailWord_6822642) baseStart_6822642 baseEnd_6822642 := by
    simpa [prefixWord, tailWord_6822642, baseEnd_6822642] using wordTrace_append hprefix tailTrace_6822642
  have hstable : (prefixWord ++ tailWord_6822642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822642).length < 2 ^ (prefixWord ++ tailWord_6822642).sum := by decide
  have hdescent : baseEnd_6822642 < baseStart_6822642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822658 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_6822658 : Nat := 118140960795 + 6822658 * 2 ^ 59
def prefixEnd_6822658 : Nat := 4983230072969 + 3 ^ 40 * 6822658 * 2
def baseEnd_6822658 : Nat := 3503302895243072552898173

theorem tailTrace_6822658 : CollatzResearch.WordTrace tailWord_6822658 prefixEnd_6822658 3503302895243072552898173 := by
  unfold tailWord_6822658
  simp only [CollatzResearch.WordTrace]
  refine ⟨62210695129170689515957157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165895187011121838709219085 62210695129170689515957157)
  ·
    refine ⟨11664505336719504284241967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62210695129170689515957157 11664505336719504284241967)
    ·
      refine ⟨17496758005079256426362951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11664505336719504284241967 17496758005079256426362951)
      ·
        refine ⟨26245137007618884639544427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17496758005079256426362951 26245137007618884639544427)
        ·
          refine ⟨39367705511428326959316641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26245137007618884639544427 39367705511428326959316641)
          ·
            refine ⟨29525779133571245219487481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39367705511428326959316641 29525779133571245219487481)
            ·
              refine ⟨22144334350178433914615611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29525779133571245219487481 22144334350178433914615611)
              ·
                refine ⟨33216501525267650871923417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22144334350178433914615611 33216501525267650871923417)
                ·
                  refine ⟨24912376143950738153942563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33216501525267650871923417 24912376143950738153942563)
                  ·
                    refine ⟨37368564215926107230913845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24912376143950738153942563 37368564215926107230913845)
                    ·
                      refine ⟨3503302895243072552898173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37368564215926107230913845 3503302895243072552898173)
                      ·
                        rfl

theorem cell23_6822658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_6822658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822658 prefixEnd_6822658 := by exact prefixLift 6822658
  have htrace : WordTrace (prefixWord ++ tailWord_6822658) baseStart_6822658 baseEnd_6822658 := by
    simpa [prefixWord, tailWord_6822658, baseEnd_6822658] using wordTrace_append hprefix tailTrace_6822658
  have hstable : (prefixWord ++ tailWord_6822658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822658).length < 2 ^ (prefixWord ++ tailWord_6822658).sum := by decide
  have hdescent : baseEnd_6822658 < baseStart_6822658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822671 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 3]
def baseStart_6822671 : Nat := 118140960795 + 6822671 * 2 ^ 59
def prefixEnd_6822671 : Nat := 4983230072969 + 3 ^ 40 * 6822671 * 2
def baseEnd_6822671 : Nat := 3503309570491581002035613

theorem tailTrace_6822671 : CollatzResearch.WordTrace tailWord_6822671 prefixEnd_6822671 3503309570491581002035613 := by
  unfold tailWord_6822671
  simp only [CollatzResearch.WordTrace]
  refine ⟨248843254665635661284051867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165895503110423774189367911 248843254665635661284051867)
  ·
    refine ⟨373264881998453491926077801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248843254665635661284051867 373264881998453491926077801)
    ·
      refine ⟨279948661498840118944558351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373264881998453491926077801 279948661498840118944558351)
      ·
        refine ⟨419922992248260178416837527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279948661498840118944558351 419922992248260178416837527)
        ·
          refine ⟨629884488372390267625256291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419922992248260178416837527 629884488372390267625256291)
          ·
            refine ⟨944826732558585401437884437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629884488372390267625256291 944826732558585401437884437)
            ·
              refine ⟨44288753088683690692400833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 944826732558585401437884437 44288753088683690692400833)
              ·
                refine ⟨33216564816512768019300625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44288753088683690692400833 33216564816512768019300625)
                ·
                  refine ⟨24912423612384576014475469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33216564816512768019300625 24912423612384576014475469)
                  ·
                    refine ⟨9342158854644216005428301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24912423612384576014475469 9342158854644216005428301)
                    ·
                      refine ⟨3503309570491581002035613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9342158854644216005428301 3503309570491581002035613)
                      ·
                        rfl

theorem cell23_6822671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 3].length) (baseStart_6822671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822671 prefixEnd_6822671 := by exact prefixLift 6822671
  have htrace : WordTrace (prefixWord ++ tailWord_6822671) baseStart_6822671 baseEnd_6822671 := by
    simpa [prefixWord, tailWord_6822671, baseEnd_6822671] using wordTrace_append hprefix tailTrace_6822671
  have hstable : (prefixWord ++ tailWord_6822671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822671).length < 2 ^ (prefixWord ++ tailWord_6822671).sum := by decide
  have hdescent : baseEnd_6822671 < baseStart_6822671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822685 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_6822685 : Nat := 118140960795 + 6822685 * 2 ^ 59
def prefixEnd_6822685 : Nat := 4983230072969 + 3 ^ 40 * 6822685 * 2
def baseEnd_6822685 : Nat := 3503316759220743947260549

theorem tailTrace_6822685 : CollatzResearch.WordTrace tailWord_6822685 prefixEnd_6822685 3503316759220743947260549 := by
  unfold tailWord_6822685
  simp only [CollatzResearch.WordTrace]
  refine ⟨248843765287584941675061509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165895843525056627783374339 248843765287584941675061509)
  ·
    refine ⟨46658205991422176564074033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248843765287584941675061509 46658205991422176564074033)
    ·
      refine ⟨34993654493566632423055525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46658205991422176564074033 34993654493566632423055525)
      ·
        refine ⟨6561310217543743579322911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34993654493566632423055525 6561310217543743579322911)
        ·
          refine ⟨9841965326315615368984367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6561310217543743579322911 9841965326315615368984367)
          ·
            refine ⟨14762947989473423053476551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9841965326315615368984367 14762947989473423053476551)
            ·
              refine ⟨22144421984210134580214827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14762947989473423053476551 22144421984210134580214827)
              ·
                refine ⟨33216632976315201870322241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22144421984210134580214827 33216632976315201870322241)
                ·
                  refine ⟨24912474732236401402741681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33216632976315201870322241 24912474732236401402741681)
                  ·
                    refine ⟨18684356049177301052056261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24912474732236401402741681 18684356049177301052056261)
                    ·
                      refine ⟨3503316759220743947260549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18684356049177301052056261 3503316759220743947260549)
                      ·
                        rfl

theorem cell23_6822685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_6822685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822685 prefixEnd_6822685 := by exact prefixLift 6822685
  have htrace : WordTrace (prefixWord ++ tailWord_6822685) baseStart_6822685 baseEnd_6822685 := by
    simpa [prefixWord, tailWord_6822685, baseEnd_6822685] using wordTrace_append hprefix tailTrace_6822685
  have hstable : (prefixWord ++ tailWord_6822685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822685).length < 2 ^ (prefixWord ++ tailWord_6822685).sum := by decide
  have hdescent : baseEnd_6822685 < baseStart_6822685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822688 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 3]
def baseStart_6822688 : Nat := 118140960795 + 6822688 * 2 ^ 59
def prefixEnd_6822688 : Nat := 4983230072969 + 3 ^ 40 * 6822688 * 2
def baseEnd_6822688 : Nat := 3503318299662707435523035

theorem tailTrace_6822688 : CollatzResearch.WordTrace tailWord_6822688 prefixEnd_6822688 3503318299662707435523035 := by
  unfold tailWord_6822688
  simp only [CollatzResearch.WordTrace]
  refine ⟨124421937353287036593710359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165895916471049382124947145 124421937353287036593710359)
  ·
    refine ⟨186632906029930554890565539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124421937353287036593710359 186632906029930554890565539)
    ·
      refine ⟨279949359044895832335848309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186632906029930554890565539 279949359044895832335848309)
      ·
        refine ⟨26245252410458984281485779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279949359044895832335848309 26245252410458984281485779)
        ·
          refine ⟨39367878615688476422228669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26245252410458984281485779 39367878615688476422228669)
          ·
            refine ⟨14762954480883178658335751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39367878615688476422228669 14762954480883178658335751)
            ·
              refine ⟨22144431721324767987503627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14762954480883178658335751 22144431721324767987503627)
              ·
                refine ⟨33216647581987151981255441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22144431721324767987503627 33216647581987151981255441)
                ·
                  refine ⟨24912485686490363985941581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33216647581987151981255441 24912485686490363985941581)
                  ·
                    refine ⟨9342182132433886494728093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24912485686490363985941581 9342182132433886494728093)
                    ·
                      refine ⟨3503318299662707435523035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9342182132433886494728093 3503318299662707435523035)
                      ·
                        rfl

theorem cell23_6822688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_6822688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822688 prefixEnd_6822688 := by exact prefixLift 6822688
  have htrace : WordTrace (prefixWord ++ tailWord_6822688) baseStart_6822688 baseEnd_6822688 := by
    simpa [prefixWord, tailWord_6822688, baseEnd_6822688] using wordTrace_append hprefix tailTrace_6822688
  have hstable : (prefixWord ++ tailWord_6822688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822688).length < 2 ^ (prefixWord ++ tailWord_6822688).sum := by decide
  have hdescent : baseEnd_6822688 < baseStart_6822688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822711 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_6822711 : Nat := 118140960795 + 6822711 * 2 ^ 59
def prefixEnd_6822711 : Nat := 4983230072969 + 3 ^ 40 * 6822711 * 2
def baseEnd_6822711 : Nat := 3503330109717760845535429

theorem tailTrace_6822711 : CollatzResearch.WordTrace tailWord_6822711 prefixEnd_6822711 3503330109717760845535429 := by
  unfold tailWord_6822711
  simp only [CollatzResearch.WordTrace]
  refine ⟨248844713585490748115507987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165896475723660498743671991 248844713585490748115507987)
  ·
    refine ⟨373267070378236122173261981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248844713585490748115507987 373267070378236122173261981)
    ·
      refine ⟨139975151391838545814973243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373267070378236122173261981 139975151391838545814973243)
      ·
        refine ⟨209962727087757818722459865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139975151391838545814973243 209962727087757818722459865)
        ·
          refine ⟨157472045315818364041844899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209962727087757818722459865 157472045315818364041844899)
          ·
            refine ⟨236208067973727546062767349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157472045315818364041844899 236208067973727546062767349)
            ·
              refine ⟨22144506372536957443384439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236208067973727546062767349 22144506372536957443384439)
              ·
                refine ⟨33216759558805436165076659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22144506372536957443384439 33216759558805436165076659)
                ·
                  refine ⟨49825139338208154247614989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33216759558805436165076659 49825139338208154247614989)
                  ·
                    refine ⟨18684427251828057842855621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49825139338208154247614989 18684427251828057842855621)
                    ·
                      refine ⟨3503330109717760845535429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18684427251828057842855621 3503330109717760845535429)
                      ·
                        rfl

theorem cell23_6822711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_6822711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822711 prefixEnd_6822711 := by exact prefixLift 6822711
  have htrace : WordTrace (prefixWord ++ tailWord_6822711) baseStart_6822711 baseEnd_6822711 := by
    simpa [prefixWord, tailWord_6822711, baseEnd_6822711] using wordTrace_append hprefix tailTrace_6822711
  have hstable : (prefixWord ++ tailWord_6822711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822711).length < 2 ^ (prefixWord ++ tailWord_6822711).sum := by decide
  have hdescent : baseEnd_6822711 < baseStart_6822711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822728 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 4, 4, 2]
def baseStart_6822728 : Nat := 118140960795 + 6822728 * 2 ^ 59
def prefixEnd_6822728 : Nat := 4983230072969 + 3 ^ 40 * 6822728 * 2
def baseEnd_6822728 : Nat := 3503338838888887279022851

theorem tailTrace_6822728 : CollatzResearch.WordTrace tailWord_6822728 prefixEnd_6822728 3503338838888887279022851 := by
  unfold tailWord_6822728
  simp only [CollatzResearch.WordTrace]
  refine ⟨124422666813214580009438419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165896889084286106679251225 124422666813214580009438419)
  ·
    refine ⟨186634000219821870014157629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124422666813214580009438419 186634000219821870014157629)
    ·
      refine ⟨69987750082433201255309111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186634000219821870014157629 69987750082433201255309111)
      ·
        refine ⟨104981625123649801882963667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69987750082433201255309111 104981625123649801882963667)
        ·
          refine ⟨157472437685474702824445501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104981625123649801882963667 157472437685474702824445501)
          ·
            refine ⟨59052164132053013559167063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157472437685474702824445501 59052164132053013559167063)
            ·
              refine ⟨88578246198079520338750595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59052164132053013559167063 88578246198079520338750595)
              ·
                refine ⟨132867369297119280508125893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88578246198079520338750595 132867369297119280508125893)
                ·
                  refine ⟨24912631743209865095273605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132867369297119280508125893 24912631743209865095273605)
                  ·
                    refine ⟨4671118451851849705363801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24912631743209865095273605 4671118451851849705363801)
                    ·
                      refine ⟨3503338838888887279022851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671118451851849705363801 3503338838888887279022851)
                      ·
                        rfl

theorem cell23_6822728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_6822728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822728 prefixEnd_6822728 := by exact prefixLift 6822728
  have htrace : WordTrace (prefixWord ++ tailWord_6822728) baseStart_6822728 baseEnd_6822728 := by
    simpa [prefixWord, tailWord_6822728, baseEnd_6822728] using wordTrace_append hprefix tailTrace_6822728
  have hstable : (prefixWord ++ tailWord_6822728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822728).length < 2 ^ (prefixWord ++ tailWord_6822728).sum := by decide
  have hdescent : baseEnd_6822728 < baseStart_6822728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822741 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6822741 : Nat := 118140960795 + 6822741 * 2 ^ 59
def prefixEnd_6822741 : Nat := 4983230072969 + 3 ^ 40 * 6822741 * 2
def baseEnd_6822741 : Nat := 3503345514137395728160291

theorem tailTrace_6822741 : CollatzResearch.WordTrace tailWord_6822741 prefixEnd_6822741 3503345514137395728160291 := by
  unfold tailWord_6822741
  simp only [CollatzResearch.WordTrace]
  refine ⟨248845807775382063239100077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165897205183588042159400051 248845807775382063239100077)
  ·
    refine ⟨93317177915768273714662529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248845807775382063239100077 93317177915768273714662529)
    ·
      refine ⟨69987883436826205285996897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93317177915768273714662529 69987883436826205285996897)
      ·
        refine ⟨52490912577619653964497673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69987883436826205285996897 52490912577619653964497673)
        ·
          refine ⟨39368184433214740473373255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52490912577619653964497673 39368184433214740473373255)
          ·
            refine ⟨59052276649822110710059883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39368184433214740473373255 59052276649822110710059883)
            ·
              refine ⟨88578414974733166065089825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59052276649822110710059883 88578414974733166065089825)
              ·
                refine ⟨66433811231049874548817369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88578414974733166065089825 66433811231049874548817369)
                ·
                  refine ⟨49825358423287405911613027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66433811231049874548817369 49825358423287405911613027)
                  ·
                    refine ⟨74738037634931108867419541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49825358423287405911613027 74738037634931108867419541)
                    ·
                      refine ⟨3503345514137395728160291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74738037634931108867419541 3503345514137395728160291)
                      ·
                        rfl

theorem cell23_6822741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6822741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822741 prefixEnd_6822741 := by exact prefixLift 6822741
  have htrace : WordTrace (prefixWord ++ tailWord_6822741) baseStart_6822741 baseEnd_6822741 := by
    simpa [prefixWord, tailWord_6822741, baseEnd_6822741] using wordTrace_append hprefix tailTrace_6822741
  have hstable : (prefixWord ++ tailWord_6822741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822741).length < 2 ^ (prefixWord ++ tailWord_6822741).sum := by decide
  have hdescent : baseEnd_6822741 < baseStart_6822741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822795 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 3, 1, 3]
def baseStart_6822795 : Nat := 118140960795 + 6822795 * 2 ^ 59
def prefixEnd_6822795 : Nat := 4983230072969 + 3 ^ 40 * 6822795 * 2
def baseEnd_6822795 : Nat := 3503373242092738516885043

theorem tailTrace_6822795 : CollatzResearch.WordTrace tailWord_6822795 prefixEnd_6822795 3503373242092738516885043 := by
  unfold tailWord_6822795
  simp only [CollatzResearch.WordTrace]
  refine ⟨248847777317186430461565839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165898518211457620307710559 248847777317186430461565839)
  ·
    refine ⟨373271665975779645692348759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248847777317186430461565839 373271665975779645692348759)
    ·
      refine ⟨559907498963669468538523139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373271665975779645692348759 559907498963669468538523139)
      ·
        refine ⟨839861248445504202807784709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559907498963669468538523139 839861248445504202807784709)
        ·
          refine ⟨157473984083532038026459633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 839861248445504202807784709 157473984083532038026459633)
          ·
            refine ⟨118105488062649028519844725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157473984083532038026459633 118105488062649028519844725)
            ·
              refine ⟨11072389505873346423735443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118105488062649028519844725 11072389505873346423735443)
              ·
                refine ⟨16608584258810019635603165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11072389505873346423735443 16608584258810019635603165)
                ·
                  refine ⟨6228219097053757363351187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16608584258810019635603165 6228219097053757363351187)
                  ·
                    refine ⟨9342328645580636045026781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6228219097053757363351187 9342328645580636045026781)
                    ·
                      refine ⟨3503373242092738516885043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9342328645580636045026781 3503373242092738516885043)
                      ·
                        rfl

theorem cell23_6822795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 1, 3].length) (baseStart_6822795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822795 prefixEnd_6822795 := by exact prefixLift 6822795
  have htrace : WordTrace (prefixWord ++ tailWord_6822795) baseStart_6822795 baseEnd_6822795 := by
    simpa [prefixWord, tailWord_6822795, baseEnd_6822795] using wordTrace_append hprefix tailTrace_6822795
  have hstable : (prefixWord ++ tailWord_6822795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822795).length < 2 ^ (prefixWord ++ tailWord_6822795).sum := by decide
  have hdescent : baseEnd_6822795 < baseStart_6822795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822801 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_6822801 : Nat := 118140960795 + 6822801 * 2 ^ 59
def prefixEnd_6822801 : Nat := 4983230072969 + 3 ^ 40 * 6822801 * 2
def baseEnd_6822801 : Nat := 3503376322976665493410015

theorem tailTrace_6822801 : CollatzResearch.WordTrace tailWord_6822801 prefixEnd_6822801 3503376322976665493410015 := by
  unfold tailWord_6822801
  simp only [CollatzResearch.WordTrace]
  refine ⟨248847996155164693486284257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165898664103443128990856171 248847996155164693486284257)
  ·
    refine ⟨186635997116373520114713193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248847996155164693486284257 186635997116373520114713193)
    ·
      refine ⟨139976997837280140086034895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186635997116373520114713193 139976997837280140086034895)
      ·
        refine ⟨209965496755920210129052343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139976997837280140086034895 209965496755920210129052343)
        ·
          refine ⟨314948245133880315193578515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209965496755920210129052343 314948245133880315193578515)
          ·
            refine ⟨472422367700820472790367773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314948245133880315193578515 472422367700820472790367773)
            ·
              refine ⟨177158387887807677296387915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472422367700820472790367773 177158387887807677296387915)
              ·
                refine ⟨265737581831711515944581873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177158387887807677296387915 265737581831711515944581873)
                ·
                  refine ⟨199303186373783636958436405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265737581831711515944581873 199303186373783636958436405)
                  ·
                    refine ⟨18684673722542215964853413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 199303186373783636958436405 18684673722542215964853413)
                    ·
                      refine ⟨3503376322976665493410015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18684673722542215964853413 3503376322976665493410015)
                      ·
                        rfl

theorem cell23_6822801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_6822801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822801 prefixEnd_6822801 := by exact prefixLift 6822801
  have htrace : WordTrace (prefixWord ++ tailWord_6822801) baseStart_6822801 baseEnd_6822801 := by
    simpa [prefixWord, tailWord_6822801, baseEnd_6822801] using wordTrace_append hprefix tailTrace_6822801
  have hstable : (prefixWord ++ tailWord_6822801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822801).length < 2 ^ (prefixWord ++ tailWord_6822801).sum := by decide
  have hdescent : baseEnd_6822801 < baseStart_6822801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822815 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 1, 5]
def baseStart_6822815 : Nat := 118140960795 + 6822815 * 2 ^ 59
def prefixEnd_6822815 : Nat := 4983230072969 + 3 ^ 40 * 6822815 * 2
def baseEnd_6822815 : Nat := 1167794503901942812878317

theorem tailTrace_6822815 : CollatzResearch.WordTrace tailWord_6822815 prefixEnd_6822815 1167794503901942812878317 := by
  unfold tailWord_6822815
  simp only [CollatzResearch.WordTrace]
  refine ⟨248848506777113973877293899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165899004518075982584862599 248848506777113973877293899)
  ·
    refine ⟨373272760165670960815940849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248848506777113973877293899 373272760165670960815940849)
    ·
      refine ⟨279954570124253220611955637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373272760165670960815940849 279954570124253220611955637)
      ·
        refine ⟨26245740949148739432370841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279954570124253220611955637 26245740949148739432370841)
        ·
          refine ⟨19684305711861554574278131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26245740949148739432370841 19684305711861554574278131)
          ·
            refine ⟨29526458567792331861417197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19684305711861554574278131 29526458567792331861417197)
            ·
              refine ⟨11072421962922124448031449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29526458567792331861417197 11072421962922124448031449)
              ·
                refine ⟨8304316472191593336023587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11072421962922124448031449 8304316472191593336023587)
                ·
                  refine ⟨12456474708287390004035381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8304316472191593336023587 12456474708287390004035381)
                  ·
                    refine ⟨1167794503901942812878317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12456474708287390004035381 1167794503901942812878317)
                    ·
                      rfl

theorem cell23_6822815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 5].length) (baseStart_6822815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822815 prefixEnd_6822815 := by exact prefixLift 6822815
  have htrace : WordTrace (prefixWord ++ tailWord_6822815) baseStart_6822815 baseEnd_6822815 := by
    simpa [prefixWord, tailWord_6822815, baseEnd_6822815] using wordTrace_append hprefix tailTrace_6822815
  have hstable : (prefixWord ++ tailWord_6822815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822815).length < 2 ^ (prefixWord ++ tailWord_6822815).sum := by decide
  have hdescent : baseEnd_6822815 < baseStart_6822815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822821 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_6822821 : Nat := 118140960795 + 6822821 * 2 ^ 59
def prefixEnd_6822821 : Nat := 4983230072969 + 3 ^ 40 * 6822821 * 2
def baseEnd_6822821 : Nat := 3503386592589755415159923

theorem tailTrace_6822821 : CollatzResearch.WordTrace tailWord_6822821 prefixEnd_6822821 3503386592589755415159923 := by
  unfold tailWord_6822821
  simp only [CollatzResearch.WordTrace]
  refine ⟨248848725615092236902012317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165899150410061491268008211 248848725615092236902012317)
  ·
    refine ⟨93318272105659588838254619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248848725615092236902012317 93318272105659588838254619)
    ·
      refine ⟨139977408158489383257381929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93318272105659588838254619 139977408158489383257381929)
      ·
        refine ⟨104983056118867037443036447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139977408158489383257381929 104983056118867037443036447)
        ·
          refine ⟨157474584178300556164554671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104983056118867037443036447 157474584178300556164554671)
          ·
            refine ⟨236211876267450834246832007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157474584178300556164554671 236211876267450834246832007)
            ·
              refine ⟨354317814401176251370248011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236211876267450834246832007 354317814401176251370248011)
              ·
                refine ⟨531476721601764377055372017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354317814401176251370248011 531476721601764377055372017)
                ·
                  refine ⟨398607541201323282791529013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531476721601764377055372017 398607541201323282791529013)
                  ·
                    refine ⟨37369456987624057761705845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 398607541201323282791529013 37369456987624057761705845)
                    ·
                      refine ⟨3503386592589755415159923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37369456987624057761705845 3503386592589755415159923)
                      ·
                        rfl

theorem cell23_6822821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_6822821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822821 prefixEnd_6822821 := by exact prefixLift 6822821
  have htrace : WordTrace (prefixWord ++ tailWord_6822821) baseStart_6822821 baseEnd_6822821 := by
    simpa [prefixWord, tailWord_6822821, baseEnd_6822821] using wordTrace_append hprefix tailTrace_6822821
  have hstable : (prefixWord ++ tailWord_6822821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822821).length < 2 ^ (prefixWord ++ tailWord_6822821).sum := by decide
  have hdescent : baseEnd_6822821 < baseStart_6822821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822831 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_6822831 : Nat := 118140960795 + 6822831 * 2 ^ 59
def prefixEnd_6822831 : Nat := 4983230072969 + 3 ^ 40 * 6822831 * 2
def baseEnd_6822831 : Nat := 3503391727396300376034877

theorem tailTrace_6822831 : CollatzResearch.WordTrace tailWord_6822831 prefixEnd_6822831 3503391727396300376034877 := by
  unfold tailWord_6822831
  simp only [CollatzResearch.WordTrace]
  refine ⟨248849090345056008609876347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165899393563370672406584231 248849090345056008609876347)
  ·
    refine ⟨373273635517584012914814521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248849090345056008609876347 373273635517584012914814521)
    ·
      refine ⟨279955226638188009686110891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373273635517584012914814521 279955226638188009686110891)
      ·
        refine ⟨419932839957282014529166337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279955226638188009686110891 419932839957282014529166337)
        ·
          refine ⟨314949629967961510896874753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419932839957282014529166337 314949629967961510896874753)
          ·
            refine ⟨236212222475971133172656065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314949629967961510896874753 236212222475971133172656065)
            ·
              refine ⟨177159166856978349879492049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236212222475971133172656065 177159166856978349879492049)
              ·
                refine ⟨132869375142733762409619037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177159166856978349879492049 132869375142733762409619037)
                ·
                  refine ⟨49826015678525160903607139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132869375142733762409619037 49826015678525160903607139)
                  ·
                    refine ⟨74739023517787741355410709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49826015678525160903607139 74739023517787741355410709)
                    ·
                      refine ⟨3503391727396300376034877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74739023517787741355410709 3503391727396300376034877)
                      ·
                        rfl

theorem cell23_6822831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_6822831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822831 prefixEnd_6822831 := by exact prefixLift 6822831
  have htrace : WordTrace (prefixWord ++ tailWord_6822831) baseStart_6822831 baseEnd_6822831 := by
    simpa [prefixWord, tailWord_6822831, baseEnd_6822831] using wordTrace_append hprefix tailTrace_6822831
  have hstable : (prefixWord ++ tailWord_6822831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822831).length < 2 ^ (prefixWord ++ tailWord_6822831).sum := by decide
  have hdescent : baseEnd_6822831 < baseStart_6822831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822835 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 7, 2, 2]
def baseStart_6822835 : Nat := 118140960795 + 6822835 * 2 ^ 59
def prefixEnd_6822835 : Nat := 4983230072969 + 3 ^ 40 * 6822835 * 2
def baseEnd_6822835 : Nat := 3503393781318918360384859

theorem tailTrace_6822835 : CollatzResearch.WordTrace tailWord_6822835 prefixEnd_6822835 3503393781318918360384859 := by
  unfold tailWord_6822835
  simp only [CollatzResearch.WordTrace]
  refine ⟨248849236237041517293021959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165899490824694344862014639 248849236237041517293021959)
  ·
    refine ⟨373273854355562275939532939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248849236237041517293021959 373273854355562275939532939)
    ·
      refine ⟨559910781533343413909299409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373273854355562275939532939 559910781533343413909299409)
      ·
        refine ⟨419933086150007560431974557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559910781533343413909299409 419933086150007560431974557)
        ·
          refine ⟨157474907306252835161990459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419933086150007560431974557 157474907306252835161990459)
          ·
            refine ⟨236212360959379252742985689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157474907306252835161990459 236212360959379252742985689)
            ·
              refine ⟨177159270719534439557239267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236212360959379252742985689 177159270719534439557239267)
              ·
                refine ⟨265738906079301659335858901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177159270719534439557239267 265738906079301659335858901)
                ·
                  refine ⟨6228255611233632640684193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 265738906079301659335858901 6228255611233632640684193)
                  ·
                    refine ⟨4671191708425224480513145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6228255611233632640684193 4671191708425224480513145)
                    ·
                      refine ⟨3503393781318918360384859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671191708425224480513145 3503393781318918360384859)
                      ·
                        rfl

theorem cell23_6822835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 2, 2].length) (baseStart_6822835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822835 prefixEnd_6822835 := by exact prefixLift 6822835
  have htrace : WordTrace (prefixWord ++ tailWord_6822835) baseStart_6822835 baseEnd_6822835 := by
    simpa [prefixWord, tailWord_6822835, baseEnd_6822835] using wordTrace_append hprefix tailTrace_6822835
  have hstable : (prefixWord ++ tailWord_6822835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822835).length < 2 ^ (prefixWord ++ tailWord_6822835).sum := by decide
  have hdescent : baseEnd_6822835 < baseStart_6822835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822841 : List Nat := [1, 2, 1, 4, 2, 13]
def baseStart_6822841 : Nat := 118140960795 + 6822841 * 2 ^ 59
def prefixEnd_6822841 : Nat := 4983230072969 + 3 ^ 40 * 6822841 * 2
def baseEnd_6822841 : Nat := 14417271037871791509917

theorem tailTrace_6822841 : CollatzResearch.WordTrace tailWord_6822841 prefixEnd_6822841 14417271037871791509917 := by
  unfold tailWord_6822841
  simp only [CollatzResearch.WordTrace]
  refine ⟨248849455075019780317740377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165899636716679853545160251 248849455075019780317740377)
  ·
    refine ⟨186637091306264835238305283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248849455075019780317740377 186637091306264835238305283)
    ·
      refine ⟨279955636959397252857457925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186637091306264835238305283 279955636959397252857457925)
      ·
        refine ⟨52491681929886984910773361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279955636959397252857457925 52491681929886984910773361)
        ·
          refine ⟨39368761447415238683080021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52491681929886984910773361 39368761447415238683080021)
          ·
            refine ⟨14417271037871791509917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 39368761447415238683080021 14417271037871791509917)
            ·
              rfl

theorem cell23_6822841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 13].length) (baseStart_6822841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822841 prefixEnd_6822841 := by exact prefixLift 6822841
  have htrace : WordTrace (prefixWord ++ tailWord_6822841) baseStart_6822841 baseEnd_6822841 := by
    simpa [prefixWord, tailWord_6822841, baseEnd_6822841] using wordTrace_append hprefix tailTrace_6822841
  have hstable : (prefixWord ++ tailWord_6822841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822841).length < 2 ^ (prefixWord ++ tailWord_6822841).sum := by decide
  have hdescent : baseEnd_6822841 < baseStart_6822841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822869 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 3, 2, 2]
def baseStart_6822869 : Nat := 118140960795 + 6822869 * 2 ^ 59
def prefixEnd_6822869 : Nat := 4983230072969 + 3 ^ 40 * 6822869 * 2
def baseEnd_6822869 : Nat := 3503411239661171227359703

theorem tailTrace_6822869 : CollatzResearch.WordTrace tailWord_6822869 prefixEnd_6822869 3503411239661171227359703 := by
  unfold tailWord_6822869
  simp only [CollatzResearch.WordTrace]
  refine ⟨248850476318918341099759661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165900317545945560733173107 248850476318918341099759661)
  ·
    refine ⟨93318928619594377912409873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248850476318918341099759661 93318928619594377912409873)
    ·
      refine ⟨69989196464695783434307405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93318928619594377912409873 69989196464695783434307405)
      ·
        refine ⟨26245948674260918787865277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69989196464695783434307405 26245948674260918787865277)
        ·
          refine ⟨9842230752847844545449479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26245948674260918787865277 9842230752847844545449479)
          ·
            refine ⟨14763346129271766818174219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9842230752847844545449479 14763346129271766818174219)
            ·
              refine ⟨22145019193907650227261329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14763346129271766818174219 22145019193907650227261329)
              ·
                refine ⟨16608764395430737670445997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22145019193907650227261329 16608764395430737670445997)
                ·
                  refine ⟨6228286648286526626417249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16608764395430737670445997 6228286648286526626417249)
                  ·
                    refine ⟨4671214986214894969812937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6228286648286526626417249 4671214986214894969812937)
                    ·
                      refine ⟨3503411239661171227359703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671214986214894969812937 3503411239661171227359703)
                      ·
                        rfl

theorem cell23_6822869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_6822869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822869 prefixEnd_6822869 := by exact prefixLift 6822869
  have htrace : WordTrace (prefixWord ++ tailWord_6822869) baseStart_6822869 baseEnd_6822869 := by
    simpa [prefixWord, tailWord_6822869, baseEnd_6822869] using wordTrace_append hprefix tailTrace_6822869
  have hstable : (prefixWord ++ tailWord_6822869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822869).length < 2 ^ (prefixWord ++ tailWord_6822869).sum := by decide
  have hdescent : baseEnd_6822869 < baseStart_6822869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822882 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_6822882 : Nat := 118140960795 + 6822882 * 2 ^ 59
def prefixEnd_6822882 : Nat := 4983230072969 + 3 ^ 40 * 6822882 * 2
def baseEnd_6822882 : Nat := 3503417914909679676497143

theorem tailTrace_6822882 : CollatzResearch.WordTrace tailWord_6822882 prefixEnd_6822882 3503417914909679676497143 := by
  unfold tailWord_6822882
  simp only [CollatzResearch.WordTrace]
  refine ⟨62212737616967811079995725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165900633645247496213321933 62212737616967811079995725)
  ·
    refine ⟨23329776606362929154998397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62212737616967811079995725 23329776606362929154998397)
    ·
      refine ⟨8748666227386098433124399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23329776606362929154998397 8748666227386098433124399)
      ·
        refine ⟨13122999341079147649686599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8748666227386098433124399 13122999341079147649686599)
        ·
          refine ⟨19684499011618721474529899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13122999341079147649686599 19684499011618721474529899)
          ·
            refine ⟨29526748517428082211794849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19684499011618721474529899 29526748517428082211794849)
            ·
              refine ⟨22145061388071061658846137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29526748517428082211794849 22145061388071061658846137)
              ·
                refine ⟨16608796041053296244134603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22145061388071061658846137 16608796041053296244134603)
                ·
                  refine ⟨24913194061579944366201905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16608796041053296244134603 24913194061579944366201905)
                  ·
                    refine ⟨18684895546184958274651429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24913194061579944366201905 18684895546184958274651429)
                    ·
                      refine ⟨3503417914909679676497143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18684895546184958274651429 3503417914909679676497143)
                      ·
                        rfl

theorem cell23_6822882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_6822882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822882 prefixEnd_6822882 := by exact prefixLift 6822882
  have htrace : WordTrace (prefixWord ++ tailWord_6822882) baseStart_6822882 baseEnd_6822882 := by
    simpa [prefixWord, tailWord_6822882, baseEnd_6822882] using wordTrace_append hprefix tailTrace_6822882
  have hstable : (prefixWord ++ tailWord_6822882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822882).length < 2 ^ (prefixWord ++ tailWord_6822882).sum := by decide
  have hdescent : baseEnd_6822882 < baseStart_6822882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822919 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 2, 1, 3]
def baseStart_6822919 : Nat := 118140960795 + 6822919 * 2 ^ 59
def prefixEnd_6822919 : Nat := 4983230072969 + 3 ^ 40 * 6822919 * 2
def baseEnd_6822919 : Nat := 3503436913693896031734473

theorem tailTrace_6822919 : CollatzResearch.WordTrace tailWord_6822919 prefixEnd_6822919 3503436913693896031734473 := by
  unfold tailWord_6822919
  simp only [CollatzResearch.WordTrace]
  refine ⟨248852299968737199639079811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165901533312491466426053207 248852299968737199639079811)
  ·
    refine ⟨373278449953105799458619717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248852299968737199639079811 373278449953105799458619717)
    ·
      refine ⟨69989709366207337398491197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373278449953105799458619717 69989709366207337398491197)
      ·
        refine ⟨26246141012327751524434199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69989709366207337398491197 26246141012327751524434199)
        ·
          refine ⟨39369211518491627286651299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26246141012327751524434199 39369211518491627286651299)
          ·
            refine ⟨59053817277737440929976949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39369211518491627286651299 59053817277737440929976949)
            ·
              refine ⟨5536295369787885087185339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59053817277737440929976949 5536295369787885087185339)
              ·
                refine ⟨8304443054681827630778009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5536295369787885087185339 8304443054681827630778009)
                ·
                  refine ⟨6228332291011370723083507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8304443054681827630778009 6228332291011370723083507)
                  ·
                    refine ⟨9342498436517056084625261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6228332291011370723083507 9342498436517056084625261)
                    ·
                      refine ⟨3503436913693896031734473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9342498436517056084625261 3503436913693896031734473)
                      ·
                        rfl

theorem cell23_6822919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_6822919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822919 prefixEnd_6822919 := by exact prefixLift 6822919
  have htrace : WordTrace (prefixWord ++ tailWord_6822919) baseStart_6822919 baseEnd_6822919 := by
    simpa [prefixWord, tailWord_6822919, baseEnd_6822919] using wordTrace_append hprefix tailTrace_6822919
  have hstable : (prefixWord ++ tailWord_6822919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822919).length < 2 ^ (prefixWord ++ tailWord_6822919).sum := by decide
  have hdescent : baseEnd_6822919 < baseStart_6822919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822945 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_6822945 : Nat := 118140960795 + 6822945 * 2 ^ 59
def prefixEnd_6822945 : Nat := 4983230072969 + 3 ^ 40 * 6822945 * 2
def baseEnd_6822945 : Nat := 3503450264190912930009353

theorem tailTrace_6822945 : CollatzResearch.WordTrace tailWord_6822945 prefixEnd_6822945 3503450264190912930009353 := by
  unfold tailWord_6822945
  simp only [CollatzResearch.WordTrace]
  refine ⟨248853248266643006079526289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165902165511095337386350859 248853248266643006079526289)
  ·
    refine ⟨186639936199982254559644717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248853248266643006079526289 186639936199982254559644717)
    ·
      refine ⟨69989976074993345459866769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186639936199982254559644717 69989976074993345459866769)
      ·
        refine ⟨52492482056245009094900077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69989976074993345459866769 52492482056245009094900077)
        ·
          refine ⟨19684680771091878410587529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52492482056245009094900077 19684680771091878410587529)
          ·
            refine ⟨14763510578318908807940647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19684680771091878410587529 14763510578318908807940647)
            ·
              refine ⟨22145265867478363211910971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14763510578318908807940647 22145265867478363211910971)
              ·
                refine ⟨33217898801217544817866457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22145265867478363211910971 33217898801217544817866457)
                ·
                  refine ⟨24913424100913158613399843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33217898801217544817866457 24913424100913158613399843)
                  ·
                    refine ⟨37370136151369737920099765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24913424100913158613399843 37370136151369737920099765)
                    ·
                      refine ⟨3503450264190912930009353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37370136151369737920099765 3503450264190912930009353)
                      ·
                        rfl

theorem cell23_6822945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_6822945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822945 prefixEnd_6822945 := by exact prefixLift 6822945
  have htrace : WordTrace (prefixWord ++ tailWord_6822945) baseStart_6822945 baseEnd_6822945 := by
    simpa [prefixWord, tailWord_6822945, baseEnd_6822945] using wordTrace_append hprefix tailTrace_6822945
  have hstable : (prefixWord ++ tailWord_6822945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822945).length < 2 ^ (prefixWord ++ tailWord_6822945).sum := by decide
  have hdescent : baseEnd_6822945 < baseStart_6822945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822985 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 4, 5, 2]
def baseStart_6822985 : Nat := 118140960795 + 6822985 * 2 ^ 59
def prefixEnd_6822985 : Nat := 4983230072969 + 3 ^ 40 * 6822985 * 2
def baseEnd_6822985 : Nat := 3503470803417092773509169

theorem tailTrace_6822985 : CollatzResearch.WordTrace tailWord_6822985 prefixEnd_6822985 3503470803417092773509169 := by
  unfold tailWord_6822985
  simp only [CollatzResearch.WordTrace]
  refine ⟨248854707186498092910982409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165903138124332061940654939 248854707186498092910982409)
  ·
    refine ⟨186641030389873569683236807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248854707186498092910982409 186641030389873569683236807)
    ·
      refine ⟨279961545584810354524855211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186641030389873569683236807 279961545584810354524855211)
      ·
        refine ⟨419942318377215531787282817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279961545584810354524855211 419942318377215531787282817)
        ·
          refine ⟨314956738782911648840462113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419942318377215531787282817 314956738782911648840462113)
          ·
            refine ⟨236217554087183736630346585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314956738782911648840462113 236217554087183736630346585)
            ·
              refine ⟨177163165565387802472759939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236217554087183736630346585 177163165565387802472759939)
              ·
                refine ⟨265744748348081703709139909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177163165565387802472759939 265744748348081703709139909)
                ·
                  refine ⟨49827140315265319445463733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265744748348081703709139909 49827140315265319445463733)
                  ·
                    refine ⟨4671294404556123698012225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49827140315265319445463733 4671294404556123698012225)
                    ·
                      refine ⟨3503470803417092773509169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671294404556123698012225 3503470803417092773509169)
                      ·
                        rfl

theorem cell23_6822985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 5, 2].length) (baseStart_6822985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822985 prefixEnd_6822985 := by exact prefixLift 6822985
  have htrace : WordTrace (prefixWord ++ tailWord_6822985) baseStart_6822985 baseEnd_6822985 := by
    simpa [prefixWord, tailWord_6822985, baseEnd_6822985] using wordTrace_append hprefix tailTrace_6822985
  have hstable : (prefixWord ++ tailWord_6822985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822985).length < 2 ^ (prefixWord ++ tailWord_6822985).sum := by decide
  have hdescent : baseEnd_6822985 < baseStart_6822985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6822988 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_6822988 : Nat := 118140960795 + 6822988 * 2 ^ 59
def prefixEnd_6822988 : Nat := 4983230072969 + 3 ^ 40 * 6822988 * 2
def baseEnd_6822988 : Nat := 3503472343859056261771655

theorem tailTrace_6822988 : CollatzResearch.WordTrace tailWord_6822988 prefixEnd_6822988 3503472343859056261771655 := by
  unfold tailWord_6822988
  simp only [CollatzResearch.WordTrace]
  refine ⟨124427408302743612211670809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165903211070324816282227745 124427408302743612211670809)
  ·
    refine ⟨93320556227057709158753107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124427408302743612211670809 93320556227057709158753107)
    ·
      refine ⟨139980834340586563738129661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93320556227057709158753107 139980834340586563738129661)
      ·
        refine ⟨52492812877719961401798623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139980834340586563738129661 52492812877719961401798623)
        ·
          refine ⟨78739219316579942102697935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52492812877719961401798623 78739219316579942102697935)
          ·
            refine ⟨118108828974869913154046903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78739219316579942102697935 118108828974869913154046903)
            ·
              refine ⟨177163243462304869731070355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118108828974869913154046903 177163243462304869731070355)
              ·
                refine ⟨265744865193457304596605533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177163243462304869731070355 265744865193457304596605533)
                ·
                  refine ⟨99654324447546489223727075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265744865193457304596605533 99654324447546489223727075)
                  ·
                    refine ⟨149481486671319733835590613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99654324447546489223727075 149481486671319733835590613)
                    ·
                      refine ⟨3503472343859056261771655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149481486671319733835590613 3503472343859056261771655)
                      ·
                        rfl

theorem cell23_6822988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_6822988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6822988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6822988 prefixEnd_6822988 := by exact prefixLift 6822988
  have htrace : WordTrace (prefixWord ++ tailWord_6822988) baseStart_6822988 baseEnd_6822988 := by
    simpa [prefixWord, tailWord_6822988, baseEnd_6822988] using wordTrace_append hprefix tailTrace_6822988
  have hstable : (prefixWord ++ tailWord_6822988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6822988).length < 2 ^ (prefixWord ++ tailWord_6822988).sum := by decide
  have hdescent : baseEnd_6822988 < baseStart_6822988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6822988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823035 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 3]
def baseStart_6823035 : Nat := 118140960795 + 6823035 * 2 ^ 59
def prefixEnd_6823035 : Nat := 4983230072969 + 3 ^ 40 * 6823035 * 2
def baseEnd_6823035 : Nat := 3503496477449817577883939

theorem tailTrace_6823035 : CollatzResearch.WordTrace tailWord_6823035 prefixEnd_6823035 3503496477449817577883939 := by
  unfold tailWord_6823035
  simp only [CollatzResearch.WordTrace]
  refine ⟨248856530836316951450302559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165904353890877967633535039 248856530836316951450302559)
  ·
    refine ⟨373284796254475427175453839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248856530836316951450302559 373284796254475427175453839)
    ·
      refine ⟨559927194381713140763180759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373284796254475427175453839 559927194381713140763180759)
      ·
        refine ⟨839890791572569711144771139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559927194381713140763180759 839890791572569711144771139)
        ·
          refine ⟨1259836187358854566717156709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839890791572569711144771139 1259836187358854566717156709)
          ·
            refine ⟨236219285129785231259466883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1259836187358854566717156709 236219285129785231259466883)
            ·
              refine ⟨354328927694677846889200325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236219285129785231259466883 354328927694677846889200325)
              ·
                refine ⟨66436673942752096291725061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354328927694677846889200325 66436673942752096291725061)
                ·
                  refine ⟨12456876364266018054698449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66436673942752096291725061 12456876364266018054698449)
                  ·
                    refine ⟨9342657273199513541023837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12456876364266018054698449 9342657273199513541023837)
                    ·
                      refine ⟨3503496477449817577883939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9342657273199513541023837 3503496477449817577883939)
                      ·
                        rfl

theorem cell23_6823035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 3].length) (baseStart_6823035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823035 prefixEnd_6823035 := by exact prefixLift 6823035
  have htrace : WordTrace (prefixWord ++ tailWord_6823035) baseStart_6823035 baseEnd_6823035 := by
    simpa [prefixWord, tailWord_6823035, baseEnd_6823035] using wordTrace_append hprefix tailTrace_6823035
  have hstable : (prefixWord ++ tailWord_6823035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823035).length < 2 ^ (prefixWord ++ tailWord_6823035).sum := by decide
  have hdescent : baseEnd_6823035 < baseStart_6823035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823089 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 6]
def baseStart_6823089 : Nat := 118140960795 + 6823089 * 2 ^ 59
def prefixEnd_6823089 : Nat := 4983230072969 + 3 ^ 40 * 6823089 * 2
def baseEnd_6823089 : Nat := 389280467267240040734299

theorem tailTrace_6823089 : CollatzResearch.WordTrace tailWord_6823089 prefixEnd_6823089 389280467267240040734299 := by
  unfold tailWord_6823089
  simp only [CollatzResearch.WordTrace]
  refine ⟨248858500378121318672768321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165905666918747545781845547 248858500378121318672768321)
  ·
    refine ⟨186643875283590989004576241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248858500378121318672768321 186643875283590989004576241)
    ·
      refine ⟨139982906462693241753432181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186643875283590989004576241 139982906462693241753432181)
      ·
        refine ⟨13123397480877491414384267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139982906462693241753432181 13123397480877491414384267)
        ·
          refine ⟨19685096221316237121576401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13123397480877491414384267 19685096221316237121576401)
          ·
            refine ⟨14763822165987177841182301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19685096221316237121576401 14763822165987177841182301)
            ·
              refine ⟨5536433312245191690443363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14763822165987177841182301 5536433312245191690443363)
              ·
                refine ⟨8304649968367787535665045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5536433312245191690443363 8304649968367787535665045)
                ·
                  refine ⟨389280467267240040734299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8304649968367787535665045 389280467267240040734299)
                  ·
                    rfl

theorem cell23_6823089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 6].length) (baseStart_6823089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823089 prefixEnd_6823089 := by exact prefixLift 6823089
  have htrace : WordTrace (prefixWord ++ tailWord_6823089) baseStart_6823089 baseEnd_6823089 := by
    simpa [prefixWord, tailWord_6823089, baseEnd_6823089] using wordTrace_append hprefix tailTrace_6823089
  have hstable : (prefixWord ++ tailWord_6823089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823089).length < 2 ^ (prefixWord ++ tailWord_6823089).sum := by decide
  have hdescent : baseEnd_6823089 < baseStart_6823089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823133 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_6823133 : Nat := 118140960795 + 6823133 * 2 ^ 59
def prefixEnd_6823133 : Nat := 4983230072969 + 3 ^ 40 * 6823133 * 2
def baseEnd_6823133 : Nat := 3503546798553958194458489

theorem tailTrace_6823133 : CollatzResearch.WordTrace tailWord_6823133 prefixEnd_6823133 3503546798553958194458489 := by
  unfold tailWord_6823133
  simp only [CollatzResearch.WordTrace]
  refine ⟨248860105189961914187370053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165906736793307942791580035 248860105189961914187370053)
  ·
    refine ⟨46661269723117858910131885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248860105189961914187370053 46661269723117858910131885)
    ·
      refine ⟨17497976146169197091299457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46661269723117858910131885 17497976146169197091299457)
      ·
        refine ⟨13123482109626897818474593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17497976146169197091299457 13123482109626897818474593)
        ·
          refine ⟨9842611582220173363855945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13123482109626897818474593 9842611582220173363855945)
          ·
            refine ⟨7381958686665130022891959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9842611582220173363855945 7381958686665130022891959)
            ·
              refine ⟨11072938029997695034337939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381958686665130022891959 11072938029997695034337939)
              ·
                refine ⟨16609407044996542551506909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11072938029997695034337939 16609407044996542551506909)
                ·
                  refine ⟨6228527641873703456815091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16609407044996542551506909 6228527641873703456815091)
                  ·
                    refine ⟨9342791462810555185222637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6228527641873703456815091 9342791462810555185222637)
                    ·
                      refine ⟨3503546798553958194458489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9342791462810555185222637 3503546798553958194458489)
                      ·
                        rfl

theorem cell23_6823133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_6823133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823133 prefixEnd_6823133 := by exact prefixLift 6823133
  have htrace : WordTrace (prefixWord ++ tailWord_6823133) baseStart_6823133 baseEnd_6823133 := by
    simpa [prefixWord, tailWord_6823133, baseEnd_6823133] using wordTrace_append hprefix tailTrace_6823133
  have hstable : (prefixWord ++ tailWord_6823133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823133).length < 2 ^ (prefixWord ++ tailWord_6823133).sum := by decide
  have hdescent : baseEnd_6823133 < baseStart_6823133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823135 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 6]
def baseStart_6823135 : Nat := 118140960795 + 6823135 * 2 ^ 59
def prefixEnd_6823135 : Nat := 4983230072969 + 3 ^ 40 * 6823135 * 2
def baseEnd_6823135 : Nat := 3503547825515267186633479

theorem tailTrace_6823135 : CollatzResearch.WordTrace tailWord_6823135 prefixEnd_6823135 3503547825515267186633479 := by
  unfold tailWord_6823135
  simp only [CollatzResearch.WordTrace]
  refine ⟨248860178135954668528942859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165906785423969779019295239 248860178135954668528942859)
  ·
    refine ⟨373290267203932002793414289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248860178135954668528942859 373290267203932002793414289)
    ·
      refine ⟨279967700402949002095060717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373290267203932002793414289 279967700402949002095060717)
      ·
        refine ⟨104987887651105875785647769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279967700402949002095060717 104987887651105875785647769)
        ·
          refine ⟨78740915738329406839235827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104987887651105875785647769 78740915738329406839235827)
          ·
            refine ⟨118111373607494110258853741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78740915738329406839235827 118111373607494110258853741)
            ·
              refine ⟨44291765102810291347070153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118111373607494110258853741 44291765102810291347070153)
              ·
                refine ⟨33218823827107718510302615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44291765102810291347070153 33218823827107718510302615)
                ·
                  refine ⟨49828235740661577765453923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33218823827107718510302615 49828235740661577765453923)
                  ·
                    refine ⟨74742353610992366648180885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49828235740661577765453923 74742353610992366648180885)
                    ·
                      refine ⟨3503547825515267186633479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74742353610992366648180885 3503547825515267186633479)
                      ·
                        rfl

theorem cell23_6823135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_6823135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823135 prefixEnd_6823135 := by exact prefixLift 6823135
  have htrace : WordTrace (prefixWord ++ tailWord_6823135) baseStart_6823135 baseEnd_6823135 := by
    simpa [prefixWord, tailWord_6823135, baseEnd_6823135] using wordTrace_append hprefix tailTrace_6823135
  have hstable : (prefixWord ++ tailWord_6823135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823135).length < 2 ^ (prefixWord ++ tailWord_6823135).sum := by decide
  have hdescent : baseEnd_6823135 < baseStart_6823135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823176 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 1, 1, 5]
def baseStart_6823176 : Nat := 118140960795 + 6823176 * 2 ^ 59
def prefixEnd_6823176 : Nat := 4983230072969 + 3 ^ 40 * 6823176 * 2
def baseEnd_6823176 : Nat := 3503568878222101526220791

theorem tailTrace_6823176 : CollatzResearch.WordTrace tailWord_6823176 prefixEnd_6823176 3503568878222101526220791 := by
  unfold tailWord_6823176
  simp only [CollatzResearch.WordTrace]
  refine ⟨124430836764403066265592691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165907782352537421687456921 124430836764403066265592691)
  ·
    refine ⟨186646255146604599398389037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124430836764403066265592691 186646255146604599398389037)
    ·
      refine ⟨69992345679976724774395889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186646255146604599398389037 69992345679976724774395889)
      ·
        refine ⟨52494259259982543580796917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69992345679976724774395889 52494259259982543580796917)
        ·
          refine ⟨4921336805623363460699711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52494259259982543580796917 4921336805623363460699711)
          ·
            refine ⟨7382005208435045191049567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921336805623363460699711 7382005208435045191049567)
            ·
              refine ⟨11073007812652567786574351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7382005208435045191049567 11073007812652567786574351)
              ·
                refine ⟨16609511718978851679861527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11073007812652567786574351 16609511718978851679861527)
                ·
                  refine ⟨24914267578468277519792291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16609511718978851679861527 24914267578468277519792291)
                  ·
                    refine ⟨37371401367702416279688437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24914267578468277519792291 37371401367702416279688437)
                    ·
                      refine ⟨3503568878222101526220791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37371401367702416279688437 3503568878222101526220791)
                      ·
                        rfl

theorem cell23_6823176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_6823176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823176 prefixEnd_6823176 := by exact prefixLift 6823176
  have htrace : WordTrace (prefixWord ++ tailWord_6823176) baseStart_6823176 baseEnd_6823176 := by
    simpa [prefixWord, tailWord_6823176, baseEnd_6823176] using wordTrace_append hprefix tailTrace_6823176
  have hstable : (prefixWord ++ tailWord_6823176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823176).length < 2 ^ (prefixWord ++ tailWord_6823176).sum := by decide
  have hdescent : baseEnd_6823176 < baseStart_6823176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823233 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6823233 : Nat := 118140960795 + 6823233 * 2 ^ 59
def prefixEnd_6823233 : Nat := 4983230072969 + 3 ^ 40 * 6823233 * 2
def baseEnd_6823233 : Nat := 3503598146619407803208029

theorem tailTrace_6823233 : CollatzResearch.WordTrace tailWord_6823233 prefixEnd_6823233 3503598146619407803208029 := by
  unfold tailWord_6823233
  simp only [CollatzResearch.WordTrace]
  refine ⟨248863752489599631266010353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165909168326399754177340235 248863752489599631266010353)
  ·
    refine ⟨186647814367199723449507765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248863752489599631266010353 186647814367199723449507765)
    ·
      refine ⟨17498232596924974073391353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186647814367199723449507765 17498232596924974073391353)
      ·
        refine ⟨13123674447693730555043515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17498232596924974073391353 13123674447693730555043515)
        ·
          refine ⟨19685511671540595832565273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13123674447693730555043515 19685511671540595832565273)
          ·
            refine ⟨14764133753655446874423955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19685511671540595832565273 14764133753655446874423955)
            ·
              refine ⟨22146200630483170311635933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14764133753655446874423955 22146200630483170311635933)
              ·
                refine ⟨8304825236431188866863475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22146200630483170311635933 8304825236431188866863475)
                ·
                  refine ⟨12457237854646783300295213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8304825236431188866863475 12457237854646783300295213)
                  ·
                    refine ⟨4671464195492543737610705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12457237854646783300295213 4671464195492543737610705)
                    ·
                      refine ⟨3503598146619407803208029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671464195492543737610705 3503598146619407803208029)
                      ·
                        rfl

theorem cell23_6823233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6823233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823233 prefixEnd_6823233 := by exact prefixLift 6823233
  have htrace : WordTrace (prefixWord ++ tailWord_6823233) baseStart_6823233 baseEnd_6823233 := by
    simpa [prefixWord, tailWord_6823233, baseEnd_6823233] using wordTrace_append hprefix tailTrace_6823233
  have hstable : (prefixWord ++ tailWord_6823233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823233).length < 2 ^ (prefixWord ++ tailWord_6823233).sum := by decide
  have hdescent : baseEnd_6823233 < baseStart_6823233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823235 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 11]
def baseStart_6823235 : Nat := 118140960795 + 6823235 * 2 ^ 59
def prefixEnd_6823235 : Nat := 4983230072969 + 3 ^ 40 * 6823235 * 2
def baseEnd_6823235 : Nat := 389288797064524088375891

theorem tailTrace_6823235 : CollatzResearch.WordTrace tailWord_6823235 prefixEnd_6823235 389288797064524088375891 := by
  unfold tailWord_6823235
  simp only [CollatzResearch.WordTrace]
  refine ⟨248863825435592385607583159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165909216957061590405055439 248863825435592385607583159)
  ·
    refine ⟨373295738153388578411374739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248863825435592385607583159 373295738153388578411374739)
    ·
      refine ⟨559943607230082867617062109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373295738153388578411374739 559943607230082867617062109)
      ·
        refine ⟨209978852711281075356398291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559943607230082867617062109 209978852711281075356398291)
        ·
          refine ⟨314968279066921613034597437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209978852711281075356398291 314968279066921613034597437)
          ·
            refine ⟨118113104650095604887974039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314968279066921613034597437 118113104650095604887974039)
            ·
              refine ⟨177169656975143407331961059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118113104650095604887974039 177169656975143407331961059)
              ·
                refine ⟨265754485462715110997941589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177169656975143407331961059 265754485462715110997941589)
                ·
                  refine ⟨389288797064524088375891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 265754485462715110997941589 389288797064524088375891)
                  ·
                    rfl

theorem cell23_6823235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 11].length) (baseStart_6823235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823235 prefixEnd_6823235 := by exact prefixLift 6823235
  have htrace : WordTrace (prefixWord ++ tailWord_6823235) baseStart_6823235 baseEnd_6823235 := by
    simpa [prefixWord, tailWord_6823235, baseEnd_6823235] using wordTrace_append hprefix tailTrace_6823235
  have hstable : (prefixWord ++ tailWord_6823235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823235).length < 2 ^ (prefixWord ++ tailWord_6823235).sum := by decide
  have hdescent : baseEnd_6823235 < baseStart_6823235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823246 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2]
def baseStart_6823246 : Nat := 118140960795 + 6823246 * 2 ^ 59
def prefixEnd_6823246 : Nat := 4983230072969 + 3 ^ 40 * 6823246 * 2
def baseEnd_6823246 : Nat := 3503604821867916252345469

theorem tailTrace_6823246 : CollatzResearch.WordTrace tailWord_6823246 prefixEnd_6823246 3503604821867916252345469 := by
  unfold tailWord_6823246
  simp only [CollatzResearch.WordTrace]
  refine ⟨31108028329819066810779199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165909484425701689657489061 31108028329819066810779199)
  ·
    refine ⟨46662042494728600216168799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31108028329819066810779199 46662042494728600216168799)
    ·
      refine ⟨69993063742092900324253199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46662042494728600216168799 69993063742092900324253199)
      ·
        refine ⟨104989595613139350486379799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69993063742092900324253199 104989595613139350486379799)
        ·
          refine ⟨157484393419709025729569699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104989595613139350486379799 157484393419709025729569699)
          ·
            refine ⟨236226590129563538594354549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157484393419709025729569699 236226590129563538594354549)
            ·
              refine ⟨22146242824646581743220739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236226590129563538594354549 22146242824646581743220739)
              ·
                refine ⟨33219364236969872614831109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22146242824646581743220739 33219364236969872614831109)
                ·
                  refine ⟨6228630794431851115280833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33219364236969872614831109 6228630794431851115280833)
                  ·
                    refine ⟨4671473095823888336460625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6228630794431851115280833 4671473095823888336460625)
                    ·
                      refine ⟨3503604821867916252345469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671473095823888336460625 3503604821867916252345469)
                      ·
                        rfl

theorem cell23_6823246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_6823246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823246 prefixEnd_6823246 := by exact prefixLift 6823246
  have htrace : WordTrace (prefixWord ++ tailWord_6823246) baseStart_6823246 baseEnd_6823246 := by
    simpa [prefixWord, tailWord_6823246, baseEnd_6823246] using wordTrace_append hprefix tailTrace_6823246
  have hstable : (prefixWord ++ tailWord_6823246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823246).length < 2 ^ (prefixWord ++ tailWord_6823246).sum := by decide
  have hdescent : baseEnd_6823246 < baseStart_6823246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823282 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_6823282 : Nat := 118140960795 + 6823282 * 2 ^ 59
def prefixEnd_6823282 : Nat := 4983230072969 + 3 ^ 40 * 6823282 * 2
def baseEnd_6823282 : Nat := 1167874435723826037165101

theorem tailTrace_6823282 : CollatzResearch.WordTrace tailWord_6823282 prefixEnd_6823282 1167874435723826037165101 := by
  unfold tailWord_6823282
  simp only [CollatzResearch.WordTrace]
  refine ⟨62216384916605528158636025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165910359777614741756362733 62216384916605528158636025)
  ·
    refine ⟨46662288687454146118977019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62216384916605528158636025 46662288687454146118977019)
    ·
      refine ⟨69993433031181219178465529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46662288687454146118977019 69993433031181219178465529)
      ·
        refine ⟨52495074773385914383849147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69993433031181219178465529 52495074773385914383849147)
        ·
          refine ⟨78742612160078871575773721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52495074773385914383849147 78742612160078871575773721)
          ·
            refine ⟨59056959120059153681830291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78742612160078871575773721 59056959120059153681830291)
            ·
              refine ⟨88585438680088730522745437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59056959120059153681830291 88585438680088730522745437)
              ·
                refine ⟨33219539505033273946029539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88585438680088730522745437 33219539505033273946029539)
                ·
                  refine ⟨49829309257549910919044309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33219539505033273946029539 49829309257549910919044309)
                  ·
                    refine ⟨1167874435723826037165101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49829309257549910919044309 1167874435723826037165101)
                    ·
                      rfl

theorem cell23_6823282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_6823282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823282 prefixEnd_6823282 := by exact prefixLift 6823282
  have htrace : WordTrace (prefixWord ++ tailWord_6823282) baseStart_6823282 baseEnd_6823282 := by
    simpa [prefixWord, tailWord_6823282, baseEnd_6823282] using wordTrace_append hprefix tailTrace_6823282
  have hstable : (prefixWord ++ tailWord_6823282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823282).length < 2 ^ (prefixWord ++ tailWord_6823282).sum := by decide
  have hdescent : baseEnd_6823282 < baseStart_6823282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823292 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_6823292 : Nat := 118140960795 + 6823292 * 2 ^ 59
def prefixEnd_6823292 : Nat := 4983230072969 + 3 ^ 40 * 6823292 * 2
def baseEnd_6823292 : Nat := 3503628441978023072370257

theorem tailTrace_6823292 : CollatzResearch.WordTrace tailWord_6823292 prefixEnd_6823292 3503628441978023072370257 := by
  unfold tailWord_6823292
  simp only [CollatzResearch.WordTrace]
  refine ⟨124432952198192942171204065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165910602930923922894938753 124432952198192942171204065)
  ·
    refine ⟨93324714148644706628403049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124432952198192942171204065 93324714148644706628403049)
    ·
      refine ⟨69993535611483529971302287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93324714148644706628403049 69993535611483529971302287)
      ·
        refine ⟨104990303417225294956953431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69993535611483529971302287 104990303417225294956953431)
        ·
          refine ⟨157485455125837942435430147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104990303417225294956953431 157485455125837942435430147)
          ·
            refine ⟨236228182688756913653145221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157485455125837942435430147 236228182688756913653145221)
            ·
              refine ⟨44292784254141921309964729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236228182688756913653145221 44292784254141921309964729)
              ·
                refine ⟨33219588190606440982473547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44292784254141921309964729 33219588190606440982473547)
                ·
                  refine ⟨49829382285909661473710321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33219588190606440982473547 49829382285909661473710321)
                  ·
                    refine ⟨37372036714432246105282741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49829382285909661473710321 37372036714432246105282741)
                    ·
                      refine ⟨3503628441978023072370257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37372036714432246105282741 3503628441978023072370257)
                      ·
                        rfl

theorem cell23_6823292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_6823292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823292 prefixEnd_6823292 := by exact prefixLift 6823292
  have htrace : WordTrace (prefixWord ++ tailWord_6823292) baseStart_6823292 baseEnd_6823292 := by
    simpa [prefixWord, tailWord_6823292, baseEnd_6823292] using wordTrace_append hprefix tailTrace_6823292
  have hstable : (prefixWord ++ tailWord_6823292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823292).length < 2 ^ (prefixWord ++ tailWord_6823292).sum := by decide
  have hdescent : baseEnd_6823292 < baseStart_6823292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823299 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 2, 5]
def baseStart_6823299 : Nat := 118140960795 + 6823299 * 2 ^ 59
def prefixEnd_6823299 : Nat := 4983230072969 + 3 ^ 40 * 6823299 * 2
def baseEnd_6823299 : Nat := 1167877345447534848327575

theorem tailTrace_6823299 : CollatzResearch.WordTrace tailWord_6823299 prefixEnd_6823299 1167877345447534848327575 := by
  unfold tailWord_6823299
  simp only [CollatzResearch.WordTrace]
  refine ⟨248866159707360524537912951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165910773138240349691941967 248866159707360524537912951)
  ·
    refine ⟨373299239561040786806869427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248866159707360524537912951 373299239561040786806869427)
    ·
      refine ⟨559948859341561180210304141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373299239561040786806869427 559948859341561180210304141)
      ·
        refine ⟨209980822253085442578864053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559948859341561180210304141 209980822253085442578864053)
        ·
          refine ⟨19685702086226760241768505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209980822253085442578864053 19685702086226760241768505)
          ·
            refine ⟨14764276564670070181326379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19685702086226760241768505 14764276564670070181326379)
            ·
              refine ⟨22146414847005105271989569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14764276564670070181326379 22146414847005105271989569)
              ·
                refine ⟨16609811135253828953992177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22146414847005105271989569 16609811135253828953992177)
                ·
                  refine ⟨12457358351440371715494133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16609811135253828953992177 12457358351440371715494133)
                  ·
                    refine ⟨1167877345447534848327575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12457358351440371715494133 1167877345447534848327575)
                    ·
                      rfl

theorem cell23_6823299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 5].length) (baseStart_6823299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823299 prefixEnd_6823299 := by exact prefixLift 6823299
  have htrace : WordTrace (prefixWord ++ tailWord_6823299) baseStart_6823299 baseEnd_6823299 := by
    simpa [prefixWord, tailWord_6823299, baseEnd_6823299] using wordTrace_append hprefix tailTrace_6823299
  have hstable : (prefixWord ++ tailWord_6823299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823299).length < 2 ^ (prefixWord ++ tailWord_6823299).sum := by decide
  have hdescent : baseEnd_6823299 < baseStart_6823299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
