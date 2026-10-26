import V185TrunkScan23Chunk0816

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4833849 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 4]
def baseStart_4833849 : Nat := 118140960795 + 4833849 * 2 ^ 59
def prefixEnd_4833849 : Nat := 4983230072969 + 3 ^ 40 * 4833849 * 2
def baseEnd_4833849 : Nat := 2482087948255363277257039

theorem tailTrace_4833849 : CollatzResearch.WordTrace tailWord_4833849 prefixEnd_4833849 2482087948255363277257039 := by
  unfold tailWord_4833849
  simp only [CollatzResearch.WordTrace]
  refine ⟨176304957064798103528464601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117536638043198735685643067 176304957064798103528464601)
  ·
    refine ⟨132228717798598577646348451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176304957064798103528464601 132228717798598577646348451)
    ·
      refine ⟨198343076697897866469522677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132228717798598577646348451 198343076697897866469522677)
      ·
        refine ⟨18594663440427924981517751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198343076697897866469522677 18594663440427924981517751)
        ·
          refine ⟨27891995160641887472276627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18594663440427924981517751 27891995160641887472276627)
          ·
            refine ⟨41837992740962831208414941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27891995160641887472276627 41837992740962831208414941)
            ·
              refine ⟨15689247277861061703155603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41837992740962831208414941 15689247277861061703155603)
              ·
                refine ⟨23533870916791592554733405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15689247277861061703155603 23533870916791592554733405)
                ·
                  refine ⟨8825201593796847208025027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23533870916791592554733405 8825201593796847208025027)
                  ·
                    refine ⟨13237802390695270812037541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8825201593796847208025027 13237802390695270812037541)
                    ·
                      refine ⟨2482087948255363277257039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13237802390695270812037541 2482087948255363277257039)
                      ·
                        rfl

theorem cell23_4833849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_4833849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833849 prefixEnd_4833849 := by exact prefixLift 4833849
  have htrace : WordTrace (prefixWord ++ tailWord_4833849) baseStart_4833849 baseEnd_4833849 := by
    simpa [prefixWord, tailWord_4833849, baseEnd_4833849] using wordTrace_append hprefix tailTrace_4833849
  have hstable : (prefixWord ++ tailWord_4833849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833849).length < 2 ^ (prefixWord ++ tailWord_4833849).sum := by decide
  have hdescent : baseEnd_4833849 < baseStart_4833849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833853 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 2, 3, 2]
def baseStart_4833853 : Nat := 118140960795 + 4833853 * 2 ^ 59
def prefixEnd_4833853 : Nat := 4983230072969 + 3 ^ 40 * 4833853 * 2
def baseEnd_4833853 : Nat := 2482090002177981261607021

theorem tailTrace_4833853 : CollatzResearch.WordTrace tailWord_4833853 prefixEnd_4833853 2482090002177981261607021 := by
  unfold tailWord_4833853
  simp only [CollatzResearch.WordTrace]
  refine ⟨176305102956783612211610213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117536735304522408141073475 176305102956783612211610213)
  ·
    refine ⟨33057206804396927289676915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176305102956783612211610213 33057206804396927289676915)
    ·
      refine ⟨49585810206595390934515373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33057206804396927289676915 49585810206595390934515373)
      ·
        refine ⟨18594678827473271600443265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49585810206595390934515373 18594678827473271600443265)
        ·
          refine ⟨13946009120604953700332449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18594678827473271600443265 13946009120604953700332449)
          ·
            refine ⟨10459506840453715275249337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13946009120604953700332449 10459506840453715275249337)
            ·
              refine ⟨7844630130340286456437003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10459506840453715275249337 7844630130340286456437003)
              ·
                refine ⟨11766945195510429684655505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7844630130340286456437003 11766945195510429684655505)
                ·
                  refine ⟨8825208896632822263491629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11766945195510429684655505 8825208896632822263491629)
                  ·
                    refine ⟨3309453336237308348809361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8825208896632822263491629 3309453336237308348809361)
                    ·
                      refine ⟨2482090002177981261607021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309453336237308348809361 2482090002177981261607021)
                      ·
                        rfl

theorem cell23_4833853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_4833853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833853 prefixEnd_4833853 := by exact prefixLift 4833853
  have htrace : WordTrace (prefixWord ++ tailWord_4833853) baseStart_4833853 baseEnd_4833853 := by
    simpa [prefixWord, tailWord_4833853, baseEnd_4833853] using wordTrace_append hprefix tailTrace_4833853
  have hstable : (prefixWord ++ tailWord_4833853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833853).length < 2 ^ (prefixWord ++ tailWord_4833853).sum := by decide
  have hdescent : baseEnd_4833853 < baseStart_4833853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833876 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_4833876 : Nat := 118140960795 + 4833876 * 2 ^ 59
def prefixEnd_4833876 : Nat := 4983230072969 + 3 ^ 40 * 4833876 * 2
def baseEnd_4833876 : Nat := 827367270744344890539805

theorem tailTrace_4833876 : CollatzResearch.WordTrace tailWord_4833876 prefixEnd_4833876 827367270744344890539805 := by
  unfold tailWord_4833876
  simp only [CollatzResearch.WordTrace]
  refine ⟨88152970917850143569848741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117537294557133524759798321 88152970917850143569848741)
  ·
    refine ⟨16528682047096901919346639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88152970917850143569848741 16528682047096901919346639)
    ·
      refine ⟨24793023070645352879019959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16528682047096901919346639 24793023070645352879019959)
      ·
        refine ⟨37189534605968029318529939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24793023070645352879019959 37189534605968029318529939)
        ·
          refine ⟨55784301908952043977794909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37189534605968029318529939 55784301908952043977794909)
          ·
            refine ⟨20919113215857016491673091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55784301908952043977794909 20919113215857016491673091)
            ·
              refine ⟨31378669823785524737509637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20919113215857016491673091 31378669823785524737509637)
              ·
                refine ⟨5883500591959785888283057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31378669823785524737509637 5883500591959785888283057)
                ·
                  refine ⟨4412625443969839416212293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5883500591959785888283057 4412625443969839416212293)
                  ·
                    refine ⟨827367270744344890539805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4412625443969839416212293 827367270744344890539805)
                    ·
                      rfl

theorem cell23_4833876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_4833876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833876 prefixEnd_4833876 := by exact prefixLift 4833876
  have htrace : WordTrace (prefixWord ++ tailWord_4833876) baseStart_4833876 baseEnd_4833876 := by
    simpa [prefixWord, tailWord_4833876, baseEnd_4833876] using wordTrace_append hprefix tailTrace_4833876
  have hstable : (prefixWord ++ tailWord_4833876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833876).length < 2 ^ (prefixWord ++ tailWord_4833876).sum := by decide
  have hdescent : baseEnd_4833876 < baseStart_4833876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833889 : List Nat := [1, 2, 3, 1, 1, 6, 1, 8]
def baseStart_4833889 : Nat := 118140960795 + 4833889 * 2 ^ 59
def prefixEnd_4833889 : Nat := 4983230072969 + 3 ^ 40 * 4833889 * 2
def baseEnd_4833889 : Nat := 91929943980797893361365

theorem tailTrace_4833889 : CollatzResearch.WordTrace tailWord_4833889 prefixEnd_4833889 91929943980797893361365 := by
  unfold tailWord_4833889
  simp only [CollatzResearch.WordTrace]
  refine ⟨176306415984653190359920721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117537610656435460239947147 176306415984653190359920721)
  ·
    refine ⟨132229811988489892769940541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176306415984653190359920721 132229811988489892769940541)
    ·
      refine ⟨49586179495683709788727703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132229811988489892769940541 49586179495683709788727703)
      ·
        refine ⟨74379269243525564683091555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49586179495683709788727703 74379269243525564683091555)
        ·
          refine ⟨111568903865288347024637333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74379269243525564683091555 111568903865288347024637333)
          ·
            refine ⟨5229792368685391266779875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111568903865288347024637333 5229792368685391266779875)
            ·
              refine ⟨7844688553028086900169813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5229792368685391266779875 7844688553028086900169813)
              ·
                refine ⟨91929943980797893361365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7844688553028086900169813 91929943980797893361365)
                ·
                  rfl

theorem cell23_4833889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 8].length) (baseStart_4833889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833889 prefixEnd_4833889 := by exact prefixLift 4833889
  have htrace : WordTrace (prefixWord ++ tailWord_4833889) baseStart_4833889 baseEnd_4833889 := by
    simpa [prefixWord, tailWord_4833889, baseEnd_4833889] using wordTrace_append hprefix tailTrace_4833889
  have hstable : (prefixWord ++ tailWord_4833889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833889).length < 2 ^ (prefixWord ++ tailWord_4833889).sum := by decide
  have hdescent : baseEnd_4833889 < baseStart_4833889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833906 : List Nat := [3, 2, 1, 2, 4, 1, 3, 7]
def baseStart_4833906 : Nat := 118140960795 + 4833906 * 2 ^ 59
def prefixEnd_4833906 : Nat := 4983230072969 + 3 ^ 40 * 4833906 * 2
def baseEnd_4833906 : Nat := 91930267283432205712751

theorem tailTrace_4833906 : CollatzResearch.WordTrace tailWord_4833906 prefixEnd_4833906 91930267283432205712751 := by
  unfold tailWord_4833906
  simp only [CollatzResearch.WordTrace]
  refine ⟨44076759006397900565822393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117538024017061068175526381 44076759006397900565822393)
  ·
    refine ⟨33057569254798425424366795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44076759006397900565822393 33057569254798425424366795)
    ·
      refine ⟨49586353882197638136550193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33057569254798425424366795 49586353882197638136550193)
      ·
        refine ⟨37189765411648228602412645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49586353882197638136550193 37189765411648228602412645)
        ·
          refine ⟨6973081014684042862952371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37189765411648228602412645 6973081014684042862952371)
          ·
            refine ⟨10459621522026064294428557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6973081014684042862952371 10459621522026064294428557)
            ·
              refine ⟨3922358070759774110410709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10459621522026064294428557 3922358070759774110410709)
              ·
                refine ⟨91930267283432205712751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3922358070759774110410709 91930267283432205712751)
                ·
                  rfl

theorem cell23_4833906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 7].length) (baseStart_4833906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833906 prefixEnd_4833906 := by exact prefixLift 4833906
  have htrace : WordTrace (prefixWord ++ tailWord_4833906) baseStart_4833906 baseEnd_4833906 := by
    simpa [prefixWord, tailWord_4833906, baseEnd_4833906] using wordTrace_append hprefix tailTrace_4833906
  have hstable : (prefixWord ++ tailWord_4833906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833906).length < 2 ^ (prefixWord ++ tailWord_4833906).sum := by decide
  have hdescent : baseEnd_4833906 < baseStart_4833906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833912 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_4833912 : Nat := 118140960795 + 4833912 * 2 ^ 59
def prefixEnd_4833912 : Nat := 4983230072969 + 3 ^ 40 * 4833912 * 2
def baseEnd_4833912 : Nat := 2482120297536596530769249

theorem tailTrace_4833912 : CollatzResearch.WordTrace tailWord_4833912 prefixEnd_4833912 2482120297536596530769249 := by
  unfold tailWord_4833912
  simp only [CollatzResearch.WordTrace]
  refine ⟨88153627431784932644003995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117538169909046576858671993 88153627431784932644003995)
  ·
    refine ⟨132230441147677398966005993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88153627431784932644003995 132230441147677398966005993)
    ·
      refine ⟨99172830860758049224504495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132230441147677398966005993 99172830860758049224504495)
      ·
        refine ⟨148759246291137073836756743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99172830860758049224504495 148759246291137073836756743)
        ·
          refine ⟨223138869436705610755135115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148759246291137073836756743 223138869436705610755135115)
          ·
            refine ⟨334708304155058416132702673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223138869436705610755135115 334708304155058416132702673)
            ·
              refine ⟨251031228116293812099527005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334708304155058416132702673 251031228116293812099527005)
              ·
                refine ⟨94136710543610179537322627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251031228116293812099527005 94136710543610179537322627)
                ·
                  refine ⟨141205065815415269305983941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94136710543610179537322627 141205065815415269305983941)
                  ·
                    refine ⟨26475949840390362994871989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141205065815415269305983941 26475949840390362994871989)
                    ·
                      refine ⟨2482120297536596530769249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26475949840390362994871989 2482120297536596530769249)
                      ·
                        rfl

theorem cell23_4833912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_4833912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833912 prefixEnd_4833912 := by exact prefixLift 4833912
  have htrace : WordTrace (prefixWord ++ tailWord_4833912) baseStart_4833912 baseEnd_4833912 := by
    simpa [prefixWord, tailWord_4833912, baseEnd_4833912] using wordTrace_append hprefix tailTrace_4833912
  have hstable : (prefixWord ++ tailWord_4833912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833912).length < 2 ^ (prefixWord ++ tailWord_4833912).sum := by decide
  have hdescent : baseEnd_4833912 < baseStart_4833912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833917 : List Nat := [1, 4, 1, 1, 5, 1, 2, 3, 1, 2, 2]
def baseStart_4833917 : Nat := 118140960795 + 4833917 * 2 ^ 59
def prefixEnd_4833917 : Nat := 4983230072969 + 3 ^ 40 * 4833917 * 2
def baseEnd_4833917 : Nat := 2482122864939869011206727

theorem tailTrace_4833917 : CollatzResearch.WordTrace tailWord_4833917 prefixEnd_4833917 2482122864939869011206727 := by
  unfold tailWord_4833917
  simp only [CollatzResearch.WordTrace]
  refine ⟨176307437228551751141940005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117538291485701167427960003 176307437228551751141940005)
  ·
    refine ⟨33057644480353453339113751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176307437228551751141940005 33057644480353453339113751)
    ·
      refine ⟨49586466720530180008670627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33057644480353453339113751 49586466720530180008670627)
      ·
        refine ⟨74379700080795270013005941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49586466720530180008670627 74379700080795270013005941)
        ·
          refine ⟨6973096882574556563719307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74379700080795270013005941 6973096882574556563719307)
          ·
            refine ⟨10459645323861834845578961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6973096882574556563719307 10459645323861834845578961)
            ·
              refine ⟨7844733992896376134184221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10459645323861834845578961 7844733992896376134184221)
              ·
                refine ⟨2941775247336141050319083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7844733992896376134184221 2941775247336141050319083)
                ·
                  refine ⟨4412662871004211575478625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941775247336141050319083 4412662871004211575478625)
                  ·
                    refine ⟨3309497153253158681608969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4412662871004211575478625 3309497153253158681608969)
                    ·
                      refine ⟨2482122864939869011206727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309497153253158681608969 2482122864939869011206727)
                      ·
                        rfl

theorem cell23_4833917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_4833917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833917 prefixEnd_4833917 := by exact prefixLift 4833917
  have htrace : WordTrace (prefixWord ++ tailWord_4833917) baseStart_4833917 baseEnd_4833917 := by
    simpa [prefixWord, tailWord_4833917, baseEnd_4833917] using wordTrace_append hprefix tailTrace_4833917
  have hstable : (prefixWord ++ tailWord_4833917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833917).length < 2 ^ (prefixWord ++ tailWord_4833917).sum := by decide
  have hdescent : baseEnd_4833917 < baseStart_4833917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833949 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_4833949 : Nat := 118140960795 + 4833949 * 2 ^ 59
def prefixEnd_4833949 : Nat := 4983230072969 + 3 ^ 40 * 4833949 * 2
def baseEnd_4833949 : Nat := 827379765440270962002193

theorem tailTrace_4833949 : CollatzResearch.WordTrace tailWord_4833949 prefixEnd_4833949 827379765440270962002193 := by
  unfold tailWord_4833949
  simp only [CollatzResearch.WordTrace]
  refine ⟨176308604364435820607104901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117539069576290547071403267 176308604364435820607104901)
  ·
    refine ⟨33057863318331716363832169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176308604364435820607104901 33057863318331716363832169)
    ·
      refine ⟨24793397488748787272874127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33057863318331716363832169 24793397488748787272874127)
      ·
        refine ⟨37190096233123180909311191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24793397488748787272874127 37190096233123180909311191)
        ·
          refine ⟨55785144349684771363966787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37190096233123180909311191 55785144349684771363966787)
          ·
            refine ⟨83677716524527157045950181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55785144349684771363966787 83677716524527157045950181)
            ·
              refine ⟨15689571848348841946115659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83677716524527157045950181 15689571848348841946115659)
              ·
                refine ⟨23534357772523262919173489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15689571848348841946115659 23534357772523262919173489)
                ·
                  refine ⟨17650768329392447189380117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23534357772523262919173489 17650768329392447189380117)
                  ·
                    refine ⟨827379765440270962002193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17650768329392447189380117 827379765440270962002193)
                    ·
                      rfl

theorem cell23_4833949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_4833949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833949 prefixEnd_4833949 := by exact prefixLift 4833949
  have htrace : WordTrace (prefixWord ++ tailWord_4833949) baseStart_4833949 baseEnd_4833949 := by
    simpa [prefixWord, tailWord_4833949, baseEnd_4833949] using wordTrace_append hprefix tailTrace_4833949
  have hstable : (prefixWord ++ tailWord_4833949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833949).length < 2 ^ (prefixWord ++ tailWord_4833949).sum := by decide
  have hdescent : baseEnd_4833949 < baseStart_4833949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4833996 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 7]
def baseStart_4833996 : Nat := 118140960795 + 4833996 * 2 ^ 59
def prefixEnd_4833996 : Nat := 4983230072969 + 3 ^ 40 * 4833996 * 2
def baseEnd_4833996 : Nat := 275795936656841578013207

theorem tailTrace_4833996 : CollatzResearch.WordTrace tailWord_4833996 prefixEnd_4833996 275795936656841578013207 := by
  unfold tailWord_4833996
  simp only [CollatzResearch.WordTrace]
  refine ⟨88155159297632773817032921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117540212396843698422710561 88155159297632773817032921)
  ·
    refine ⟨66116369473224580362774691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88155159297632773817032921 66116369473224580362774691)
    ·
      refine ⟨99174554209836870544162037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66116369473224580362774691 99174554209836870544162037)
      ·
        refine ⟨9297614457172206613515191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99174554209836870544162037 9297614457172206613515191)
        ·
          refine ⟨13946421685758309920272787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9297614457172206613515191 13946421685758309920272787)
          ·
            refine ⟨20919632528637464880409181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13946421685758309920272787 20919632528637464880409181)
            ·
              refine ⟨7844862198239049330153443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20919632528637464880409181 7844862198239049330153443)
              ·
                refine ⟨11767293297358573995230165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7844862198239049330153443 11767293297358573995230165)
                ·
                  refine ⟨275795936656841578013207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11767293297358573995230165 275795936656841578013207)
                  ·
                    rfl

theorem cell23_4833996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_4833996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4833996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4833996 prefixEnd_4833996 := by exact prefixLift 4833996
  have htrace : WordTrace (prefixWord ++ tailWord_4833996) baseStart_4833996 baseEnd_4833996 := by
    simpa [prefixWord, tailWord_4833996, baseEnd_4833996] using wordTrace_append hprefix tailTrace_4833996
  have hstable : (prefixWord ++ tailWord_4833996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4833996).length < 2 ^ (prefixWord ++ tailWord_4833996).sum := by decide
  have hdescent : baseEnd_4833996 < baseStart_4833996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4833996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834007 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 2, 2, 2]
def baseStart_4834007 : Nat := 118140960795 + 4834007 * 2 ^ 59
def prefixEnd_4834007 : Nat := 4983230072969 + 3 ^ 40 * 4834007 * 2
def baseEnd_4834007 : Nat := 2482169078198773659081313

theorem tailTrace_4834007 : CollatzResearch.WordTrace tailWord_4834007 prefixEnd_4834007 2482169078198773659081313 := by
  unfold tailWord_4834007
  simp only [CollatzResearch.WordTrace]
  refine ⟨176310719798225696512716275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117540479865483797675144183 176310719798225696512716275)
  ·
    refine ⟨264466079697338544769074413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176310719798225696512716275 264466079697338544769074413)
    ·
      refine ⟨99174779886501954288402905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264466079697338544769074413 99174779886501954288402905)
      ·
        refine ⟨74381084914876465716302179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99174779886501954288402905 74381084914876465716302179)
        ·
          refine ⟨111571627372314698574453269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74381084914876465716302179 111571627372314698574453269)
          ·
            refine ⟨5229920033077251495677497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111571627372314698574453269 5229920033077251495677497)
            ·
              refine ⟨3922440024807938621758123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5229920033077251495677497 3922440024807938621758123)
              ·
                refine ⟨5883660037211907932637185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3922440024807938621758123 5883660037211907932637185)
                ·
                  refine ⟨4412745027908930949477889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5883660037211907932637185 4412745027908930949477889)
                  ·
                    refine ⟨3309558770931698212108417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4412745027908930949477889 3309558770931698212108417)
                    ·
                      refine ⟨2482169078198773659081313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309558770931698212108417 2482169078198773659081313)
                      ·
                        rfl

theorem cell23_4834007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_4834007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834007 prefixEnd_4834007 := by exact prefixLift 4834007
  have htrace : WordTrace (prefixWord ++ tailWord_4834007) baseStart_4834007 baseEnd_4834007 := by
    simpa [prefixWord, tailWord_4834007, baseEnd_4834007] using wordTrace_append hprefix tailTrace_4834007
  have hstable : (prefixWord ++ tailWord_4834007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834007).length < 2 ^ (prefixWord ++ tailWord_4834007).sum := by decide
  have hdescent : baseEnd_4834007 < baseStart_4834007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834009 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 4, 5]
def baseStart_4834009 : Nat := 118140960795 + 4834009 * 2 ^ 59
def prefixEnd_4834009 : Nat := 4983230072969 + 3 ^ 40 * 4834009 * 2
def baseEnd_4834009 : Nat := 827390035053360883752101

theorem tailTrace_4834009 : CollatzResearch.WordTrace tailWord_4834009 prefixEnd_4834009 827390035053360883752101 := by
  unfold tailWord_4834009
  simp only [CollatzResearch.WordTrace]
  refine ⟨176310792744218450854289081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117540528496145633902859387 176310792744218450854289081)
  ·
    refine ⟨132233094558163838140716811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176310792744218450854289081 132233094558163838140716811)
    ·
      refine ⟨198349641837245757211075217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132233094558163838140716811 198349641837245757211075217)
      ·
        refine ⟨148762231377934317908306413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198349641837245757211075217 148762231377934317908306413)
        ·
          refine ⟨55785836766725369215614905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148762231377934317908306413 55785836766725369215614905)
          ·
            refine ⟨41839377575044026911711179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55785836766725369215614905 41839377575044026911711179)
            ·
              refine ⟨62759066362566040367566769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41839377575044026911711179 62759066362566040367566769)
              ·
                refine ⟨47069299771924530275675077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62759066362566040367566769 47069299771924530275675077)
                ·
                  refine ⟨8825493707235849426689077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47069299771924530275675077 8825493707235849426689077)
                  ·
                    refine ⟨827390035053360883752101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8825493707235849426689077 827390035053360883752101)
                    ·
                      rfl

theorem cell23_4834009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_4834009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834009 prefixEnd_4834009 := by exact prefixLift 4834009
  have htrace : WordTrace (prefixWord ++ tailWord_4834009) baseStart_4834009 baseEnd_4834009 := by
    simpa [prefixWord, tailWord_4834009, baseEnd_4834009] using wordTrace_append hprefix tailTrace_4834009
  have hstable : (prefixWord ++ tailWord_4834009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834009).length < 2 ^ (prefixWord ++ tailWord_4834009).sum := by decide
  have hdescent : baseEnd_4834009 < baseStart_4834009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834049 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_4834049 : Nat := 118140960795 + 4834049 * 2 ^ 59
def prefixEnd_4834049 : Nat := 4983230072969 + 3 ^ 40 * 4834049 * 2
def baseEnd_4834049 : Nat := 2482190644386262494756119

theorem tailTrace_4834049 : CollatzResearch.WordTrace tailWord_4834049 prefixEnd_4834049 2482190644386262494756119 := by
  unfold tailWord_4834049
  simp only [CollatzResearch.WordTrace]
  refine ⟨176312251664073537685745201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117541501109382358457163467 176312251664073537685745201)
  ·
    refine ⟨132234188748055153264308901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176312251664073537685745201 132234188748055153264308901)
    ·
      refine ⟨24793910390260341237057919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132234188748055153264308901 24793910390260341237057919)
      ·
        refine ⟨37190865585390511855586879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24793910390260341237057919 37190865585390511855586879)
        ·
          refine ⟨55786298378085767783380319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37190865585390511855586879 55786298378085767783380319)
          ·
            refine ⟨83679447567128651675070479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55786298378085767783380319 83679447567128651675070479)
            ·
              refine ⟨125519171350692977512605719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83679447567128651675070479 125519171350692977512605719)
              ·
                refine ⟨188278757026039466268908579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125519171350692977512605719 188278757026039466268908579)
                ·
                  refine ⟨282418135539059199403362869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188278757026039466268908579 282418135539059199403362869)
                  ·
                    refine ⟨26476700206786799944065269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 282418135539059199403362869 26476700206786799944065269)
                    ·
                      refine ⟨2482190644386262494756119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26476700206786799944065269 2482190644386262494756119)
                      ·
                        rfl

theorem cell23_4834049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_4834049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834049 prefixEnd_4834049 := by exact prefixLift 4834049
  have htrace : WordTrace (prefixWord ++ tailWord_4834049) baseStart_4834049 baseEnd_4834049 := by
    simpa [prefixWord, tailWord_4834049, baseEnd_4834049] using wordTrace_append hprefix tailTrace_4834049
  have hstable : (prefixWord ++ tailWord_4834049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834049).length < 2 ^ (prefixWord ++ tailWord_4834049).sum := by decide
  have hdescent : baseEnd_4834049 < baseStart_4834049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834059 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 4]
def baseStart_4834059 : Nat := 118140960795 + 4834059 * 2 ^ 59
def prefixEnd_4834059 : Nat := 4983230072969 + 3 ^ 40 * 4834059 * 2
def baseEnd_4834059 : Nat := 2482195779192807455631073

theorem tailTrace_4834059 : CollatzResearch.WordTrace tailWord_4834059 prefixEnd_4834059 2482195779192807455631073 := by
  unfold tailWord_4834059
  simp only [CollatzResearch.WordTrace]
  refine ⟨176312616394037309393609231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117541744262691539595739487 176312616394037309393609231)
  ·
    refine ⟨264468924591055964090413847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176312616394037309393609231 264468924591055964090413847)
    ·
      refine ⟨396703386886583946135620771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264468924591055964090413847 396703386886583946135620771)
      ·
        refine ⟨595055080329875919203431157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396703386886583946135620771 595055080329875919203431157)
        ·
          refine ⟨55786413780925867425321671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 595055080329875919203431157 55786413780925867425321671)
          ·
            refine ⟨83679620671388801137982507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55786413780925867425321671 83679620671388801137982507)
            ·
              refine ⟨125519431007083201706973761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83679620671388801137982507 125519431007083201706973761)
              ·
                refine ⟨94139573255312401280230321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125519431007083201706973761 94139573255312401280230321)
                ·
                  refine ⟨70604679941484300960172741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94139573255312401280230321 70604679941484300960172741)
                  ·
                    refine ⟨13238377489028306430032389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70604679941484300960172741 13238377489028306430032389)
                    ·
                      refine ⟨2482195779192807455631073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13238377489028306430032389 2482195779192807455631073)
                      ·
                        rfl

theorem cell23_4834059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 4].length) (baseStart_4834059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834059 prefixEnd_4834059 := by exact prefixLift 4834059
  have htrace : WordTrace (prefixWord ++ tailWord_4834059) baseStart_4834059 baseEnd_4834059 := by
    simpa [prefixWord, tailWord_4834059, baseEnd_4834059] using wordTrace_append hprefix tailTrace_4834059
  have hstable : (prefixWord ++ tailWord_4834059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834059).length < 2 ^ (prefixWord ++ tailWord_4834059).sum := by decide
  have hdescent : baseEnd_4834059 < baseStart_4834059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834077 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_4834077 : Nat := 118140960795 + 4834077 * 2 ^ 59
def prefixEnd_4834077 : Nat := 4983230072969 + 3 ^ 40 * 4834077 * 2
def baseEnd_4834077 : Nat := 827401673948196128401997

theorem tailTrace_4834077 : CollatzResearch.WordTrace tailWord_4834077 prefixEnd_4834077 827401673948196128401997 := by
  unfold tailWord_4834077
  simp only [CollatzResearch.WordTrace]
  refine ⟨176313272907972098467764485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117542181938648065645176323 176313272907972098467764485)
  ·
    refine ⟨33058738670244768462705841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176313272907972098467764485 33058738670244768462705841)
    ·
      refine ⟨24794054002683576347029381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33058738670244768462705841 24794054002683576347029381)
      ·
        refine ⟨4648885125503170565068009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24794054002683576347029381 4648885125503170565068009)
        ·
          refine ⟨3486663844127377923801007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4648885125503170565068009 3486663844127377923801007)
          ·
            refine ⟨5229995766191066885701511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3486663844127377923801007 5229995766191066885701511)
            ·
              refine ⟨7844993649286600328552267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5229995766191066885701511 7844993649286600328552267)
              ·
                refine ⟨11767490473929900492828401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7844993649286600328552267 11767490473929900492828401)
                ·
                  refine ⟨8825617855447425369621301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11767490473929900492828401 8825617855447425369621301)
                  ·
                    refine ⟨827401673948196128401997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8825617855447425369621301 827401673948196128401997)
                    ·
                      rfl

theorem cell23_4834077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_4834077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834077 prefixEnd_4834077 := by exact prefixLift 4834077
  have htrace : WordTrace (prefixWord ++ tailWord_4834077) baseStart_4834077 baseEnd_4834077 := by
    simpa [prefixWord, tailWord_4834077, baseEnd_4834077] using wordTrace_append hprefix tailTrace_4834077
  have hstable : (prefixWord ++ tailWord_4834077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834077).length < 2 ^ (prefixWord ++ tailWord_4834077).sum := by decide
  have hdescent : baseEnd_4834077 < baseStart_4834077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834133 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 1, 5]
def baseStart_4834133 : Nat := 118140960795 + 4834133 * 2 ^ 59
def prefixEnd_4834133 : Nat := 4983230072969 + 3 ^ 40 * 4834133 * 2
def baseEnd_4834133 : Nat := 827411258920413388701911

theorem tailTrace_4834133 : CollatzResearch.WordTrace tailWord_4834133 prefixEnd_4834133 827411258920413388701911 := by
  unfold tailWord_4834133
  simp only [CollatzResearch.WordTrace]
  refine ⟨176315315395769220031803053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117543543597179480021202035 176315315395769220031803053)
  ·
    refine ⟨66118243273413457511926145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176315315395769220031803053 66118243273413457511926145)
    ·
      refine ⟨49588682455060093133944609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66118243273413457511926145 49588682455060093133944609)
      ·
        refine ⟨37191511841295069850458457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49588682455060093133944609 37191511841295069850458457)
        ·
          refine ⟨27893633880971302387843843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37191511841295069850458457 27893633880971302387843843)
          ·
            refine ⟨41840450821456953581765765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27893633880971302387843843 41840450821456953581765765)
            ·
              refine ⟨7845084529023178796581081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41840450821456953581765765 7845084529023178796581081)
              ·
                refine ⟨5883813396767384097435811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7845084529023178796581081 5883813396767384097435811)
                ·
                  refine ⟨8825720095151076146153717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5883813396767384097435811 8825720095151076146153717)
                  ·
                    refine ⟨827411258920413388701911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8825720095151076146153717 827411258920413388701911)
                    ·
                      rfl

theorem cell23_4834133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_4834133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834133 prefixEnd_4834133 := by exact prefixLift 4834133
  have htrace : WordTrace (prefixWord ++ tailWord_4834133) baseStart_4834133 baseEnd_4834133 := by
    simpa [prefixWord, tailWord_4834133, baseEnd_4834133] using wordTrace_append hprefix tailTrace_4834133
  have hstable : (prefixWord ++ tailWord_4834133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834133).length < 2 ^ (prefixWord ++ tailWord_4834133).sum := by decide
  have hdescent : baseEnd_4834133 < baseStart_4834133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834136 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_4834136 : Nat := 118140960795 + 4834136 * 2 ^ 59
def prefixEnd_4834136 : Nat := 4983230072969 + 3 ^ 40 * 4834136 * 2
def baseEnd_4834136 : Nat := 2482235317203203654368219

theorem tailTrace_4834136 : CollatzResearch.WordTrace tailWord_4834136 prefixEnd_4834136 2482235317203203654368219 := by
  unfold tailWord_4834136
  simp only [CollatzResearch.WordTrace]
  refine ⟨88157712407379175772081131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117543616543172234362774841 88157712407379175772081131)
  ·
    refine ⟨132236568611068763658121697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88157712407379175772081131 132236568611068763658121697)
    ·
      refine ⟨99177426458301572743591273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132236568611068763658121697 99177426458301572743591273)
      ·
        refine ⟨74383069843726179557693455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99177426458301572743591273 74383069843726179557693455)
        ·
          refine ⟨111574604765589269336540183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74383069843726179557693455 111574604765589269336540183)
          ·
            refine ⟨167361907148383904004810275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111574604765589269336540183 167361907148383904004810275)
            ·
              refine ⟨251042860722575856007215413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167361907148383904004810275 251042860722575856007215413)
              ·
                refine ⟨23535268192741486500676445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 251042860722575856007215413 23535268192741486500676445)
                ·
                  refine ⟨8825725572278057437753667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23535268192741486500676445 8825725572278057437753667)
                  ·
                    refine ⟨13238588358417086156630501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8825725572278057437753667 13238588358417086156630501)
                    ·
                      refine ⟨2482235317203203654368219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13238588358417086156630501 2482235317203203654368219)
                      ·
                        rfl

theorem cell23_4834136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_4834136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834136 prefixEnd_4834136 := by exact prefixLift 4834136
  have htrace : WordTrace (prefixWord ++ tailWord_4834136) baseStart_4834136 baseEnd_4834136 := by
    simpa [prefixWord, tailWord_4834136, baseEnd_4834136] using wordTrace_append hprefix tailTrace_4834136
  have hstable : (prefixWord ++ tailWord_4834136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834136).length < 2 ^ (prefixWord ++ tailWord_4834136).sum := by decide
  have hdescent : baseEnd_4834136 < baseStart_4834136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834140 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_4834140 : Nat := 118140960795 + 4834140 * 2 ^ 59
def prefixEnd_4834140 : Nat := 4983230072969 + 3 ^ 40 * 4834140 * 2
def baseEnd_4834140 : Nat := 2482237371125821638718201

theorem tailTrace_4834140 : CollatzResearch.WordTrace tailWord_4834140 prefixEnd_4834140 2482237371125821638718201 := by
  unfold tailWord_4834140
  simp only [CollatzResearch.WordTrace]
  refine ⟨88157785353371930113653937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117543713804495906818205249 88157785353371930113653937)
  ·
    refine ⟨66118339015028947585240453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88157785353371930113653937 66118339015028947585240453)
    ·
      refine ⟨12397188565317927672232585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66118339015028947585240453 12397188565317927672232585)
      ·
        refine ⟨9297891423988445754174439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12397188565317927672232585 9297891423988445754174439)
        ·
          refine ⟨13946837135982668631261659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9297891423988445754174439 13946837135982668631261659)
          ·
            refine ⟨20920255703974002946892489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13946837135982668631261659 20920255703974002946892489)
            ·
              refine ⟨15690191777980502210169367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20920255703974002946892489 15690191777980502210169367)
              ·
                refine ⟨23535287666970753315254051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15690191777980502210169367 23535287666970753315254051)
                ·
                  refine ⟨35302931500456129972881077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23535287666970753315254051 35302931500456129972881077)
                  ·
                    refine ⟨3309649828167762184957601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35302931500456129972881077 3309649828167762184957601)
                    ·
                      refine ⟨2482237371125821638718201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309649828167762184957601 2482237371125821638718201)
                      ·
                        rfl

theorem cell23_4834140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_4834140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834140 prefixEnd_4834140 := by exact prefixLift 4834140
  have htrace : WordTrace (prefixWord ++ tailWord_4834140) baseStart_4834140 baseEnd_4834140 := by
    simpa [prefixWord, tailWord_4834140, baseEnd_4834140] using wordTrace_append hprefix tailTrace_4834140
  have hstable : (prefixWord ++ tailWord_4834140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834140).length < 2 ^ (prefixWord ++ tailWord_4834140).sum := by decide
  have hdescent : baseEnd_4834140 < baseStart_4834140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834147 : List Nat := [1, 1, 1, 5, 3, 1, 3, 3, 1, 1, 3]
def baseStart_4834147 : Nat := 118140960795 + 4834147 * 2 ^ 59
def prefixEnd_4834147 : Nat := 4983230072969 + 3 ^ 40 * 4834147 * 2
def baseEnd_4834147 : Nat := 2482240965490403111330669

theorem tailTrace_4834147 : CollatzResearch.WordTrace tailWord_4834147 prefixEnd_4834147 2482240965490403111330669 := by
  unfold tailWord_4834147
  simp only [CollatzResearch.WordTrace]
  refine ⟨176315826017718500422812695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117543884011812333615208463 176315826017718500422812695)
  ·
    refine ⟨264473739026577750634219043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176315826017718500422812695 264473739026577750634219043)
    ·
      refine ⟨396710608539866625951328565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264473739026577750634219043 396710608539866625951328565)
      ·
        refine ⟨37191619550612496182937053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 396710608539866625951328565 37191619550612496182937053)
        ·
          refine ⟨13946857331479686068601395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37191619550612496182937053 13946857331479686068601395)
          ·
            refine ⟨20920285997219529102902093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13946857331479686068601395 20920285997219529102902093)
            ·
              refine ⟨7845107248957323413588285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20920285997219529102902093 7845107248957323413588285)
              ·
                refine ⟨2941915218358996280095607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7845107248957323413588285 2941915218358996280095607)
                ·
                  refine ⟨4412872827538494420143411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941915218358996280095607 4412872827538494420143411)
                  ·
                    refine ⟨6619309241307741630215117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4412872827538494420143411 6619309241307741630215117)
                    ·
                      refine ⟨2482240965490403111330669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6619309241307741630215117 2482240965490403111330669)
                      ·
                        rfl

theorem cell23_4834147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_4834147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834147 prefixEnd_4834147 := by exact prefixLift 4834147
  have htrace : WordTrace (prefixWord ++ tailWord_4834147) baseStart_4834147 baseEnd_4834147 := by
    simpa [prefixWord, tailWord_4834147, baseEnd_4834147] using wordTrace_append hprefix tailTrace_4834147
  have hstable : (prefixWord ++ tailWord_4834147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834147).length < 2 ^ (prefixWord ++ tailWord_4834147).sum := by decide
  have hdescent : baseEnd_4834147 < baseStart_4834147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834207 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 1, 2, 3]
def baseStart_4834207 : Nat := 118140960795 + 4834207 * 2 ^ 59
def prefixEnd_4834207 : Nat := 4983230072969 + 3 ^ 40 * 4834207 * 2
def baseEnd_4834207 : Nat := 2482271774329672876580393

theorem tailTrace_4834207 : CollatzResearch.WordTrace tailWord_4834207 prefixEnd_4834207 2482271774329672876580393 := by
  unfold tailWord_4834207
  simp only [CollatzResearch.WordTrace]
  refine ⟨176318014397501130669996875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117545342931667420446664583 176318014397501130669996875)
  ·
    refine ⟨264477021596251696004995313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176318014397501130669996875 264477021596251696004995313)
    ·
      refine ⟨198357766197188772003746485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264477021596251696004995313 198357766197188772003746485)
      ·
        refine ⟨18596040580986447375351233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198357766197188772003746485 18596040580986447375351233)
        ·
          refine ⟨13947030435739835531513425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18596040580986447375351233 13947030435739835531513425)
          ·
            refine ⟨10460272826804876648635069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13947030435739835531513425 10460272826804876648635069)
            ·
              refine ⟨3922602310051828743238151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10460272826804876648635069 3922602310051828743238151)
              ·
                refine ⟨5883903465077743114857227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3922602310051828743238151 5883903465077743114857227)
                ·
                  refine ⟨8825855197616614672285841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5883903465077743114857227 8825855197616614672285841)
                  ·
                    refine ⟨6619391398212461004214381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8825855197616614672285841 6619391398212461004214381)
                    ·
                      refine ⟨2482271774329672876580393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6619391398212461004214381 2482271774329672876580393)
                      ·
                        rfl

theorem cell23_4834207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_4834207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834207 prefixEnd_4834207 := by exact prefixLift 4834207
  have htrace : WordTrace (prefixWord ++ tailWord_4834207) baseStart_4834207 baseEnd_4834207 := by
    simpa [prefixWord, tailWord_4834207, baseEnd_4834207] using wordTrace_append hprefix tailTrace_4834207
  have hstable : (prefixWord ++ tailWord_4834207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834207).length < 2 ^ (prefixWord ++ tailWord_4834207).sum := by decide
  have hdescent : baseEnd_4834207 < baseStart_4834207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834243 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 5, 4, 2]
def baseStart_4834243 : Nat := 118140960795 + 4834243 * 2 ^ 59
def prefixEnd_4834243 : Nat := 4983230072969 + 3 ^ 40 * 4834243 * 2
def baseEnd_4834243 : Nat := 2482290259633234735730227

theorem tailTrace_4834243 : CollatzResearch.WordTrace tailWord_4834243 prefixEnd_4834243 2482290259633234735730227 := by
  unfold tailWord_4834243
  simp only [CollatzResearch.WordTrace]
  refine ⟨176319327425370708818307383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117546218283580472545538255 176319327425370708818307383)
  ·
    refine ⟨264478991138056063227461075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176319327425370708818307383 264478991138056063227461075)
    ·
      refine ⟨396718486707084094841191613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264478991138056063227461075 396718486707084094841191613)
      ·
        refine ⟨148769432515156535565446855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 396718486707084094841191613 148769432515156535565446855)
        ·
          refine ⟨223154148772734803348170283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148769432515156535565446855 223154148772734803348170283)
          ·
            refine ⟨334731223159102205022255425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223154148772734803348170283 334731223159102205022255425)
            ·
              refine ⟨251048417369326653766691569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334731223159102205022255425 251048417369326653766691569)
              ·
                refine ⟨188286313026994990325018677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251048417369326653766691569 188286313026994990325018677)
                ·
                  refine ⟨17651841846280780342970501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188286313026994990325018677 17651841846280780342970501)
                  ·
                    refine ⟨3309720346177646314306969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17651841846280780342970501 3309720346177646314306969)
                    ·
                      refine ⟨2482290259633234735730227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309720346177646314306969 2482290259633234735730227)
                      ·
                        rfl

theorem cell23_4834243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 4, 2].length) (baseStart_4834243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834243 prefixEnd_4834243 := by exact prefixLift 4834243
  have htrace : WordTrace (prefixWord ++ tailWord_4834243) baseStart_4834243 baseEnd_4834243 := by
    simpa [prefixWord, tailWord_4834243, baseEnd_4834243] using wordTrace_append hprefix tailTrace_4834243
  have hstable : (prefixWord ++ tailWord_4834243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834243).length < 2 ^ (prefixWord ++ tailWord_4834243).sum := by decide
  have hdescent : baseEnd_4834243 < baseStart_4834243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834256 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 4]
def baseStart_4834256 : Nat := 118140960795 + 4834256 * 2 ^ 59
def prefixEnd_4834256 : Nat := 4983230072969 + 3 ^ 40 * 4834256 * 2
def baseEnd_4834256 : Nat := 2482296934881743184867667

theorem tailTrace_4834256 : CollatzResearch.WordTrace tailWord_4834256 prefixEnd_4834256 2482296934881743184867667 := by
  unfold tailWord_4834256
  simp only [CollatzResearch.WordTrace]
  refine ⟨88159900787161806019265311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117546534382882408025687081 88159900787161806019265311)
  ·
    refine ⟨132239851180742709028897967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88159900787161806019265311 132239851180742709028897967)
    ·
      refine ⟨198359776771114063543346951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132239851180742709028897967 198359776771114063543346951)
      ·
        refine ⟨297539665156671095315020427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198359776771114063543346951 297539665156671095315020427)
        ·
          refine ⟨446309497735006642972530641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297539665156671095315020427 446309497735006642972530641)
          ·
            refine ⟨334732123301254982229397981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446309497735006642972530641 334732123301254982229397981)
            ·
              refine ⟨125524546237970618336024243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334732123301254982229397981 125524546237970618336024243)
              ·
                refine ⟨188286819356955927504036365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125524546237970618336024243 188286819356955927504036365)
                ·
                  refine ⟨70607557258858472814013637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188286819356955927504036365 70607557258858472814013637)
                  ·
                    refine ⟨13238916986035963652627557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70607557258858472814013637 13238916986035963652627557)
                    ·
                      refine ⟨2482296934881743184867667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13238916986035963652627557 2482296934881743184867667)
                      ·
                        rfl

theorem cell23_4834256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_4834256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834256 prefixEnd_4834256 := by exact prefixLift 4834256
  have htrace : WordTrace (prefixWord ++ tailWord_4834256) baseStart_4834256 baseEnd_4834256 := by
    simpa [prefixWord, tailWord_4834256, baseEnd_4834256] using wordTrace_append hprefix tailTrace_4834256
  have hstable : (prefixWord ++ tailWord_4834256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834256).length < 2 ^ (prefixWord ++ tailWord_4834256).sum := by decide
  have hdescent : baseEnd_4834256 < baseStart_4834256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834264 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 1, 3, 2]
def baseStart_4834264 : Nat := 118140960795 + 4834264 * 2 ^ 59
def prefixEnd_4834264 : Nat := 4983230072969 + 3 ^ 40 * 4834264 * 2
def baseEnd_4834264 : Nat := 2482301042726979153567631

theorem tailTrace_4834264 : CollatzResearch.WordTrace tailWord_4834264 prefixEnd_4834264 2482301042726979153567631 := by
  unfold tailWord_4834264
  simp only [CollatzResearch.WordTrace]
  refine ⟨88160046679147314702410923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117546728905529752936547897 88160046679147314702410923)
  ·
    refine ⟨132240070018720972053616385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88160046679147314702410923 132240070018720972053616385)
    ·
      refine ⟨99180052514040729040212289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132240070018720972053616385 99180052514040729040212289)
      ·
        refine ⟨74385039385530546780159217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99180052514040729040212289 74385039385530546780159217)
        ·
          refine ⟨55788779539147910085119413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74385039385530546780159217 55788779539147910085119413)
          ·
            refine ⟨5230198081795116570479945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55788779539147910085119413 5230198081795116570479945)
            ·
              refine ⟨3922648561346337427859959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5230198081795116570479945 3922648561346337427859959)
              ·
                refine ⟨5883972842019506141789939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3922648561346337427859959 5883972842019506141789939)
                ·
                  refine ⟨8825959263029259212684909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5883972842019506141789939 8825959263029259212684909)
                  ·
                    refine ⟨3309734723635972204756841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8825959263029259212684909 3309734723635972204756841)
                    ·
                      refine ⟨2482301042726979153567631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309734723635972204756841 2482301042726979153567631)
                      ·
                        rfl

theorem cell23_4834264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_4834264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834264 prefixEnd_4834264 := by exact prefixLift 4834264
  have htrace : WordTrace (prefixWord ++ tailWord_4834264) baseStart_4834264 baseEnd_4834264 := by
    simpa [prefixWord, tailWord_4834264, baseEnd_4834264] using wordTrace_append hprefix tailTrace_4834264
  have hstable : (prefixWord ++ tailWord_4834264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834264).length < 2 ^ (prefixWord ++ tailWord_4834264).sum := by decide
  have hdescent : baseEnd_4834264 < baseStart_4834264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834276 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_4834276 : Nat := 118140960795 + 4834276 * 2 ^ 59
def prefixEnd_4834276 : Nat := 4983230072969 + 3 ^ 40 * 4834276 * 2
def baseEnd_4834276 : Nat := 2482307204494833106617575

theorem tailTrace_4834276 : CollatzResearch.WordTrace tailWord_4834276 prefixEnd_4834276 2482307204494833106617575 := by
  unfold tailWord_4834276
  simp only [CollatzResearch.WordTrace]
  refine ⟨88160265517125577727129341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117547020689500770302839121 88160265517125577727129341)
  ·
    refine ⟨33060099568922091647673503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88160265517125577727129341 33060099568922091647673503)
    ·
      refine ⟨49590149353383137471510255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33060099568922091647673503 49590149353383137471510255)
      ·
        refine ⟨74385224030074706207265383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49590149353383137471510255 74385224030074706207265383)
        ·
          refine ⟨111577836045112059310898075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74385224030074706207265383 111577836045112059310898075)
          ·
            refine ⟨167366754067668088966347113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111577836045112059310898075 167366754067668088966347113)
            ·
              refine ⟨125525065550751066724760335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167366754067668088966347113 125525065550751066724760335)
              ·
                refine ⟨188287598326126600087140503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125525065550751066724760335 188287598326126600087140503)
                ·
                  refine ⟨282431397489189900130710755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188287598326126600087140503 282431397489189900130710755)
                  ·
                    refine ⟨423647096233784850196066133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 282431397489189900130710755 423647096233784850196066133)
                    ·
                      refine ⟨2482307204494833106617575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 423647096233784850196066133 2482307204494833106617575)
                      ·
                        rfl

theorem cell23_4834276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_4834276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834276 prefixEnd_4834276 := by exact prefixLift 4834276
  have htrace : WordTrace (prefixWord ++ tailWord_4834276) baseStart_4834276 baseEnd_4834276 := by
    simpa [prefixWord, tailWord_4834276, baseEnd_4834276] using wordTrace_append hprefix tailTrace_4834276
  have hstable : (prefixWord ++ tailWord_4834276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834276).length < 2 ^ (prefixWord ++ tailWord_4834276).sum := by decide
  have hdescent : baseEnd_4834276 < baseStart_4834276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834294 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_4834294 : Nat := 118140960795 + 4834294 * 2 ^ 59
def prefixEnd_4834294 : Nat := 4983230072969 + 3 ^ 40 * 4834294 * 2
def baseEnd_4834294 : Nat := 2482316447146614036192493

theorem tailTrace_4834294 : CollatzResearch.WordTrace tailWord_4834294 prefixEnd_4834294 2482316447146614036192493 := by
  unfold tailWord_4834294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11020074221761621533025871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117547458365457296352275957 11020074221761621533025871)
  ·
    refine ⟨16530111332642432299538807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11020074221761621533025871 16530111332642432299538807)
    ·
      refine ⟨24795166998963648449308211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16530111332642432299538807 24795166998963648449308211)
      ·
        refine ⟨37192750498445472673962317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24795166998963648449308211 37192750498445472673962317)
        ·
          refine ⟨13947281436917052252735869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37192750498445472673962317 13947281436917052252735869)
          ·
            refine ⟨5230230538843894594775951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13947281436917052252735869 5230230538843894594775951)
            ·
              refine ⟨7845345808265841892163927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230230538843894594775951 7845345808265841892163927)
              ·
                refine ⟨11768018712398762838245891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7845345808265841892163927 11768018712398762838245891)
                ·
                  refine ⟨17652028068598144257368837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11768018712398762838245891 17652028068598144257368837)
                  ·
                    refine ⟨3309755262862152048256657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17652028068598144257368837 3309755262862152048256657)
                    ·
                      refine ⟨2482316447146614036192493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309755262862152048256657 2482316447146614036192493)
                      ·
                        rfl

theorem cell23_4834294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_4834294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834294 prefixEnd_4834294 := by exact prefixLift 4834294
  have htrace : WordTrace (prefixWord ++ tailWord_4834294) baseStart_4834294 baseEnd_4834294 := by
    simpa [prefixWord, tailWord_4834294, baseEnd_4834294] using wordTrace_append hprefix tailTrace_4834294
  have hstable : (prefixWord ++ tailWord_4834294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834294).length < 2 ^ (prefixWord ++ tailWord_4834294).sum := by decide
  have hdescent : baseEnd_4834294 < baseStart_4834294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834340 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_4834340 : Nat := 118140960795 + 4834340 * 2 ^ 59
def prefixEnd_4834340 : Nat := 4983230072969 + 3 ^ 40 * 4834340 * 2
def baseEnd_4834340 : Nat := 2482340067256720856217281

theorem tailTrace_4834340 : CollatzResearch.WordTrace tailWord_4834340 prefixEnd_4834340 2482340067256720856217281 := by
  unfold tailWord_4834340
  simp only [CollatzResearch.WordTrace]
  refine ⟨88161432653009647192294237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117548576870679529589725649 88161432653009647192294237)
  ·
    refine ⟨33060537244878617697110339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88161432653009647192294237 33060537244878617697110339)
    ·
      refine ⟨49590805867317926545665509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33060537244878617697110339 49590805867317926545665509)
      ·
        refine ⟨9298276100122111227312283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49590805867317926545665509 9298276100122111227312283)
        ·
          refine ⟨13947414150183166840968425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9298276100122111227312283 13947414150183166840968425)
          ·
            refine ⟨10460560612637375130726319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13947414150183166840968425 10460560612637375130726319)
            ·
              refine ⟨15690840918956062696089479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10460560612637375130726319 15690840918956062696089479)
              ·
                refine ⟨23536261378434094044134219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15690840918956062696089479 23536261378434094044134219)
                ·
                  refine ⟨35304392067651141066201329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23536261378434094044134219 35304392067651141066201329)
                  ·
                    refine ⟨26478294050738355799650997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35304392067651141066201329 26478294050738355799650997)
                    ·
                      refine ⟨2482340067256720856217281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26478294050738355799650997 2482340067256720856217281)
                      ·
                        rfl

theorem cell23_4834340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_4834340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834340 prefixEnd_4834340 := by exact prefixLift 4834340
  have htrace : WordTrace (prefixWord ++ tailWord_4834340) baseStart_4834340 baseEnd_4834340 := by
    simpa [prefixWord, tailWord_4834340, baseEnd_4834340] using wordTrace_append hprefix tailTrace_4834340
  have hstable : (prefixWord ++ tailWord_4834340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834340).length < 2 ^ (prefixWord ++ tailWord_4834340).sum := by decide
  have hdescent : baseEnd_4834340 < baseStart_4834340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834350 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_4834350 : Nat := 118140960795 + 4834350 * 2 ^ 59
def prefixEnd_4834350 : Nat := 4983230072969 + 3 ^ 40 * 4834350 * 2
def baseEnd_4834350 : Nat := 2482345202063265817092235

theorem tailTrace_4834350 : CollatzResearch.WordTrace tailWord_4834350 prefixEnd_4834350 2482345202063265817092235 := by
  unfold tailWord_4834350
  simp only [CollatzResearch.WordTrace]
  refine ⟨22040403754497883261556563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117548820023988710728301669 22040403754497883261556563)
  ·
    refine ⟨33060605631746824892334845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22040403754497883261556563 33060605631746824892334845)
    ·
      refine ⟨12397727111905059334625567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33060605631746824892334845 12397727111905059334625567)
      ·
        refine ⟨18596590667857589001938351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12397727111905059334625567 18596590667857589001938351)
        ·
          refine ⟨27894886001786383502907527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18596590667857589001938351 27894886001786383502907527)
          ·
            refine ⟨41842329002679575254361291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27894886001786383502907527 41842329002679575254361291)
            ·
              refine ⟨62763493504019362881541937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41842329002679575254361291 62763493504019362881541937)
              ·
                refine ⟨47072620128014522161156453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62763493504019362881541937 47072620128014522161156453)
                ·
                  refine ⟨8826116274002722905216835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47072620128014522161156453 8826116274002722905216835)
                  ·
                    refine ⟨13239174411004084357825253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8826116274002722905216835 13239174411004084357825253)
                    ·
                      refine ⟨2482345202063265817092235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13239174411004084357825253 2482345202063265817092235)
                      ·
                        rfl

theorem cell23_4834350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_4834350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834350 prefixEnd_4834350 := by exact prefixLift 4834350
  have htrace : WordTrace (prefixWord ++ tailWord_4834350) baseStart_4834350 baseEnd_4834350 := by
    simpa [prefixWord, tailWord_4834350, baseEnd_4834350] using wordTrace_append hprefix tailTrace_4834350
  have hstable : (prefixWord ++ tailWord_4834350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834350).length < 2 ^ (prefixWord ++ tailWord_4834350).sum := by decide
  have hdescent : baseEnd_4834350 < baseStart_4834350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834421 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4834421 : Nat := 118140960795 + 4834421 * 2 ^ 59
def prefixEnd_4834421 : Nat := 4983230072969 + 3 ^ 40 * 4834421 * 2
def baseEnd_4834421 : Nat := 2482381659189735039304409

theorem tailTrace_4834421 : CollatzResearch.WordTrace tailWord_4834421 prefixEnd_4834421 2482381659189735039304409 := by
  unfold tailWord_4834421
  simp only [CollatzResearch.WordTrace]
  refine ⟨176325819618725845218287117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117550546412483896812191411 176325819618725845218287117)
  ·
    refine ⟨66122182357022191956857669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176325819618725845218287117 66122182357022191956857669)
    ·
      refine ⟨12397909191941660991910813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66122182357022191956857669 12397909191941660991910813)
      ·
        refine ⟨4649215946978122871966555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12397909191941660991910813 4649215946978122871966555)
        ·
          refine ⟨6973823920467184307949833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4649215946978122871966555 6973823920467184307949833)
          ·
            refine ⟨5230367940350388230962375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6973823920467184307949833 5230367940350388230962375)
            ·
              refine ⟨7845551910525582346443563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230367940350388230962375 7845551910525582346443563)
              ·
                refine ⟨11768327865788373519665345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7845551910525582346443563 11768327865788373519665345)
                ·
                  refine ⟨8826245899341280139749009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11768327865788373519665345 8826245899341280139749009)
                  ·
                    refine ⟨6619684424505960104811757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8826245899341280139749009 6619684424505960104811757)
                    ·
                      refine ⟨2482381659189735039304409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6619684424505960104811757 2482381659189735039304409)
                      ·
                        rfl

theorem cell23_4834421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4834421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834421 prefixEnd_4834421 := by exact prefixLift 4834421
  have htrace : WordTrace (prefixWord ++ tailWord_4834421) baseStart_4834421 baseEnd_4834421 := by
    simpa [prefixWord, tailWord_4834421, baseEnd_4834421] using wordTrace_append hprefix tailTrace_4834421
  have hstable : (prefixWord ++ tailWord_4834421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834421).length < 2 ^ (prefixWord ++ tailWord_4834421).sum := by decide
  have hdescent : baseEnd_4834421 < baseStart_4834421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834437 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 1, 5]
def baseStart_4834437 : Nat := 118140960795 + 4834437 * 2 ^ 59
def prefixEnd_4834437 : Nat := 4983230072969 + 3 ^ 40 * 4834437 * 2
def baseEnd_4834437 : Nat := 827463291626735658901445

theorem tailTrace_4834437 : CollatzResearch.WordTrace tailWord_4834437 prefixEnd_4834437 827463291626735658901445 := by
  unfold tailWord_4834437
  simp only [CollatzResearch.WordTrace]
  refine ⟨176326403186667879950869565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117550935457778586633913043 176326403186667879950869565)
  ·
    refine ⟨66122401195000454981576087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176326403186667879950869565 66122401195000454981576087)
    ·
      refine ⟨99183601792500682472364131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66122401195000454981576087 99183601792500682472364131)
      ·
        refine ⟨148775402688751023708546197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99183601792500682472364131 148775402688751023708546197)
        ·
          refine ⟨6973847001035204236338103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 148775402688751023708546197 6973847001035204236338103)
          ·
            refine ⟨10460770501552806354507155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6973847001035204236338103 10460770501552806354507155)
            ·
              refine ⟨15691155752329209531760733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10460770501552806354507155 15691155752329209531760733)
              ·
                refine ⟨5884183407123453574410275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15691155752329209531760733 5884183407123453574410275)
                ·
                  refine ⟨8826275110685180361615413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5884183407123453574410275 8826275110685180361615413)
                  ·
                    refine ⟨827463291626735658901445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8826275110685180361615413 827463291626735658901445)
                    ·
                      rfl

theorem cell23_4834437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_4834437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834437 prefixEnd_4834437 := by exact prefixLift 4834437
  have htrace : WordTrace (prefixWord ++ tailWord_4834437) baseStart_4834437 baseEnd_4834437 := by
    simpa [prefixWord, tailWord_4834437, baseEnd_4834437] using wordTrace_append hprefix tailTrace_4834437
  have hstable : (prefixWord ++ tailWord_4834437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834437).length < 2 ^ (prefixWord ++ tailWord_4834437).sum := by decide
  have hdescent : baseEnd_4834437 < baseStart_4834437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834443 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 5]
def baseStart_4834443 : Nat := 118140960795 + 4834443 * 2 ^ 59
def prefixEnd_4834443 : Nat := 4983230072969 + 3 ^ 40 * 4834443 * 2
def baseEnd_4834443 : Nat := 2482392955764133953229307

theorem tailTrace_4834443 : CollatzResearch.WordTrace tailWord_4834443 prefixEnd_4834443 2482392955764133953229307 := by
  unfold tailWord_4834443
  simp only [CollatzResearch.WordTrace]
  refine ⟨176326622024646142975587983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117551081349764095317058655 176326622024646142975587983)
  ·
    refine ⟨264489933036969214463381975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176326622024646142975587983 264489933036969214463381975)
    ·
      refine ⟨396734899555453821695072963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264489933036969214463381975 396734899555453821695072963)
      ·
        refine ⟨595102349333180732542609445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396734899555453821695072963 595102349333180732542609445)
        ·
          refine ⟨111581690499971387351739271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 595102349333180732542609445 111581690499971387351739271)
          ·
            refine ⟨167372535749957081027608907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111581690499971387351739271 167372535749957081027608907)
            ·
              refine ⟨251058803624935621541413361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167372535749957081027608907 251058803624935621541413361)
              ·
                refine ⟨188294102718701716156060021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251058803624935621541413361 188294102718701716156060021)
                ·
                  refine ⟨17652572129878285889630627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188294102718701716156060021 17652572129878285889630627)
                  ·
                    refine ⟨26478858194817428834445941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17652572129878285889630627 26478858194817428834445941)
                    ·
                      refine ⟨2482392955764133953229307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26478858194817428834445941 2482392955764133953229307)
                      ·
                        rfl

theorem cell23_4834443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 5].length) (baseStart_4834443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834443 prefixEnd_4834443 := by exact prefixLift 4834443
  have htrace : WordTrace (prefixWord ++ tailWord_4834443) baseStart_4834443 baseEnd_4834443 := by
    simpa [prefixWord, tailWord_4834443, baseEnd_4834443] using wordTrace_append hprefix tailTrace_4834443
  have hstable : (prefixWord ++ tailWord_4834443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834443).length < 2 ^ (prefixWord ++ tailWord_4834443).sum := by decide
  have hdescent : baseEnd_4834443 < baseStart_4834443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834460 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4834460 : Nat := 118140960795 + 4834460 * 2 ^ 59
def prefixEnd_4834460 : Nat := 4983230072969 + 3 ^ 40 * 4834460 * 2
def baseEnd_4834460 : Nat := 2482401684935260386716729

theorem tailTrace_4834460 : CollatzResearch.WordTrace tailWord_4834460 prefixEnd_4834460 2482401684935260386716729 := by
  unfold tailWord_4834460
  simp only [CollatzResearch.WordTrace]
  refine ⟨88163621032792277439478417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117551494710389703252637889 88163621032792277439478417)
  ·
    refine ⟨66122715774594208079608813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88163621032792277439478417 66122715774594208079608813)
    ·
      refine ⟨24796018415472828029853305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66122715774594208079608813 24796018415472828029853305)
      ·
        refine ⟨18597013811604621022389979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24796018415472828029853305 18597013811604621022389979)
        ·
          refine ⟨27895520717406931533584969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18597013811604621022389979 27895520717406931533584969)
          ·
            refine ⟨20921640538055198650188727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27895520717406931533584969 20921640538055198650188727)
            ·
              refine ⟨31382460807082797975283091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20921640538055198650188727 31382460807082797975283091)
              ·
                refine ⟨47073691210624196962924637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31382460807082797975283091 47073691210624196962924637)
                ·
                  refine ⟨17652634203984073861096739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47073691210624196962924637 17652634203984073861096739)
                  ·
                    refine ⟨26478951305976110791645109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17652634203984073861096739 26478951305976110791645109)
                    ·
                      refine ⟨2482401684935260386716729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26478951305976110791645109 2482401684935260386716729)
                      ·
                        rfl

theorem cell23_4834460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4834460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834460 prefixEnd_4834460 := by exact prefixLift 4834460
  have htrace : WordTrace (prefixWord ++ tailWord_4834460) baseStart_4834460 baseEnd_4834460 := by
    simpa [prefixWord, tailWord_4834460, baseEnd_4834460] using wordTrace_append hprefix tailTrace_4834460
  have hstable : (prefixWord ++ tailWord_4834460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834460).length < 2 ^ (prefixWord ++ tailWord_4834460).sum := by decide
  have hdescent : baseEnd_4834460 < baseStart_4834460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834474 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4834474 : Nat := 118140960795 + 4834474 * 2 ^ 59
def prefixEnd_4834474 : Nat := 4983230072969 + 3 ^ 40 * 4834474 * 2
def baseEnd_4834474 : Nat := 2482408873664423331941665

theorem tailTrace_4834474 : CollatzResearch.WordTrace tailWord_4834474 prefixEnd_4834474 2482408873664423331941665 := by
  unfold tailWord_4834474
  simp only [CollatzResearch.WordTrace]
  refine ⟨44081938171883458817491619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117551835125022556846644317 44081938171883458817491619)
  ·
    refine ⟨66122907257825188226237429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44081938171883458817491619 66122907257825188226237429)
    ·
      refine ⟨6199022555421111396209759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66122907257825188226237429 6199022555421111396209759)
      ·
        refine ⟨9298533833131667094314639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6199022555421111396209759 9298533833131667094314639)
        ·
          refine ⟨13947800749697500641471959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9298533833131667094314639 13947800749697500641471959)
          ·
            refine ⟨20921701124546250962207939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13947800749697500641471959 20921701124546250962207939)
            ·
              refine ⟨31382551686819376443311909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20921701124546250962207939 31382551686819376443311909)
              ·
                refine ⟨5884228441278633083120983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31382551686819376443311909 5884228441278633083120983)
                ·
                  refine ⟨8826342661917949624681475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5884228441278633083120983 8826342661917949624681475)
                  ·
                    refine ⟨13239513992876924437022213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8826342661917949624681475 13239513992876924437022213)
                    ·
                      refine ⟨2482408873664423331941665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13239513992876924437022213 2482408873664423331941665)
                      ·
                        rfl

theorem cell23_4834474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4834474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834474 prefixEnd_4834474 := by exact prefixLift 4834474
  have htrace : WordTrace (prefixWord ++ tailWord_4834474) baseStart_4834474 baseEnd_4834474 := by
    simpa [prefixWord, tailWord_4834474, baseEnd_4834474] using wordTrace_append hprefix tailTrace_4834474
  have hstable : (prefixWord ++ tailWord_4834474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834474).length < 2 ^ (prefixWord ++ tailWord_4834474).sum := by decide
  have hdescent : baseEnd_4834474 < baseStart_4834474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834490 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3]
def baseStart_4834490 : Nat := 118140960795 + 4834490 * 2 ^ 59
def prefixEnd_4834490 : Nat := 4983230072969 + 3 ^ 40 * 4834490 * 2
def baseEnd_4834490 : Nat := 2482417089354895269341591

theorem tailTrace_4834490 : CollatzResearch.WordTrace tailWord_4834490 prefixEnd_4834490 2482417089354895269341591 := by
  unfold tailWord_4834490
  simp only [CollatzResearch.WordTrace]
  refine ⟨44082084063868967500637231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117552224170317246668365949 44082084063868967500637231)
  ·
    refine ⟨66123126095803451250955847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44082084063868967500637231 66123126095803451250955847)
    ·
      refine ⟨99184689143705176876433771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66123126095803451250955847 99184689143705176876433771)
      ·
        refine ⟨148777033715557765314650657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99184689143705176876433771 148777033715557765314650657)
        ·
          refine ⟨111582775286668323985987993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148777033715557765314650657 111582775286668323985987993)
          ·
            refine ⟨83687081465001242989490995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111582775286668323985987993 83687081465001242989490995)
            ·
              refine ⟨125530622197501864484236493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83687081465001242989490995 125530622197501864484236493)
              ·
                refine ⟨47073983324063199181588685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125530622197501864484236493 47073983324063199181588685)
                ·
                  refine ⟨17652743746523699693095757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47073983324063199181588685 17652743746523699693095757)
                  ·
                    refine ⟨6619778904946387384910909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17652743746523699693095757 6619778904946387384910909)
                    ·
                      refine ⟨2482417089354895269341591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6619778904946387384910909 2482417089354895269341591)
                      ·
                        rfl

theorem cell23_4834490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_4834490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834490 prefixEnd_4834490 := by exact prefixLift 4834490
  have htrace : WordTrace (prefixWord ++ tailWord_4834490) baseStart_4834490 baseEnd_4834490 := by
    simpa [prefixWord, tailWord_4834490, baseEnd_4834490] using wordTrace_append hprefix tailTrace_4834490
  have hstable : (prefixWord ++ tailWord_4834490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834490).length < 2 ^ (prefixWord ++ tailWord_4834490).sum := by decide
  have hdescent : baseEnd_4834490 < baseStart_4834490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834494 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_4834494 : Nat := 118140960795 + 4834494 * 2 ^ 59
def prefixEnd_4834494 : Nat := 4983230072969 + 3 ^ 40 * 4834494 * 2
def baseEnd_4834494 : Nat := 2482419143277513253691573

theorem tailTrace_4834494 : CollatzResearch.WordTrace tailWord_4834494 prefixEnd_4834494 2482419143277513253691573 := by
  unfold tailWord_4834494
  simp only [CollatzResearch.WordTrace]
  refine ⟨22041060268432672335711817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117552321431640919123796357 22041060268432672335711817)
  ·
    refine ⟨16530795201324504251783863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22041060268432672335711817 16530795201324504251783863)
    ·
      refine ⟨24796192801986756377675795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16530795201324504251783863 24796192801986756377675795)
      ·
        refine ⟨37194289202980134566513693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24796192801986756377675795 37194289202980134566513693)
        ·
          refine ⟨13947858451117550462442635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37194289202980134566513693 13947858451117550462442635)
          ·
            refine ⟨20921787676676325693663953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13947858451117550462442635 20921787676676325693663953)
            ·
              refine ⟨15691340757507244270247965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20921787676676325693663953 15691340757507244270247965)
              ·
                refine ⟨5884252784065216601342987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15691340757507244270247965 5884252784065216601342987)
                ·
                  refine ⟨8826379176097824902014481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5884252784065216601342987 8826379176097824902014481)
                  ·
                    refine ⟨6619784382073368676510861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8826379176097824902014481 6619784382073368676510861)
                    ·
                      refine ⟨2482419143277513253691573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6619784382073368676510861 2482419143277513253691573)
                      ·
                        rfl

theorem cell23_4834494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_4834494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834494 prefixEnd_4834494 := by exact prefixLift 4834494
  have htrace : WordTrace (prefixWord ++ tailWord_4834494) baseStart_4834494 baseEnd_4834494 := by
    simpa [prefixWord, tailWord_4834494, baseEnd_4834494] using wordTrace_append hprefix tailTrace_4834494
  have hstable : (prefixWord ++ tailWord_4834494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834494).length < 2 ^ (prefixWord ++ tailWord_4834494).sum := by decide
  have hdescent : baseEnd_4834494 < baseStart_4834494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834497 : List Nat := [1, 2, 6, 1, 1, 3, 9]
def baseStart_4834497 : Nat := 118140960795 + 4834497 * 2 ^ 59
def prefixEnd_4834497 : Nat := 4983230072969 + 3 ^ 40 * 4834497 * 2
def baseEnd_4834497 : Nat := 30647168934808354838939

theorem tailTrace_4834497 : CollatzResearch.WordTrace tailWord_4834497 prefixEnd_4834497 30647168934808354838939 := by
  unfold tailWord_4834497
  simp only [CollatzResearch.WordTrace]
  refine ⟨176328591566450510198053745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117552394377633673465369163 176328591566450510198053745)
  ·
    refine ⟨132246443674837882648540309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176328591566450510198053745 132246443674837882648540309)
    ·
      refine ⟨6199052047258025749150327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132246443674837882648540309 6199052047258025749150327)
      ·
        refine ⟨9298578070887038623725491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6199052047258025749150327 9298578070887038623725491)
        ·
          refine ⟨13947867106330557935588237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9298578070887038623725491 13947867106330557935588237)
          ·
            refine ⟨5230450164873959225845589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13947867106330557935588237 5230450164873959225845589)
            ·
              refine ⟨30647168934808354838939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5230450164873959225845589 30647168934808354838939)
              ·
                rfl

theorem cell23_4834497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 9].length) (baseStart_4834497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834497 prefixEnd_4834497 := by exact prefixLift 4834497
  have htrace : WordTrace (prefixWord ++ tailWord_4834497) baseStart_4834497 baseEnd_4834497 := by
    simpa [prefixWord, tailWord_4834497, baseEnd_4834497] using wordTrace_append hprefix tailTrace_4834497
  have hstable : (prefixWord ++ tailWord_4834497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834497).length < 2 ^ (prefixWord ++ tailWord_4834497).sum := by decide
  have hdescent : baseEnd_4834497 < baseStart_4834497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834502 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_4834502 : Nat := 118140960795 + 4834502 * 2 ^ 59
def prefixEnd_4834502 : Nat := 4983230072969 + 3 ^ 40 * 4834502 * 2
def baseEnd_4834502 : Nat := 2482423251122749222391537

theorem tailTrace_4834502 : CollatzResearch.WordTrace tailWord_4834502 prefixEnd_4834502 2482423251122749222391537 := by
  unfold tailWord_4834502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5510274185357262376624555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 117552515954288264034657173 5510274185357262376624555)
  ·
    refine ⟨8265411278035893564936833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5510274185357262376624555 8265411278035893564936833)
    ·
      refine ⟨6199058458526920173702625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8265411278035893564936833 6199058458526920173702625)
      ·
        refine ⟨4649293843895190130276969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6199058458526920173702625 4649293843895190130276969)
        ·
          refine ⟨3486970382921392597707727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4649293843895190130276969 3486970382921392597707727)
          ·
            refine ⟨5230455574382088896561591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3486970382921392597707727 5230455574382088896561591)
            ·
              refine ⟨7845683361573133344842387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230455574382088896561591 7845683361573133344842387)
              ·
                refine ⟨11768525042359700017263581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7845683361573133344842387 11768525042359700017263581)
                ·
                  refine ⟨4413196890884887506473843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11768525042359700017263581 4413196890884887506473843)
                  ·
                    refine ⟨6619795336327331259710765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4413196890884887506473843 6619795336327331259710765)
                    ·
                      refine ⟨2482423251122749222391537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6619795336327331259710765 2482423251122749222391537)
                      ·
                        rfl

theorem cell23_4834502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_4834502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834502 prefixEnd_4834502 := by exact prefixLift 4834502
  have htrace : WordTrace (prefixWord ++ tailWord_4834502) baseStart_4834502 baseEnd_4834502 := by
    simpa [prefixWord, tailWord_4834502, baseEnd_4834502] using wordTrace_append hprefix tailTrace_4834502
  have hstable : (prefixWord ++ tailWord_4834502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834502).length < 2 ^ (prefixWord ++ tailWord_4834502).sum := by decide
  have hdescent : baseEnd_4834502 < baseStart_4834502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834547 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 3, 4, 2]
def baseStart_4834547 : Nat := 118140960795 + 4834547 * 2 ^ 59
def prefixEnd_4834547 : Nat := 4983230072969 + 3 ^ 40 * 4834547 * 2
def baseEnd_4834547 : Nat := 2482446357752201546328829

theorem tailTrace_4834547 : CollatzResearch.WordTrace tailWord_4834547 prefixEnd_4834547 2482446357752201546328829 := by
  unfold tailWord_4834547
  simp only [CollatzResearch.WordTrace]
  refine ⟨176330415216269368737373895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117553610144179579158249263 176330415216269368737373895)
  ·
    refine ⟨264495622824404053106060843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176330415216269368737373895 264495622824404053106060843)
    ·
      refine ⟨396743434236606079659091265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264495622824404053106060843 396743434236606079659091265)
      ·
        refine ⟨297557575677454559744318449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396743434236606079659091265 297557575677454559744318449)
        ·
          refine ⟨223168181758090919808238837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297557575677454559744318449 223168181758090919808238837)
          ·
            refine ⟨20922017039821023732022391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 223168181758090919808238837 20922017039821023732022391)
            ·
              refine ⟨31383025559731535598033587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20922017039821023732022391 31383025559731535598033587)
              ·
                refine ⟨47074538339597303397050381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31383025559731535598033587 47074538339597303397050381)
                ·
                  refine ⟨17652951877348988773893893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47074538339597303397050381 17652951877348988773893893)
                  ·
                    refine ⟨3309928477002935395105105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17652951877348988773893893 3309928477002935395105105)
                    ·
                      refine ⟨2482446357752201546328829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3309928477002935395105105 2482446357752201546328829)
                      ·
                        rfl

theorem cell23_4834547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 4, 2].length) (baseStart_4834547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834547 prefixEnd_4834547 := by exact prefixLift 4834547
  have htrace : WordTrace (prefixWord ++ tailWord_4834547) baseStart_4834547 baseEnd_4834547 := by
    simpa [prefixWord, tailWord_4834547, baseEnd_4834547] using wordTrace_append hprefix tailTrace_4834547
  have hstable : (prefixWord ++ tailWord_4834547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834547).length < 2 ^ (prefixWord ++ tailWord_4834547).sum := by decide
  have hdescent : baseEnd_4834547 < baseStart_4834547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834560 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 4]
def baseStart_4834560 : Nat := 118140960795 + 4834560 * 2 ^ 59
def prefixEnd_4834560 : Nat := 4983230072969 + 3 ^ 40 * 4834560 * 2
def baseEnd_4834560 : Nat := 2482453033000709995466269

theorem tailTrace_4834560 : CollatzResearch.WordTrace tailWord_4834560 prefixEnd_4834560 2482453033000709995466269 := by
  unfold tailWord_4834560
  simp only [CollatzResearch.WordTrace]
  refine ⟨88165444682611135978798567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117553926243481514638398089 88165444682611135978798567)
  ·
    refine ⟨132248167023916703968197851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88165444682611135978798567 132248167023916703968197851)
    ·
      refine ⟨198372250535875055952296777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132248167023916703968197851 198372250535875055952296777)
      ·
        refine ⟨148779187901906291964222583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198372250535875055952296777 148779187901906291964222583)
        ·
          refine ⟨223168781852859437946333875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148779187901906291964222583 223168781852859437946333875)
          ·
            refine ⟨334753172779289156919500813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223168781852859437946333875 334753172779289156919500813)
            ·
              refine ⟨125532439792233433844812805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334753172779289156919500813 125532439792233433844812805)
              ·
                refine ⟨23537332461043768845902401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125532439792233433844812805 23537332461043768845902401)
                ·
                  refine ⟨17652999345782826634426801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23537332461043768845902401 17652999345782826634426801)
                  ·
                    refine ⟨13239749509337119975820101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17652999345782826634426801 13239749509337119975820101)
                    ·
                      refine ⟨2482453033000709995466269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13239749509337119975820101 2482453033000709995466269)
                      ·
                        rfl

theorem cell23_4834560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_4834560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834560 prefixEnd_4834560 := by exact prefixLift 4834560
  have htrace : WordTrace (prefixWord ++ tailWord_4834560) baseStart_4834560 baseEnd_4834560 := by
    simpa [prefixWord, tailWord_4834560, baseEnd_4834560] using wordTrace_append hprefix tailTrace_4834560
  have hstable : (prefixWord ++ tailWord_4834560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834560).length < 2 ^ (prefixWord ++ tailWord_4834560).sum := by decide
  have hdescent : baseEnd_4834560 < baseStart_4834560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834570 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 7]
def baseStart_4834570 : Nat := 118140960795 + 4834570 * 2 ^ 59
def prefixEnd_4834570 : Nat := 4983230072969 + 3 ^ 40 * 4834570 * 2
def baseEnd_4834570 : Nat := 275828685311917217371247

theorem tailTrace_4834570 : CollatzResearch.WordTrace tailWord_4834570 prefixEnd_4834570 275828685311917217371247 := by
  unfold tailWord_4834570
  simp only [CollatzResearch.WordTrace]
  refine ⟨44082813523796510916365291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117554169396790695776974109 44082813523796510916365291)
  ·
    refine ⟨66124220285694766374547937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44082813523796510916365291 66124220285694766374547937)
    ·
      refine ⟨49593165214271074780910953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66124220285694766374547937 49593165214271074780910953)
      ·
        refine ⟨37194873910703306085683215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49593165214271074780910953 37194873910703306085683215)
        ·
          refine ⟨55792310866054959128524823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37194873910703306085683215 55792310866054959128524823)
          ·
            refine ⟨83688466299082438692787235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55792310866054959128524823 83688466299082438692787235)
            ·
              refine ⟨125532699448623658039180853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83688466299082438692787235 125532699448623658039180853)
              ·
                refine ⟨11768690573308467941173205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125532699448623658039180853 11768690573308467941173205)
                ·
                  refine ⟨275828685311917217371247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11768690573308467941173205 275828685311917217371247)
                  ·
                    rfl

theorem cell23_4834570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_4834570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834570 prefixEnd_4834570 := by exact prefixLift 4834570
  have htrace : WordTrace (prefixWord ++ tailWord_4834570) baseStart_4834570 baseEnd_4834570 := by
    simpa [prefixWord, tailWord_4834570, baseEnd_4834570] using wordTrace_append hprefix tailTrace_4834570
  have hstable : (prefixWord ++ tailWord_4834570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834570).length < 2 ^ (prefixWord ++ tailWord_4834570).sum := by decide
  have hdescent : baseEnd_4834570 < baseStart_4834570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834657 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_4834657 : Nat := 118140960795 + 4834657 * 2 ^ 59
def prefixEnd_4834657 : Nat := 4983230072969 + 3 ^ 40 * 4834657 * 2
def baseEnd_4834657 : Nat := 2482502840624196115953323

theorem tailTrace_4834657 : CollatzResearch.WordTrace tailWord_4834657 prefixEnd_4834657 2482502840624196115953323 := by
  unfold tailWord_4834657
  simp only [CollatzResearch.WordTrace]
  refine ⟨176334427245870857523878225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117556284830580571682585483 176334427245870857523878225)
  ·
    refine ⟨132250820434403143142908669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176334427245870857523878225 132250820434403143142908669)
    ·
      refine ⟨49594057662901178678590751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132250820434403143142908669 49594057662901178678590751)
      ·
        refine ⟨74391086494351768017886127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49594057662901178678590751 74391086494351768017886127)
        ·
          refine ⟨111586629741527652026829191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74391086494351768017886127 111586629741527652026829191)
          ·
            refine ⟨167379944612291478040243787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111586629741527652026829191 167379944612291478040243787)
            ·
              refine ⟨251069916918437217060365681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167379944612291478040243787 251069916918437217060365681)
              ·
                refine ⟨188302437688827912795274261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251069916918437217060365681 188302437688827912795274261)
                ·
                  refine ⟨8826676766663808412278481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 188302437688827912795274261 8826676766663808412278481)
                  ·
                    refine ⟨6620007574997856309208861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8826676766663808412278481 6620007574997856309208861)
                    ·
                      refine ⟨2482502840624196115953323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6620007574997856309208861 2482502840624196115953323)
                      ·
                        rfl

theorem cell23_4834657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_4834657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834657 prefixEnd_4834657 := by exact prefixLift 4834657
  have htrace : WordTrace (prefixWord ++ tailWord_4834657) baseStart_4834657 baseEnd_4834657 := by
    simpa [prefixWord, tailWord_4834657, baseEnd_4834657] using wordTrace_append hprefix tailTrace_4834657
  have hstable : (prefixWord ++ tailWord_4834657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834657).length < 2 ^ (prefixWord ++ tailWord_4834657).sum := by decide
  have hdescent : baseEnd_4834657 < baseStart_4834657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834674 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_4834674 : Nat := 118140960795 + 4834674 * 2 ^ 59
def prefixEnd_4834674 : Nat := 4983230072969 + 3 ^ 40 * 4834674 * 2
def baseEnd_4834674 : Nat := 2482511569795322549440745

theorem tailTrace_4834674 : CollatzResearch.WordTrace tailWord_4834674 prefixEnd_4834674 2482511569795322549440745 := by
  unfold tailWord_4834674
  simp only [CollatzResearch.WordTrace]
  refine ⟨44083761821702317356811769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117556698191206179618164717 44083761821702317356811769)
  ·
    refine ⟨33062821366276738017608827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44083761821702317356811769 33062821366276738017608827)
    ·
      refine ⟨49594232049415107026413241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33062821366276738017608827 49594232049415107026413241)
      ·
        refine ⟨37195674037061330269809931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49594232049415107026413241 37195674037061330269809931)
        ·
          refine ⟨55793511055591995404714897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37195674037061330269809931 55793511055591995404714897)
          ·
            refine ⟨41845133291693996553536173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55793511055591995404714897 41845133291693996553536173)
            ·
              refine ⟨15691924984385248707576065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41845133291693996553536173 15691924984385248707576065)
              ·
                refine ⟨11768943738288936530682049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15691924984385248707576065 11768943738288936530682049)
                ·
                  refine ⟨8826707803716702398011537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11768943738288936530682049 8826707803716702398011537)
                  ·
                    refine ⟨6620030852787526798508653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8826707803716702398011537 6620030852787526798508653)
                    ·
                      refine ⟨2482511569795322549440745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6620030852787526798508653 2482511569795322549440745)
                      ·
                        rfl

theorem cell23_4834674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_4834674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834674 prefixEnd_4834674 := by exact prefixLift 4834674
  have htrace : WordTrace (prefixWord ++ tailWord_4834674) baseStart_4834674 baseEnd_4834674 := by
    simpa [prefixWord, tailWord_4834674, baseEnd_4834674] using wordTrace_append hprefix tailTrace_4834674
  have hstable : (prefixWord ++ tailWord_4834674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834674).length < 2 ^ (prefixWord ++ tailWord_4834674).sum := by decide
  have hdescent : baseEnd_4834674 < baseStart_4834674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834737 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 3, 6]
def baseStart_4834737 : Nat := 118140960795 + 4834737 * 2 ^ 59
def prefixEnd_4834737 : Nat := 4983230072969 + 3 ^ 40 * 4834737 * 2
def baseEnd_4834737 : Nat := 827514639692185267650985

theorem tailTrace_4834737 : CollatzResearch.WordTrace tailWord_4834737 prefixEnd_4834737 827514639692185267650985 := by
  unfold tailWord_4834737
  simp only [CollatzResearch.WordTrace]
  refine ⟨176337345085581031186790465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117558230057054020791193643 176337345085581031186790465)
  ·
    refine ⟨132253008814185773390092849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176337345085581031186790465 132253008814185773390092849)
    ·
      refine ⟨99189756610639330042569637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132253008814185773390092849 99189756610639330042569637)
      ·
        refine ⟨18598079364494874382981807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99189756610639330042569637 18598079364494874382981807)
        ·
          refine ⟨27897119046742311574472711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18598079364494874382981807 27897119046742311574472711)
          ·
            refine ⟨41845678570113467361709067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27897119046742311574472711 41845678570113467361709067)
            ·
              refine ⟨62768517855170201042563601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41845678570113467361709067 62768517855170201042563601)
              ·
                refine ⟨47076388391377650781922701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62768517855170201042563601 47076388391377650781922701)
                ·
                  refine ⟨17653645646766619043221013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47076388391377650781922701 17653645646766619043221013)
                  ·
                    refine ⟨827514639692185267650985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17653645646766619043221013 827514639692185267650985)
                    ·
                      rfl

theorem cell23_4834737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_4834737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834737 prefixEnd_4834737 := by exact prefixLift 4834737
  have htrace : WordTrace (prefixWord ++ tailWord_4834737) baseStart_4834737 baseEnd_4834737 := by
    simpa [prefixWord, tailWord_4834737, baseEnd_4834737] using wordTrace_append hprefix tailTrace_4834737
  have hstable : (prefixWord ++ tailWord_4834737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834737).length < 2 ^ (prefixWord ++ tailWord_4834737).sum := by decide
  have hdescent : baseEnd_4834737 < baseStart_4834737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834778 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4]
def baseStart_4834778 : Nat := 118140960795 + 4834778 * 2 ^ 59
def prefixEnd_4834778 : Nat := 4983230072969 + 3 ^ 40 * 4834778 * 2
def baseEnd_4834778 : Nat := 2482564971783390142540267

theorem tailTrace_4834778 : CollatzResearch.WordTrace tailWord_4834778 prefixEnd_4834778 2482564971783390142540267 := by
  unfold tailWord_4834778
  simp only [CollatzResearch.WordTrace]
  refine ⟨44084710119608123797258247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117559226985621663459355325 44084710119608123797258247)
  ·
    refine ⟨66127065179412185695887371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44084710119608123797258247 66127065179412185695887371)
    ·
      refine ⟨99190597769118278543831057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66127065179412185695887371 99190597769118278543831057)
      ·
        refine ⟨74392948326838708907873293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99190597769118278543831057 74392948326838708907873293)
        ·
          refine ⟨27897355622564515840452485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74392948326838708907873293 27897355622564515840452485)
          ·
            refine ⟨5230754179230846720084841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27897355622564515840452485 5230754179230846720084841)
            ·
              refine ⟨3923065634423135040063631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5230754179230846720084841 3923065634423135040063631)
              ·
                refine ⟨5884598451634702560095447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923065634423135040063631 5884598451634702560095447)
                ·
                  refine ⟨8826897677452053840143171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5884598451634702560095447 8826897677452053840143171)
                  ·
                    refine ⟨13240346516178080760214757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8826897677452053840143171 13240346516178080760214757)
                    ·
                      refine ⟨2482564971783390142540267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13240346516178080760214757 2482564971783390142540267)
                      ·
                        rfl

theorem cell23_4834778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_4834778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834778 prefixEnd_4834778 := by exact prefixLift 4834778
  have htrace : WordTrace (prefixWord ++ tailWord_4834778) baseStart_4834778 baseEnd_4834778 := by
    simpa [prefixWord, tailWord_4834778, baseEnd_4834778] using wordTrace_append hprefix tailTrace_4834778
  have hstable : (prefixWord ++ tailWord_4834778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834778).length < 2 ^ (prefixWord ++ tailWord_4834778).sum := by decide
  have hdescent : baseEnd_4834778 < baseStart_4834778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834805 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 2, 4]
def baseStart_4834805 : Nat := 118140960795 + 4834805 * 2 ^ 59
def prefixEnd_4834805 : Nat := 4983230072969 + 3 ^ 40 * 4834805 * 2
def baseEnd_4834805 : Nat := 827526278587020512300881

theorem tailTrace_4834805 : CollatzResearch.WordTrace tailWord_4834805 prefixEnd_4834805 827526278587020512300881 := by
  unfold tailWord_4834805
  simp only [CollatzResearch.WordTrace]
  refine ⟨176339825249334678800265869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117559883499556452533510579 176339825249334678800265869)
  ·
    refine ⟨66127434468500504550099701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176339825249334678800265869 66127434468500504550099701)
    ·
      refine ⟨6199446981421922301571847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66127434468500504550099701 6199446981421922301571847)
      ·
        refine ⟨9299170472132883452357771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6199446981421922301571847 9299170472132883452357771)
        ·
          refine ⟨13948755708199325178536657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9299170472132883452357771 13948755708199325178536657)
          ·
            refine ⟨10461566781149493883902493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13948755708199325178536657 10461566781149493883902493)
            ·
              refine ⟨3923087542931060206463435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10461566781149493883902493 3923087542931060206463435)
              ·
                refine ⟨5884631314396590309695153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923087542931060206463435 5884631314396590309695153)
                ·
                  refine ⟨4413473485797442732271365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5884631314396590309695153 4413473485797442732271365)
                  ·
                    refine ⟨827526278587020512300881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4413473485797442732271365 827526278587020512300881)
                    ·
                      rfl

theorem cell23_4834805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_4834805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834805 prefixEnd_4834805 := by exact prefixLift 4834805
  have htrace : WordTrace (prefixWord ++ tailWord_4834805) baseStart_4834805 baseEnd_4834805 := by
    simpa [prefixWord, tailWord_4834805, baseEnd_4834805] using wordTrace_append hprefix tailTrace_4834805
  have hstable : (prefixWord ++ tailWord_4834805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834805).length < 2 ^ (prefixWord ++ tailWord_4834805).sum := by decide
  have hdescent : baseEnd_4834805 < baseStart_4834805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834818 : List Nat := [3, 4, 1, 2, 1, 3, 2, 7]
def baseStart_4834818 : Nat := 118140960795 + 4834818 * 2 ^ 59
def prefixEnd_4834818 : Nat := 4983230072969 + 3 ^ 40 * 4834818 * 2
def baseEnd_4834818 : Nat := 91947611518872962445929

theorem tailTrace_4834818 : CollatzResearch.WordTrace tailWord_4834818 prefixEnd_4834818 91947611518872962445929 := by
  unfold tailWord_4834818
  simp only [CollatzResearch.WordTrace]
  refine ⟨44085074849571895505122277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117560199598858388013659405 44085074849571895505122277)
  ·
    refine ⟨8265951534294730407210427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44085074849571895505122277 8265951534294730407210427)
    ·
      refine ⟨12398927301442095610815641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8265951534294730407210427 12398927301442095610815641)
      ·
        refine ⟨9299195476081571708111731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12398927301442095610815641 9299195476081571708111731)
        ·
          refine ⟨13948793214122357562167597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9299195476081571708111731 13948793214122357562167597)
          ·
            refine ⟨5230797455295884085812849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13948793214122357562167597 5230797455295884085812849)
            ·
              refine ⟨3923098091471913064359637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5230797455295884085812849 3923098091471913064359637)
              ·
                refine ⟨91947611518872962445929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3923098091471913064359637 91947611518872962445929)
                ·
                  rfl

theorem cell23_4834818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 7].length) (baseStart_4834818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834818 prefixEnd_4834818 := by exact prefixLift 4834818
  have htrace : WordTrace (prefixWord ++ tailWord_4834818) baseStart_4834818 baseEnd_4834818 := by
    simpa [prefixWord, tailWord_4834818, baseEnd_4834818] using wordTrace_append hprefix tailTrace_4834818
  have hstable : (prefixWord ++ tailWord_4834818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834818).length < 2 ^ (prefixWord ++ tailWord_4834818).sum := by decide
  have hdescent : baseEnd_4834818 < baseStart_4834818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834846 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4834846 : Nat := 118140960795 + 4834846 * 2 ^ 59
def prefixEnd_4834846 : Nat := 4983230072969 + 3 ^ 40 * 4834846 * 2
def baseEnd_4834846 : Nat := 2482599888467895876489955

theorem tailTrace_4834846 : CollatzResearch.WordTrace tailWord_4834846 prefixEnd_4834846 2482599888467895876489955 := by
  unfold tailWord_4834846
  simp only [CollatzResearch.WordTrace]
  refine ⟨22042665080273267850313549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117560880428124095201672261 22042665080273267850313549)
  ·
    refine ⟨8265999405102475443867581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22042665080273267850313549 8265999405102475443867581)
    ·
      refine ⟨3099749776913428291450343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8265999405102475443867581 3099749776913428291450343)
      ·
        refine ⟨4649624665370142437175515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3099749776913428291450343 4649624665370142437175515)
        ·
          refine ⟨6974436998055213655763273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4649624665370142437175515 6974436998055213655763273)
          ·
            refine ⟨5230827748541410241822455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6974436998055213655763273 5230827748541410241822455)
            ·
              refine ⟨7846241622812115362733683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230827748541410241822455 7846241622812115362733683)
              ·
                refine ⟨11769362434218173044100525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7846241622812115362733683 11769362434218173044100525)
                ·
                  refine ⟨4413510912831814891537697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11769362434218173044100525 4413510912831814891537697)
                  ·
                    refine ⟨3310133184623861168653273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4413510912831814891537697 3310133184623861168653273)
                    ·
                      refine ⟨2482599888467895876489955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3310133184623861168653273 2482599888467895876489955)
                      ·
                        rfl

theorem cell23_4834846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4834846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834846 prefixEnd_4834846 := by exact prefixLift 4834846
  have htrace : WordTrace (prefixWord ++ tailWord_4834846) baseStart_4834846 baseEnd_4834846 := by
    simpa [prefixWord, tailWord_4834846, baseEnd_4834846] using wordTrace_append hprefix tailTrace_4834846
  have hstable : (prefixWord ++ tailWord_4834846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834846).length < 2 ^ (prefixWord ++ tailWord_4834846).sum := by decide
  have hdescent : baseEnd_4834846 < baseStart_4834846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834862 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_4834862 : Nat := 118140960795 + 4834862 * 2 ^ 59
def prefixEnd_4834862 : Nat := 4983230072969 + 3 ^ 40 * 4834862 * 2
def baseEnd_4834862 : Nat := 2482608104158367813889881

theorem tailTrace_4834862 : CollatzResearch.WordTrace tailWord_4834862 prefixEnd_4834862 2482608104158367813889881 := by
  unfold tailWord_4834862
  simp only [CollatzResearch.WordTrace]
  refine ⟨22042738026266022191886355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117561269473418785023393893 22042738026266022191886355)
  ·
    refine ⟨33064107039399033287829533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22042738026266022191886355 33064107039399033287829533)
    ·
      refine ⟨12399040139774637482936075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33064107039399033287829533 12399040139774637482936075)
      ·
        refine ⟨18598560209661956224404113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12399040139774637482936075 18598560209661956224404113)
        ·
          refine ⟨13948920157246467168303085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18598560209661956224404113 13948920157246467168303085)
          ·
            refine ⟨5230845058967425188113657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13948920157246467168303085 5230845058967425188113657)
            ·
              refine ⟨3923133794225568891085243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5230845058967425188113657 3923133794225568891085243)
              ·
                refine ⟨5884700691338353336627865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923133794225568891085243 5884700691338353336627865)
                ·
                  refine ⟨4413525518503765002470899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5884700691338353336627865 4413525518503765002470899)
                  ·
                    refine ⟨6620288277755647503706349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4413525518503765002470899 6620288277755647503706349)
                    ·
                      refine ⟨2482608104158367813889881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6620288277755647503706349 2482608104158367813889881)
                      ·
                        rfl

theorem cell23_4834862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_4834862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834862 prefixEnd_4834862 := by exact prefixLift 4834862
  have htrace : WordTrace (prefixWord ++ tailWord_4834862) baseStart_4834862 baseEnd_4834862 := by
    simpa [prefixWord, tailWord_4834862, baseEnd_4834862] using wordTrace_append hprefix tailTrace_4834862
  have hstable : (prefixWord ++ tailWord_4834862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834862).length < 2 ^ (prefixWord ++ tailWord_4834862).sum := by decide
  have hdescent : baseEnd_4834862 < baseStart_4834862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834908 : List Nat := [2, 2, 4, 1, 2, 2, 1, 4, 5]
def baseStart_4834908 : Nat := 118140960795 + 4834908 * 2 ^ 59
def prefixEnd_4834908 : Nat := 4983230072969 + 3 ^ 40 * 4834908 * 2
def baseEnd_4834908 : Nat := 275847969363163848212741

theorem tailTrace_4834908 : CollatzResearch.WordTrace tailWord_4834908 prefixEnd_4834908 275847969363163848212741 := by
  unfold tailWord_4834908
  simp only [CollatzResearch.WordTrace]
  refine ⟨88171790983980763695632689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117562387978641018260843585 88171790983980763695632689)
  ·
    refine ⟨66128843237985572771724517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88171790983980763695632689 66128843237985572771724517)
    ·
      refine ⟨12399158107122294894698347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66128843237985572771724517 12399158107122294894698347)
      ·
        refine ⟨18598737160683442342047521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12399158107122294894698347 18598737160683442342047521)
        ·
          refine ⟨13949052870512581756535641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18598737160683442342047521 13949052870512581756535641)
          ·
            refine ⟨10461789652884436317401731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13949052870512581756535641 10461789652884436317401731)
            ·
              refine ⟨15692684479326654476102597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10461789652884436317401731 15692684479326654476102597)
              ·
                refine ⟨2942378339873747714269237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15692684479326654476102597 2942378339873747714269237)
                ·
                  refine ⟨275847969363163848212741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2942378339873747714269237 275847969363163848212741)
                  ·
                    rfl

theorem cell23_4834908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_4834908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834908 prefixEnd_4834908 := by exact prefixLift 4834908
  have htrace : WordTrace (prefixWord ++ tailWord_4834908) baseStart_4834908 baseEnd_4834908 := by
    simpa [prefixWord, tailWord_4834908, baseEnd_4834908] using wordTrace_append hprefix tailTrace_4834908
  have hstable : (prefixWord ++ tailWord_4834908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834908).length < 2 ^ (prefixWord ++ tailWord_4834908).sum := by decide
  have hdescent : baseEnd_4834908 < baseStart_4834908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834924 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_4834924 : Nat := 118140960795 + 4834924 * 2 ^ 59
def prefixEnd_4834924 : Nat := 4983230072969 + 3 ^ 40 * 4834924 * 2
def baseEnd_4834924 : Nat := 2482639939958946571314595

theorem tailTrace_4834924 : CollatzResearch.WordTrace tailWord_4834924 prefixEnd_4834924 2482639939958946571314595 := by
  unfold tailWord_4834924
  simp only [CollatzResearch.WordTrace]
  refine ⟨88172082767951781061923913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117562777023935708082565217 88172082767951781061923913)
  ·
    refine ⟨66129062075963835796442935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88172082767951781061923913 66129062075963835796442935)
    ·
      refine ⟨99193593113945753694664403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66129062075963835796442935 99193593113945753694664403)
      ·
        refine ⟨148790389670918630541996605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99193593113945753694664403 148790389670918630541996605)
        ·
          refine ⟨55796396126594486453248727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148790389670918630541996605 55796396126594486453248727)
          ·
            refine ⟨83694594189891729679873091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55796396126594486453248727 83694594189891729679873091)
            ·
              refine ⟨125541891284837594519809637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83694594189891729679873091 125541891284837594519809637)
              ·
                refine ⟨23539104615907048972464307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125541891284837594519809637 23539104615907048972464307)
                ·
                  refine ⟨35308656923860573458696461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23539104615907048972464307 35308656923860573458696461)
                  ·
                    refine ⟨13240746346447715047011173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35308656923860573458696461 13240746346447715047011173)
                    ·
                      refine ⟨2482639939958946571314595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13240746346447715047011173 2482639939958946571314595)
                      ·
                        rfl

theorem cell23_4834924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_4834924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834924 prefixEnd_4834924 := by exact prefixLift 4834924
  have htrace : WordTrace (prefixWord ++ tailWord_4834924) baseStart_4834924 baseEnd_4834924 := by
    simpa [prefixWord, tailWord_4834924, baseEnd_4834924] using wordTrace_append hprefix tailTrace_4834924
  have hstable : (prefixWord ++ tailWord_4834924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834924).length < 2 ^ (prefixWord ++ tailWord_4834924).sum := by decide
  have hdescent : baseEnd_4834924 < baseStart_4834924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834941 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_4834941 : Nat := 118140960795 + 4834941 * 2 ^ 59
def prefixEnd_4834941 : Nat := 4983230072969 + 3 ^ 40 * 4834941 * 2
def baseEnd_4834941 : Nat := 2482648669130073004802017

theorem tailTrace_4834941 : CollatzResearch.WordTrace tailWord_4834941 prefixEnd_4834941 2482648669130073004802017 := by
  unfold tailWord_4834941
  simp only [CollatzResearch.WordTrace]
  refine ⟨176344785576841974027216677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117563190384561316018144451 176344785576841974027216677)
  ·
    refine ⟨33064647295657870130103127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176344785576841974027216677 33064647295657870130103127)
    ·
      refine ⟨49596970943486805195154691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33064647295657870130103127 49596970943486805195154691)
      ·
        refine ⟨74395456415230207792732037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49596970943486805195154691 74395456415230207792732037)
        ·
          refine ⟨13949148077855663961137257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74395456415230207792732037 13949148077855663961137257)
          ·
            refine ⟨10461861058391747970852943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13949148077855663961137257 10461861058391747970852943)
            ·
              refine ⟨15692791587587621956279415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10461861058391747970852943 15692791587587621956279415)
              ·
                refine ⟨23539187381381432934419123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15692791587587621956279415 23539187381381432934419123)
                ·
                  refine ⟨35308781072072149401628685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23539187381381432934419123 35308781072072149401628685)
                  ·
                    refine ⟨13240792902027056025610757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35308781072072149401628685 13240792902027056025610757)
                    ·
                      refine ⟨2482648669130073004802017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13240792902027056025610757 2482648669130073004802017)
                      ·
                        rfl

theorem cell23_4834941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_4834941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834941 prefixEnd_4834941 := by exact prefixLift 4834941
  have htrace : WordTrace (prefixWord ++ tailWord_4834941) baseStart_4834941 baseEnd_4834941 := by
    simpa [prefixWord, tailWord_4834941, baseEnd_4834941] using wordTrace_append hprefix tailTrace_4834941
  have hstable : (prefixWord ++ tailWord_4834941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834941).length < 2 ^ (prefixWord ++ tailWord_4834941).sum := by decide
  have hdescent : baseEnd_4834941 < baseStart_4834941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834958 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2]
def baseStart_4834958 : Nat := 118140960795 + 4834958 * 2 ^ 59
def prefixEnd_4834958 : Nat := 4983230072969 + 3 ^ 40 * 4834958 * 2
def baseEnd_4834958 : Nat := 2482657398301199438289439

theorem tailTrace_4834958 : CollatzResearch.WordTrace tailWord_4834958 prefixEnd_4834958 2482657398301199438289439 := by
  unfold tailWord_4834958
  simp only [CollatzResearch.WordTrace]
  refine ⟨22043175702222548241323191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117563603745186923953723685 22043175702222548241323191)
  ·
    refine ⟨33064763553333822361984787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22043175702222548241323191 33064763553333822361984787)
    ·
      refine ⟨49597145330000733542977181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33064763553333822361984787 49597145330000733542977181)
      ·
        refine ⟨18598929498750275078616443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49597145330000733542977181 18598929498750275078616443)
        ·
          refine ⟨27898394248125412617924665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18598929498750275078616443 27898394248125412617924665)
          ·
            refine ⟨20923795686094059463443499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27898394248125412617924665 20923795686094059463443499)
            ·
              refine ⟨31385693529141089195165249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20923795686094059463443499 31385693529141089195165249)
              ·
                refine ⟨23539270146855816896373937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31385693529141089195165249 23539270146855816896373937)
                ·
                  refine ⟨17654452610141862672280453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23539270146855816896373937 17654452610141862672280453)
                  ·
                    refine ⟨3310209864401599251052585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17654452610141862672280453 3310209864401599251052585)
                    ·
                      refine ⟨2482657398301199438289439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3310209864401599251052585 2482657398301199438289439)
                      ·
                        rfl

theorem cell23_4834958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_4834958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834958 prefixEnd_4834958 := by exact prefixLift 4834958
  have htrace : WordTrace (prefixWord ++ tailWord_4834958) baseStart_4834958 baseEnd_4834958 := by
    simpa [prefixWord, tailWord_4834958, baseEnd_4834958] using wordTrace_append hprefix tailTrace_4834958
  have hstable : (prefixWord ++ tailWord_4834958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834958).length < 2 ^ (prefixWord ++ tailWord_4834958).sum := by decide
  have hdescent : baseEnd_4834958 < baseStart_4834958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834968 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 3, 4]
def baseStart_4834968 : Nat := 118140960795 + 4834968 * 2 ^ 59
def prefixEnd_4834968 : Nat := 4983230072969 + 3 ^ 40 * 4834968 * 2
def baseEnd_4834968 : Nat := 827554177702581466388131

theorem tailTrace_4834968 : CollatzResearch.WordTrace tailWord_4834968 prefixEnd_4834968 827554177702581466388131 := by
  unfold tailWord_4834968
  simp only [CollatzResearch.WordTrace]
  refine ⟨88172885173872078819224779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117563846898496105092299705 88172885173872078819224779)
  ·
    refine ⟨132259327760808118228837169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88172885173872078819224779 132259327760808118228837169)
    ·
      refine ⟨99194495820606088671627877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132259327760808118228837169 99194495820606088671627877)
      ·
        refine ⟨18598967966363641625930227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99194495820606088671627877 18598967966363641625930227)
        ·
          refine ⟨27898451949545462438895341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18598967966363641625930227 27898451949545462438895341)
          ·
            refine ⟨10461919481079548414585753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27898451949545462438895341 10461919481079548414585753)
            ·
              refine ⟨7846439610809661310939315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10461919481079548414585753 7846439610809661310939315)
              ·
                refine ⟨11769659416214491966408973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7846439610809661310939315 11769659416214491966408973)
                ·
                  refine ⟨4413622281080434487403365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11769659416214491966408973 4413622281080434487403365)
                  ·
                    refine ⟨827554177702581466388131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4413622281080434487403365 827554177702581466388131)
                    ·
                      rfl

theorem cell23_4834968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_4834968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834968 prefixEnd_4834968 := by exact prefixLift 4834968
  have htrace : WordTrace (prefixWord ++ tailWord_4834968) baseStart_4834968 baseEnd_4834968 := by
    simpa [prefixWord, tailWord_4834968, baseEnd_4834968] using wordTrace_append hprefix tailTrace_4834968
  have hstable : (prefixWord ++ tailWord_4834968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834968).length < 2 ^ (prefixWord ++ tailWord_4834968).sum := by decide
  have hdescent : baseEnd_4834968 < baseStart_4834968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4834998 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_4834998 : Nat := 118140960795 + 4834998 * 2 ^ 59
def prefixEnd_4834998 : Nat := 4983230072969 + 3 ^ 40 * 4834998 * 2
def baseEnd_4834998 : Nat := 275853104169708809087695

theorem tailTrace_4834998 : CollatzResearch.WordTrace tailWord_4834998 prefixEnd_4834998 275853104169708809087695 := by
  unfold tailWord_4834998
  simp only [CollatzResearch.WordTrace]
  refine ⟨11021679033602217047627603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117564576358423648508027765 11021679033602217047627603)
  ·
    refine ⟨16532518550403325571441405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11021679033602217047627603 16532518550403325571441405)
    ·
      refine ⟨6199694456401247089290527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16532518550403325571441405 6199694456401247089290527)
      ·
        refine ⟨9299541684601870633935791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6199694456401247089290527 9299541684601870633935791)
        ·
          refine ⟨13949312526902805950903687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9299541684601870633935791 13949312526902805950903687)
          ·
            refine ⟨20923968790354208926355531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13949312526902805950903687 20923968790354208926355531)
            ·
              refine ⟨31385953185531313389533297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20923968790354208926355531 31385953185531313389533297)
              ·
                refine ⟨23539464889148485042149973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31385953185531313389533297 23539464889148485042149973)
                ·
                  refine ⟨275853104169708809087695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23539464889148485042149973 275853104169708809087695)
                  ·
                    rfl

theorem cell23_4834998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_4834998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4834998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4834998 prefixEnd_4834998 := by exact prefixLift 4834998
  have htrace : WordTrace (prefixWord ++ tailWord_4834998) baseStart_4834998 baseEnd_4834998 := by
    simpa [prefixWord, tailWord_4834998, baseEnd_4834998] using wordTrace_append hprefix tailTrace_4834998
  have hstable : (prefixWord ++ tailWord_4834998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4834998).length < 2 ^ (prefixWord ++ tailWord_4834998).sum := by decide
  have hdescent : baseEnd_4834998 < baseStart_4834998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4834998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835024 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 5, 6]
def baseStart_4835024 : Nat := 118140960795 + 4835024 * 2 ^ 59
def prefixEnd_4835024 : Nat := 4983230072969 + 3 ^ 40 * 4835024 * 2
def baseEnd_4835024 : Nat := 827563762674798726688045

theorem tailTrace_4835024 : CollatzResearch.WordTrace tailWord_4835024 prefixEnd_4835024 827563762674798726688045 := by
  unfold tailWord_4835024
  simp only [CollatzResearch.WordTrace]
  refine ⟨88173906417770639601244063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117565208557027519468325417 88173906417770639601244063)
  ·
    refine ⟨132260859626655959401866095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88173906417770639601244063 132260859626655959401866095)
    ·
      refine ⟨198391289439983939102799143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132260859626655959401866095 198391289439983939102799143)
      ·
        refine ⟨297586934159975908654198715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198391289439983939102799143 297586934159975908654198715)
        ·
          refine ⟨446380401239963862981298073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297586934159975908654198715 446380401239963862981298073)
          ·
            refine ⟨334785300929972897235973555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446380401239963862981298073 334785300929972897235973555)
            ·
              refine ⟨502177951394959345853960333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334785300929972897235973555 502177951394959345853960333)
              ·
                refine ⟨188316731773109754695235125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 502177951394959345853960333 188316731773109754695235125)
                ·
                  refine ⟨17654693603729039502678293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188316731773109754695235125 17654693603729039502678293)
                  ·
                    refine ⟨827563762674798726688045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17654693603729039502678293 827563762674798726688045)
                    ·
                      rfl

theorem cell23_4835024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_4835024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835024 prefixEnd_4835024 := by exact prefixLift 4835024
  have htrace : WordTrace (prefixWord ++ tailWord_4835024) baseStart_4835024 baseEnd_4835024 := by
    simpa [prefixWord, tailWord_4835024, baseEnd_4835024] using wordTrace_append hprefix tailTrace_4835024
  have hstable : (prefixWord ++ tailWord_4835024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835024).length < 2 ^ (prefixWord ++ tailWord_4835024).sum := by decide
  have hdescent : baseEnd_4835024 < baseStart_4835024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835025 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 3, 1, 3]
def baseStart_4835025 : Nat := 118140960795 + 4835025 * 2 ^ 59
def prefixEnd_4835025 : Nat := 4983230072969 + 3 ^ 40 * 4835025 * 2
def baseEnd_4835025 : Nat := 2482691801505050676151631

theorem tailTrace_4835025 : CollatzResearch.WordTrace tailWord_4835025 prefixEnd_4835025 2482691801505050676151631 := by
  unfold tailWord_4835025
  simp only [CollatzResearch.WordTrace]
  refine ⟨176347849308537656373274529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117565232872358437582183019 176347849308537656373274529)
  ·
    refine ⟨132260886981403242279955897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176347849308537656373274529 132260886981403242279955897)
    ·
      refine ⟨99195665236052431709966923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132260886981403242279955897 99195665236052431709966923)
      ·
        refine ⟨148793497854078647564950385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99195665236052431709966923 148793497854078647564950385)
        ·
          refine ⟨111595123390558985673712789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148793497854078647564950385 111595123390558985673712789)
          ·
            refine ⟨5231021408932452453455287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111595123390558985673712789 5231021408932452453455287)
            ·
              refine ⟨7846532113398678680182931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5231021408932452453455287 7846532113398678680182931)
              ·
                refine ⟨11769798170098018020274397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7846532113398678680182931 11769798170098018020274397)
                ·
                  refine ⟨4413674313786756757602899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11769798170098018020274397 4413674313786756757602899)
                  ·
                    refine ⟨6620511470680135136404349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4413674313786756757602899 6620511470680135136404349)
                    ·
                      refine ⟨2482691801505050676151631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6620511470680135136404349 2482691801505050676151631)
                      ·
                        rfl

theorem cell23_4835025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_4835025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835025 prefixEnd_4835025 := by exact prefixLift 4835025
  have htrace : WordTrace (prefixWord ++ tailWord_4835025) baseStart_4835025 baseEnd_4835025 := by
    simpa [prefixWord, tailWord_4835025, baseEnd_4835025] using wordTrace_append hprefix tailTrace_4835025
  have hstable : (prefixWord ++ tailWord_4835025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835025).length < 2 ^ (prefixWord ++ tailWord_4835025).sum := by decide
  have hdescent : baseEnd_4835025 < baseStart_4835025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835031 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_4835031 : Nat := 118140960795 + 4835031 * 2 ^ 59
def prefixEnd_4835031 : Nat := 4983230072969 + 3 ^ 40 * 4835031 * 2
def baseEnd_4835031 : Nat := 2482694882388977652676603

theorem tailTrace_4835031 : CollatzResearch.WordTrace tailWord_4835031 prefixEnd_4835031 2482694882388977652676603 := by
  unfold tailWord_4835031
  simp only [CollatzResearch.WordTrace]
  refine ⟨176348068146515919397992947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117565378764343946265328631 176348068146515919397992947)
  ·
    refine ⟨264522102219773879096989421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176348068146515919397992947 264522102219773879096989421)
    ·
      refine ⟨99195788332415204661371033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264522102219773879096989421 99195788332415204661371033)
      ·
        refine ⟨74396841249311403496028275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99195788332415204661371033 74396841249311403496028275)
        ·
          refine ⟨111595261873967105244042413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74396841249311403496028275 111595261873967105244042413)
          ·
            refine ⟨41848223202737664466515905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111595261873967105244042413 41848223202737664466515905)
            ·
              refine ⟨31386167402053248349886929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41848223202737664466515905 31386167402053248349886929)
              ·
                refine ⟨23539625551539936262415197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31386167402053248349886929 23539625551539936262415197)
                ·
                  refine ⟨8827359581827476098405699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23539625551539936262415197 8827359581827476098405699)
                  ·
                    refine ⟨13241039372741214147608549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8827359581827476098405699 13241039372741214147608549)
                    ·
                      refine ⟨2482694882388977652676603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13241039372741214147608549 2482694882388977652676603)
                      ·
                        rfl

theorem cell23_4835031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_4835031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835031 prefixEnd_4835031 := by exact prefixLift 4835031
  have htrace : WordTrace (prefixWord ++ tailWord_4835031) baseStart_4835031 baseEnd_4835031 := by
    simpa [prefixWord, tailWord_4835031, baseEnd_4835031] using wordTrace_append hprefix tailTrace_4835031
  have hstable : (prefixWord ++ tailWord_4835031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835031).length < 2 ^ (prefixWord ++ tailWord_4835031).sum := by decide
  have hdescent : baseEnd_4835031 < baseStart_4835031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835048 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_4835048 : Nat := 118140960795 + 4835048 * 2 ^ 59
def prefixEnd_4835048 : Nat := 4983230072969 + 3 ^ 40 * 4835048 * 2
def baseEnd_4835048 : Nat := 2482703611560104086164025

theorem tailTrace_4835048 : CollatzResearch.WordTrace tailWord_4835048 prefixEnd_4835048 2482703611560104086164025 := by
  unfold tailWord_4835048
  simp only [CollatzResearch.WordTrace]
  refine ⟨88174344093727165650680899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117565792124969554200907865 88174344093727165650680899)
  ·
    refine ⟨132261516140590748476021349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88174344093727165650680899 132261516140590748476021349)
    ·
      refine ⟨24799034276360765339254003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132261516140590748476021349 24799034276360765339254003)
      ·
        refine ⟨37198551414541148008881005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24799034276360765339254003 37198551414541148008881005)
        ·
          refine ⟨13949456780452930503330377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37198551414541148008881005 13949456780452930503330377)
          ·
            refine ⟨10462092585339697877497783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13949456780452930503330377 10462092585339697877497783)
            ·
              refine ⟨15693138878009546816246675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10462092585339697877497783 15693138878009546816246675)
              ·
                refine ⟨23539708317014320224370013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15693138878009546816246675 23539708317014320224370013)
                ·
                  refine ⟨8827390618880370084138755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23539708317014320224370013 8827390618880370084138755)
                  ·
                    refine ⟨13241085928320555126208133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8827390618880370084138755 13241085928320555126208133)
                    ·
                      refine ⟨2482703611560104086164025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13241085928320555126208133 2482703611560104086164025)
                      ·
                        rfl

theorem cell23_4835048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_4835048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835048 prefixEnd_4835048 := by exact prefixLift 4835048
  have htrace : WordTrace (prefixWord ++ tailWord_4835048) baseStart_4835048 baseEnd_4835048 := by
    simpa [prefixWord, tailWord_4835048, baseEnd_4835048] using wordTrace_append hprefix tailTrace_4835048
  have hstable : (prefixWord ++ tailWord_4835048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835048).length < 2 ^ (prefixWord ++ tailWord_4835048).sum := by decide
  have hdescent : baseEnd_4835048 < baseStart_4835048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835081 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 5, 3, 3]
def baseStart_4835081 : Nat := 118140960795 + 4835081 * 2 ^ 59
def prefixEnd_4835081 : Nat := 4983230072969 + 3 ^ 40 * 4835081 * 2
def baseEnd_4835081 : Nat := 2482720556421702457051373

theorem tailTrace_4835081 : CollatzResearch.WordTrace tailWord_4835081 prefixEnd_4835081 2482720556421702457051373 := by
  unfold tailWord_4835081
  simp only [CollatzResearch.WordTrace]
  refine ⟨176349891796334777937313097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117566594530889851958208731 176349891796334777937313097)
  ·
    refine ⟨132262418847251083452984823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176349891796334777937313097 132262418847251083452984823)
    ·
      refine ⟨198393628270876625179477235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132262418847251083452984823 198393628270876625179477235)
      ·
        refine ⟨297590442406314937769215853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198393628270876625179477235 297590442406314937769215853)
        ·
          refine ⟨111596415902368101663455945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297590442406314937769215853 111596415902368101663455945)
          ·
            refine ⟨83697311926776076247591959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111596415902368101663455945 83697311926776076247591959)
            ·
              refine ⟨125545967890164114371387939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83697311926776076247591959 125545967890164114371387939)
              ·
                refine ⟨188318951835246171557081909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125545967890164114371387939 188318951835246171557081909)
                ·
                  refine ⟨17654901734554328583476429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188318951835246171557081909 17654901734554328583476429)
                  ·
                    refine ⟨6620588150457873218803661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17654901734554328583476429 6620588150457873218803661)
                    ·
                      refine ⟨2482720556421702457051373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6620588150457873218803661 2482720556421702457051373)
                      ·
                        rfl

theorem cell23_4835081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 3, 3].length) (baseStart_4835081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835081 prefixEnd_4835081 := by exact prefixLift 4835081
  have htrace : WordTrace (prefixWord ++ tailWord_4835081) baseStart_4835081 baseEnd_4835081 := by
    simpa [prefixWord, tailWord_4835081, baseEnd_4835081] using wordTrace_append hprefix tailTrace_4835081
  have hstable : (prefixWord ++ tailWord_4835081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835081).length < 2 ^ (prefixWord ++ tailWord_4835081).sum := by decide
  have hdescent : baseEnd_4835081 < baseStart_4835081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835098 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3]
def baseStart_4835098 : Nat := 118140960795 + 4835098 * 2 ^ 59
def prefixEnd_4835098 : Nat := 4983230072969 + 3 ^ 40 * 4835098 * 2
def baseEnd_4835098 : Nat := 2482729285592828890538795

theorem tailTrace_4835098 : CollatzResearch.WordTrace tailWord_4835098 prefixEnd_4835098 2482729285592828890538795 := by
  unfold tailWord_4835098
  simp only [CollatzResearch.WordTrace]
  refine ⟨44087627959318297460170487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117567007891515459893787965 44087627959318297460170487)
  ·
    refine ⟨66131441938977446190255731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44087627959318297460170487 66131441938977446190255731)
    ·
      refine ⟨99197162908466169285383597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66131441938977446190255731 99197162908466169285383597)
      ·
        refine ⟨37198936090674813482018849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99197162908466169285383597 37198936090674813482018849)
        ·
          refine ⟨27899202068006110111514137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37198936090674813482018849 27899202068006110111514137)
          ·
            refine ⟨20924401551004582583635603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27899202068006110111514137 20924401551004582583635603)
            ·
              refine ⟨31386602326506873875453405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20924401551004582583635603 31386602326506873875453405)
              ·
                refine ⟨11769975872440077703295027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31386602326506873875453405 11769975872440077703295027)
                ·
                  refine ⟨17654963808660116554942541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11769975872440077703295027 17654963808660116554942541)
                  ·
                    refine ⟨6620611428247543708103453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17654963808660116554942541 6620611428247543708103453)
                    ·
                      refine ⟨2482729285592828890538795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6620611428247543708103453 2482729285592828890538795)
                      ·
                        rfl

theorem cell23_4835098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_4835098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835098 prefixEnd_4835098 := by exact prefixLift 4835098
  have htrace : WordTrace (prefixWord ++ tailWord_4835098) baseStart_4835098 baseEnd_4835098 := by
    simpa [prefixWord, tailWord_4835098, baseEnd_4835098] using wordTrace_append hprefix tailTrace_4835098
  have hstable : (prefixWord ++ tailWord_4835098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835098).length < 2 ^ (prefixWord ++ tailWord_4835098).sum := by decide
  have hdescent : baseEnd_4835098 < baseStart_4835098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835161 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 7]
def baseStart_4835161 : Nat := 118140960795 + 4835161 * 2 ^ 59
def prefixEnd_4835161 : Nat := 4983230072969 + 3 ^ 40 * 4835161 * 2
def baseEnd_4835161 : Nat := 275862403874895793783445

theorem tailTrace_4835161 : CollatzResearch.WordTrace tailWord_4835161 prefixEnd_4835161 275862403874895793783445 := by
  unfold tailWord_4835161
  simp only [CollatzResearch.WordTrace]
  refine ⟨176352809636044951600225337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117568539757363301066816891 176352809636044951600225337)
  ·
    refine ⟨132264607227033713700169003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176352809636044951600225337 132264607227033713700169003)
    ·
      refine ⟨198396910840550570550253505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132264607227033713700169003 198396910840550570550253505)
      ·
        refine ⟨148797683130412927912690129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198396910840550570550253505 148797683130412927912690129)
        ·
          refine ⟨111598262347809695934517597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148797683130412927912690129 111598262347809695934517597)
          ·
            refine ⟨41849348380428635975444099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111598262347809695934517597 41849348380428635975444099)
            ·
              refine ⟨62774022570642953963166149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41849348380428635975444099 62774022570642953963166149)
              ·
                refine ⟨11770129231995553868093653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62774022570642953963166149 11770129231995553868093653)
                ·
                  refine ⟨275862403874895793783445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11770129231995553868093653 275862403874895793783445)
                  ·
                    rfl

theorem cell23_4835161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 7].length) (baseStart_4835161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835161 prefixEnd_4835161 := by exact prefixLift 4835161
  have htrace : WordTrace (prefixWord ++ tailWord_4835161) baseStart_4835161 baseEnd_4835161 := by
    simpa [prefixWord, tailWord_4835161, baseEnd_4835161] using wordTrace_append hprefix tailTrace_4835161
  have hstable : (prefixWord ++ tailWord_4835161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835161).length < 2 ^ (prefixWord ++ tailWord_4835161).sum := by decide
  have hdescent : baseEnd_4835161 < baseStart_4835161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835246 : List Nat := [4, 1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_4835246 : Nat := 118140960795 + 4835246 * 2 ^ 59
def prefixEnd_4835246 : Nat := 4983230072969 + 3 ^ 40 * 4835246 * 2
def baseEnd_4835246 : Nat := 275867253414410479054235

theorem tailTrace_4835246 : CollatzResearch.WordTrace tailWord_4835246 prefixEnd_4835246 275867253414410479054235 := by
  unfold tailWord_4835246
  simp only [CollatzResearch.WordTrace]
  refine ⟨22044488730092126389633699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117570606560491340744713061 22044488730092126389633699)
  ·
    refine ⟨33066733095138189584450549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22044488730092126389633699 33066733095138189584450549)
    ·
      refine ⟨3100006227669205273542239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33066733095138189584450549 3100006227669205273542239)
      ·
        refine ⟨4650009341503807910313359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3100006227669205273542239 4650009341503807910313359)
        ·
          refine ⟨6975014012255711865470039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4650009341503807910313359 6975014012255711865470039)
          ·
            refine ⟨10462521018383567798205059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6975014012255711865470039 10462521018383567798205059)
            ·
              refine ⟨15693781527575351697307589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10462521018383567798205059 15693781527575351697307589)
              ·
                refine ⟨2942584036420378443245173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15693781527575351697307589 2942584036420378443245173)
                ·
                  refine ⟨275867253414410479054235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2942584036420378443245173 275867253414410479054235)
                  ·
                    rfl

theorem cell23_4835246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_4835246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835246 prefixEnd_4835246 := by exact prefixLift 4835246
  have htrace : WordTrace (prefixWord ++ tailWord_4835246) baseStart_4835246 baseEnd_4835246 := by
    simpa [prefixWord, tailWord_4835246, baseEnd_4835246] using wordTrace_append hprefix tailTrace_4835246
  have hstable : (prefixWord ++ tailWord_4835246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835246).length < 2 ^ (prefixWord ++ tailWord_4835246).sum := by decide
  have hdescent : baseEnd_4835246 < baseStart_4835246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835262 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_4835262 : Nat := 118140960795 + 4835262 * 2 ^ 59
def prefixEnd_4835262 : Nat := 4983230072969 + 3 ^ 40 * 4835262 * 2
def baseEnd_4835262 : Nat := 2482813496420166248888041

theorem tailTrace_4835262 : CollatzResearch.WordTrace tailWord_4835262 prefixEnd_4835262 2482813496420166248888041 := by
  unfold tailWord_4835262
  simp only [CollatzResearch.WordTrace]
  refine ⟨22044561676084880731206505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117570995605786030566434693 22044561676084880731206505)
  ·
    refine ⟨16533421257063660548404879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22044561676084880731206505 16533421257063660548404879)
    ·
      refine ⟨24800131885595490822607319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16533421257063660548404879 24800131885595490822607319)
      ·
        refine ⟨37200197828393236233910979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24800131885595490822607319 37200197828393236233910979)
        ·
          refine ⟨55800296742589854350866469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37200197828393236233910979 55800296742589854350866469)
          ·
            refine ⟨10462555639235597690787463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55800296742589854350866469 10462555639235597690787463)
            ·
              refine ⟨15693833458853396536181195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10462555639235597690787463 15693833458853396536181195)
              ·
                refine ⟨23540750188280094804271793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15693833458853396536181195 23540750188280094804271793)
                ·
                  refine ⟨17655562641210071103203845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23540750188280094804271793 17655562641210071103203845)
                  ·
                    refine ⟨3310417995226888331850721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17655562641210071103203845 3310417995226888331850721)
                    ·
                      refine ⟨2482813496420166248888041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3310417995226888331850721 2482813496420166248888041)
                      ·
                        rfl

theorem cell23_4835262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_4835262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835262 prefixEnd_4835262 := by exact prefixLift 4835262
  have htrace : WordTrace (prefixWord ++ tailWord_4835262) baseStart_4835262 baseEnd_4835262 := by
    simpa [prefixWord, tailWord_4835262, baseEnd_4835262] using wordTrace_append hprefix tailTrace_4835262
  have hstable : (prefixWord ++ tailWord_4835262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835262).length < 2 ^ (prefixWord ++ tailWord_4835262).sum := by decide
  have hdescent : baseEnd_4835262 < baseStart_4835262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835282 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_4835282 : Nat := 118140960795 + 4835282 * 2 ^ 59
def prefixEnd_4835282 : Nat := 4983230072969 + 3 ^ 40 * 4835282 * 2
def baseEnd_4835282 : Nat := 2482823766033256170637949

theorem tailTrace_4835282 : CollatzResearch.WordTrace tailWord_4835282 prefixEnd_4835282 2482823766033256170637949 := by
  unfold tailWord_4835282
  simp only [CollatzResearch.WordTrace]
  refine ⟨44089305717151647316345025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117571481912404392843586733 44089305717151647316345025)
  ·
    refine ⟨33066979287863735487258769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44089305717151647316345025 33066979287863735487258769)
    ·
      refine ⟨24800234465897801615444077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33066979287863735487258769 24800234465897801615444077)
      ·
        refine ⟨9300087924711675605791529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24800234465897801615444077 9300087924711675605791529)
        ·
          refine ⟨6975065943533756704343647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9300087924711675605791529 6975065943533756704343647)
          ·
            refine ⟨10462598915300635056515471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6975065943533756704343647 10462598915300635056515471)
            ·
              refine ⟨15693898372950952584773207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10462598915300635056515471 15693898372950952584773207)
              ·
                refine ⟨23540847559426428877159811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15693898372950952584773207 23540847559426428877159811)
                ·
                  refine ⟨35311271339139643315739717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23540847559426428877159811 35311271339139643315739717)
                  ·
                    refine ⟨6620863376088683121701197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35311271339139643315739717 6620863376088683121701197)
                    ·
                      refine ⟨2482823766033256170637949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6620863376088683121701197 2482823766033256170637949)
                      ·
                        rfl

theorem cell23_4835282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_4835282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835282 prefixEnd_4835282 := by exact prefixLift 4835282
  have htrace : WordTrace (prefixWord ++ tailWord_4835282) baseStart_4835282 baseEnd_4835282 := by
    simpa [prefixWord, tailWord_4835282, baseEnd_4835282] using wordTrace_append hprefix tailTrace_4835282
  have hstable : (prefixWord ++ tailWord_4835282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835282).length < 2 ^ (prefixWord ++ tailWord_4835282).sum := by decide
  have hdescent : baseEnd_4835282 < baseStart_4835282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835289 : List Nat := [1, 2, 1, 2, 6, 1, 2, 3, 1, 4]
def baseStart_4835289 : Nat := 118140960795 + 4835289 * 2 ^ 59
def prefixEnd_4835289 : Nat := 4983230072969 + 3 ^ 40 * 4835289 * 2
def baseEnd_4835289 : Nat := 827609120132612547750139

theorem tailTrace_4835289 : CollatzResearch.WordTrace tailWord_4835289 prefixEnd_4835289 827609120132612547750139 := by
  unfold tailWord_4835289
  simp only [CollatzResearch.WordTrace]
  refine ⟨176357478179581229460884921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117571652119720819640589947 176357478179581229460884921)
  ·
    refine ⟨132268108634685922095663691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176357478179581229460884921 132268108634685922095663691)
    ·
      refine ⟨198402162952028883143495537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132268108634685922095663691 198402162952028883143495537)
      ·
        refine ⟨148801622214021662357621653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198402162952028883143495537 148801622214021662357621653)
        ·
          refine ⟨6975076041282265423013515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 148801622214021662357621653 6975076041282265423013515)
          ·
            refine ⟨10462614061923398134520273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6975076041282265423013515 10462614061923398134520273)
            ·
              refine ⟨7846960546442548600890205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10462614061923398134520273 7846960546442548600890205)
              ·
                refine ⟨2942610204915955725333827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7846960546442548600890205 2942610204915955725333827)
                ·
                  refine ⟨4413915307373933588000741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2942610204915955725333827 4413915307373933588000741)
                  ·
                    refine ⟨827609120132612547750139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4413915307373933588000741 827609120132612547750139)
                    ·
                      rfl

theorem cell23_4835289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 1, 4].length) (baseStart_4835289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835289 prefixEnd_4835289 := by exact prefixLift 4835289
  have htrace : WordTrace (prefixWord ++ tailWord_4835289) baseStart_4835289 baseEnd_4835289 := by
    simpa [prefixWord, tailWord_4835289, baseEnd_4835289] using wordTrace_append hprefix tailTrace_4835289
  have hstable : (prefixWord ++ tailWord_4835289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835289).length < 2 ^ (prefixWord ++ tailWord_4835289).sum := by decide
  have hdescent : baseEnd_4835289 < baseStart_4835289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835328 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 1, 6]
def baseStart_4835328 : Nat := 118140960795 + 4835328 * 2 ^ 59
def prefixEnd_4835328 : Nat := 4983230072969 + 3 ^ 40 * 4835328 * 2
def baseEnd_4835328 : Nat := 827615795381120996887579

theorem tailTrace_4835328 : CollatzResearch.WordTrace tailWord_4835328 prefixEnd_4835328 827615795381120996887579 := by
  unfold tailWord_4835328
  simp only [CollatzResearch.WordTrace]
  refine ⟨88179450313219969560777319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117572600417626626081036425 88179450313219969560777319)
  ·
    refine ⟨132269175469829954341165979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88179450313219969560777319 132269175469829954341165979)
    ·
      refine ⟨198403763204744931511748969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132269175469829954341165979 198403763204744931511748969)
      ·
        refine ⟨148802822403558698633811727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198403763204744931511748969 148802822403558698633811727)
        ·
          refine ⟨223204233605338047950717591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148802822403558698633811727 223204233605338047950717591)
          ·
            refine ⟨334806350408007071926076387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223204233605338047950717591 334806350408007071926076387)
            ·
              refine ⟨502209525612010607889114581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334806350408007071926076387 502209525612010607889114581)
              ·
                refine ⟨11770535756531498622401123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 502209525612010607889114581 11770535756531498622401123)
                ·
                  refine ⟨17655803634797247933601685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11770535756531498622401123 17655803634797247933601685)
                  ·
                    refine ⟨827615795381120996887579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17655803634797247933601685 827615795381120996887579)
                    ·
                      rfl

theorem cell23_4835328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_4835328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835328 prefixEnd_4835328 := by exact prefixLift 4835328
  have htrace : WordTrace (prefixWord ++ tailWord_4835328) baseStart_4835328 baseEnd_4835328 := by
    simpa [prefixWord, tailWord_4835328, baseEnd_4835328] using wordTrace_append hprefix tailTrace_4835328
  have hstable : (prefixWord ++ tailWord_4835328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835328).length < 2 ^ (prefixWord ++ tailWord_4835328).sum := by decide
  have hdescent : baseEnd_4835328 < baseStart_4835328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835362 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_4835362 : Nat := 118140960795 + 4835362 * 2 ^ 59
def prefixEnd_4835362 : Nat := 4983230072969 + 3 ^ 40 * 4835362 * 2
def baseEnd_4835362 : Nat := 827621614828538619212527

theorem tailTrace_4835362 : CollatzResearch.WordTrace tailWord_4835362 prefixEnd_4835362 827621614828538619212527 := by
  unfold tailWord_4835362
  simp only [CollatzResearch.WordTrace]
  refine ⟨44090035177079190732073085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117573427138877841952194893 44090035177079190732073085)
  ·
    refine ⟨16533763191404696524527407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44090035177079190732073085 16533763191404696524527407)
    ·
      refine ⟨24800644787107044786791111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16533763191404696524527407 24800644787107044786791111)
      ·
        refine ⟨37200967180660567180186667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24800644787107044786791111 37200967180660567180186667)
        ·
          refine ⟨55801450770990850770280001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37200967180660567180186667 55801450770990850770280001)
          ·
            refine ⟨41851088078243138077710001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55801450770990850770280001 41851088078243138077710001)
            ·
              refine ⟨31388316058682353558282501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41851088078243138077710001 31388316058682353558282501)
              ·
                refine ⟨5885309261002941292177969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31388316058682353558282501 5885309261002941292177969)
                ·
                  refine ⟨4413981945752205969133477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5885309261002941292177969 4413981945752205969133477)
                  ·
                    refine ⟨827621614828538619212527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4413981945752205969133477 827621614828538619212527)
                    ·
                      rfl

theorem cell23_4835362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_4835362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835362 prefixEnd_4835362 := by exact prefixLift 4835362
  have htrace : WordTrace (prefixWord ++ tailWord_4835362) baseStart_4835362 baseEnd_4835362 := by
    simpa [prefixWord, tailWord_4835362, baseEnd_4835362] using wordTrace_append hprefix tailTrace_4835362
  have hstable : (prefixWord ++ tailWord_4835362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835362).length < 2 ^ (prefixWord ++ tailWord_4835362).sum := by decide
  have hdescent : baseEnd_4835362 < baseStart_4835362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835382 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_4835382 : Nat := 118140960795 + 4835382 * 2 ^ 59
def prefixEnd_4835382 : Nat := 4983230072969 + 3 ^ 40 * 4835382 * 2
def baseEnd_4835382 : Nat := 2482875114098705779387489

theorem tailTrace_4835382 : CollatzResearch.WordTrace tailWord_4835382 prefixEnd_4835382 2482875114098705779387489 := by
  unfold tailWord_4835382
  simp only [CollatzResearch.WordTrace]
  refine ⟨11022554385515269146501275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117573913445496204229346933 11022554385515269146501275)
  ·
    refine ⟨16533831578272903719751913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11022554385515269146501275 16533831578272903719751913)
    ·
      refine ⟨12400373683704677789813935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16533831578272903719751913 12400373683704677789813935)
      ·
        refine ⟨18600560525557016684720903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12400373683704677789813935 18600560525557016684720903)
        ·
          refine ⟨27900840788335525027081355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18600560525557016684720903 27900840788335525027081355)
          ·
            refine ⟨41851261182503287540622033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27900840788335525027081355 41851261182503287540622033)
            ·
              refine ⟨31388445886877465655466525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41851261182503287540622033 31388445886877465655466525)
              ·
                refine ⟨11770667207579049620799947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31388445886877465655466525 11770667207579049620799947)
                ·
                  refine ⟨17656000811368574431199921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11770667207579049620799947 17656000811368574431199921)
                  ·
                    refine ⟨13242000608526430823399941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17656000811368574431199921 13242000608526430823399941)
                    ·
                      refine ⟨2482875114098705779387489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13242000608526430823399941 2482875114098705779387489)
                      ·
                        rfl

theorem cell23_4835382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_4835382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835382 prefixEnd_4835382 := by exact prefixLift 4835382
  have htrace : WordTrace (prefixWord ++ tailWord_4835382) baseStart_4835382 baseEnd_4835382 := by
    simpa [prefixWord, tailWord_4835382, baseEnd_4835382] using wordTrace_append hprefix tailTrace_4835382
  have hstable : (prefixWord ++ tailWord_4835382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835382).length < 2 ^ (prefixWord ++ tailWord_4835382).sum := by decide
  have hdescent : baseEnd_4835382 < baseStart_4835382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835420 : List Nat := [2, 2, 4, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_4835420 : Nat := 118140960795 + 4835420 * 2 ^ 59
def prefixEnd_4835420 : Nat := 4983230072969 + 3 ^ 40 * 4835420 * 2
def baseEnd_4835420 : Nat := 2482894626363576630712315

theorem tailTrace_4835420 : CollatzResearch.WordTrace tailWord_4835420 prefixEnd_4835420 2482894626363576630712315 := by
  unfold tailWord_4835420
  simp only [CollatzResearch.WordTrace]
  refine ⟨88181128071053319416951857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117574837428071092555935809 88181128071053319416951857)
  ·
    refine ⟨66135846053289989562713893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88181128071053319416951857 66135846053289989562713893)
    ·
      refine ⟨12400471134991873043008855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66135846053289989562713893 12400471134991873043008855)
      ·
        refine ⟨18600706702487809564513283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12400471134991873043008855 18600706702487809564513283)
        ·
          refine ⟨27901060053731714346769925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18600706702487809564513283 27901060053731714346769925)
          ·
            refine ⟨5231448760074696440019361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27901060053731714346769925 5231448760074696440019361)
            ·
              refine ⟨3923586570056022330014521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5231448760074696440019361 3923586570056022330014521)
              ·
                refine ⟨2942689927542016747510891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3923586570056022330014521 2942689927542016747510891)
                ·
                  refine ⟨4414034891313025121266337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2942689927542016747510891 4414034891313025121266337)
                  ·
                    refine ⟨3310526168484768840949753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4414034891313025121266337 3310526168484768840949753)
                    ·
                      refine ⟨2482894626363576630712315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3310526168484768840949753 2482894626363576630712315)
                      ·
                        rfl

theorem cell23_4835420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_4835420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835420 prefixEnd_4835420 := by exact prefixLift 4835420
  have htrace : WordTrace (prefixWord ++ tailWord_4835420) baseStart_4835420 baseEnd_4835420 := by
    simpa [prefixWord, tailWord_4835420, baseEnd_4835420] using wordTrace_append hprefix tailTrace_4835420
  have hstable : (prefixWord ++ tailWord_4835420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835420).length < 2 ^ (prefixWord ++ tailWord_4835420).sum := by decide
  have hdescent : baseEnd_4835420 < baseStart_4835420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835515 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 4]
def baseStart_4835515 : Nat := 118140960795 + 4835515 * 2 ^ 59
def prefixEnd_4835515 : Nat := 4983230072969 + 3 ^ 40 * 4835515 * 2
def baseEnd_4835515 : Nat := 2482943407025753759024377

theorem tailTrace_4835515 : CollatzResearch.WordTrace tailWord_4835515 prefixEnd_4835515 2482943407025753759024377 := by
  unfold tailWord_4835515
  simp only [CollatzResearch.WordTrace]
  refine ⟨176365721076762470058611999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117577147384508313372407999 176365721076762470058611999)
  ·
    refine ⟨264548581615143705087917999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176365721076762470058611999 264548581615143705087917999)
    ·
      refine ⟨396822872422715557631876999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264548581615143705087917999 396822872422715557631876999)
      ·
        refine ⟨595234308634073336447815499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396822872422715557631876999 595234308634073336447815499)
        ·
          refine ⟨892851462951110004671723249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595234308634073336447815499 892851462951110004671723249)
          ·
            refine ⟨669638597213332503503792437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 892851462951110004671723249 669638597213332503503792437)
            ·
              refine ⟨62778618488749922203480541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 669638597213332503503792437 62778618488749922203480541)
              ·
                refine ⟨23541981933281220826305203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62778618488749922203480541 23541981933281220826305203)
                ·
                  refine ⟨35312972899921831239457805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23541981933281220826305203 35312972899921831239457805)
                  ·
                    refine ⟨13242364837470686714796677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35312972899921831239457805 13242364837470686714796677)
                    ·
                      refine ⟨2482943407025753759024377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13242364837470686714796677 2482943407025753759024377)
                      ·
                        rfl

theorem cell23_4835515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 4].length) (baseStart_4835515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835515 prefixEnd_4835515 := by exact prefixLift 4835515
  have htrace : WordTrace (prefixWord ++ tailWord_4835515) baseStart_4835515 baseEnd_4835515 := by
    simpa [prefixWord, tailWord_4835515, baseEnd_4835515] using wordTrace_append hprefix tailTrace_4835515
  have hstable : (prefixWord ++ tailWord_4835515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835515).length < 2 ^ (prefixWord ++ tailWord_4835515).sum := by decide
  have hdescent : baseEnd_4835515 < baseStart_4835515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835516 : List Nat := [2, 2, 2, 3, 3, 2, 1, 3, 5]
def baseStart_4835516 : Nat := 118140960795 + 4835516 * 2 ^ 59
def prefixEnd_4835516 : Nat := 4983230072969 + 3 ^ 40 * 4835516 * 2
def baseEnd_4835516 : Nat := 275882657834045361679097

theorem tailTrace_4835516 : CollatzResearch.WordTrace tailWord_4835516 prefixEnd_4835516 275882657834045361679097 := by
  unfold tailWord_4835516
  simp only [CollatzResearch.WordTrace]
  refine ⟨88182878774879423614699201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117577171699839231486265601 88182878774879423614699201)
  ·
    refine ⟨66137159081159567711024401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88182878774879423614699201 66137159081159567711024401)
    ·
      refine ⟨49602869310869675783268301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66137159081159567711024401 49602869310869675783268301)
      ·
        refine ⟨18601075991576128418725613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49602869310869675783268301 18601075991576128418725613)
        ·
          refine ⟨6975403496841048157022105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18601075991576128418725613 6975403496841048157022105)
          ·
            refine ⟨5231552622630786117766579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6975403496841048157022105 5231552622630786117766579)
            ·
              refine ⟨7847328933946179176649869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5231552622630786117766579 7847328933946179176649869)
              ·
                refine ⟨2942748350229817191243701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7847328933946179176649869 2942748350229817191243701)
                ·
                  refine ⟨275882657834045361679097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2942748350229817191243701 275882657834045361679097)
                  ·
                    rfl

theorem cell23_4835516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_4835516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835516 prefixEnd_4835516 := by exact prefixLift 4835516
  have htrace : WordTrace (prefixWord ++ tailWord_4835516) baseStart_4835516 baseEnd_4835516 := by
    simpa [prefixWord, tailWord_4835516, baseEnd_4835516] using wordTrace_append hprefix tailTrace_4835516
  have hstable : (prefixWord ++ tailWord_4835516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835516).length < 2 ^ (prefixWord ++ tailWord_4835516).sum := by decide
  have hdescent : baseEnd_4835516 < baseStart_4835516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835545 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_4835545 : Nat := 118140960795 + 4835545 * 2 ^ 59
def prefixEnd_4835545 : Nat := 4983230072969 + 3 ^ 40 * 4835545 * 2
def baseEnd_4835545 : Nat := 2482958811445388641649239

theorem tailTrace_4835545 : CollatzResearch.WordTrace tailWord_4835545 prefixEnd_4835545 2482958811445388641649239 := by
  unfold tailWord_4835545
  simp only [CollatzResearch.WordTrace]
  refine ⟨176366815266653785182204089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117577876844435856788136059 176366815266653785182204089)
  ·
    refine ⟨132275111449990338886653067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176366815266653785182204089 132275111449990338886653067)
    ·
      refine ⟨198412667174985508329979601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132275111449990338886653067 198412667174985508329979601)
      ·
        refine ⟨148809500381239131247484701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198412667174985508329979601 148809500381239131247484701)
        ·
          refine ⟨55803562642964674217806763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148809500381239131247484701 55803562642964674217806763)
          ·
            refine ⟨83705343964447011326710145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55803562642964674217806763 83705343964447011326710145)
            ·
              refine ⟨62779007973335258495032609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83705343964447011326710145 62779007973335258495032609)
              ·
                refine ⟨47084255980001443871274457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62779007973335258495032609 47084255980001443871274457)
                ·
                  refine ⟨35313191985001082903455843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47084255980001443871274457 35313191985001082903455843)
                  ·
                    refine ⟨52969787977501624355183765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35313191985001082903455843 52969787977501624355183765)
                    ·
                      refine ⟨2482958811445388641649239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52969787977501624355183765 2482958811445388641649239)
                      ·
                        rfl

theorem cell23_4835545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_4835545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835545 prefixEnd_4835545 := by exact prefixLift 4835545
  have htrace : WordTrace (prefixWord ++ tailWord_4835545) baseStart_4835545 baseEnd_4835545 := by
    simpa [prefixWord, tailWord_4835545, baseEnd_4835545] using wordTrace_append hprefix tailTrace_4835545
  have hstable : (prefixWord ++ tailWord_4835545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835545).length < 2 ^ (prefixWord ++ tailWord_4835545).sum := by decide
  have hdescent : baseEnd_4835545 < baseStart_4835545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835552 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 3]
def baseStart_4835552 : Nat := 118140960795 + 4835552 * 2 ^ 59
def prefixEnd_4835552 : Nat := 4983230072969 + 3 ^ 40 * 4835552 * 2
def baseEnd_4835552 : Nat := 2482962405809970114261707

theorem tailTrace_4835552 : CollatzResearch.WordTrace tailWord_4835552 prefixEnd_4835552 2482962405809970114261707 := by
  unfold tailWord_4835552
  simp only [CollatzResearch.WordTrace]
  refine ⟨88183535288814212688854455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117578047051752283585139273 88183535288814212688854455)
  ·
    refine ⟨132275302933221319033281683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88183535288814212688854455 132275302933221319033281683)
    ·
      refine ⟨198412954399831978549922525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132275302933221319033281683 198412954399831978549922525)
      ·
        refine ⟨74404857899936991956220947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198412954399831978549922525 74404857899936991956220947)
        ·
          refine ⟨111607286849905487934331421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74404857899936991956220947 111607286849905487934331421)
          ·
            refine ⟨41852732568714557975374283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111607286849905487934331421 41852732568714557975374283)
            ·
              refine ⟨62779098853071836963061425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41852732568714557975374283 62779098853071836963061425)
              ·
                refine ⟨47084324139803877722296069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62779098853071836963061425 47084324139803877722296069)
                ·
                  refine ⟨8828310776213227072930513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47084324139803877722296069 8828310776213227072930513)
                  ·
                    refine ⟨6621233082159920304697885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8828310776213227072930513 6621233082159920304697885)
                    ·
                      refine ⟨2482962405809970114261707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6621233082159920304697885 2482962405809970114261707)
                      ·
                        rfl

theorem cell23_4835552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_4835552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835552 prefixEnd_4835552 := by exact prefixLift 4835552
  have htrace : WordTrace (prefixWord ++ tailWord_4835552) baseStart_4835552 baseEnd_4835552 := by
    simpa [prefixWord, tailWord_4835552, baseEnd_4835552] using wordTrace_append hprefix tailTrace_4835552
  have hstable : (prefixWord ++ tailWord_4835552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835552).length < 2 ^ (prefixWord ++ tailWord_4835552).sum := by decide
  have hdescent : baseEnd_4835552 < baseStart_4835552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835586 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_4835586 : Nat := 118140960795 + 4835586 * 2 ^ 59
def prefixEnd_4835586 : Nat := 4983230072969 + 3 ^ 40 * 4835586 * 2
def baseEnd_4835586 : Nat := 2482979864152222981236551

theorem tailTrace_4835586 : CollatzResearch.WordTrace tailWord_4835586 prefixEnd_4835586 2482979864152222981236551 := by
  unfold tailWord_4835586
  simp only [CollatzResearch.WordTrace]
  refine ⟨44092077664876312296111653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117578873773003499456297741 44092077664876312296111653)
  ·
    refine ⟨8267264562164308555520935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44092077664876312296111653 8267264562164308555520935)
    ·
      refine ⟨12400896843246462833281403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8267264562164308555520935 12400896843246462833281403)
      ·
        refine ⟨18601345264869694249922105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12400896843246462833281403 18601345264869694249922105)
        ·
          refine ⟨13951008948652270687441579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18601345264869694249922105 13951008948652270687441579)
          ·
            refine ⟨20926513422978406031162369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13951008948652270687441579 20926513422978406031162369)
            ·
              refine ⟨15694885067233804523371777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20926513422978406031162369 15694885067233804523371777)
              ·
                refine ⟨11771163800425353392528833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15694885067233804523371777 11771163800425353392528833)
                ·
                  refine ⟨8828372850319015044396625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11771163800425353392528833 8828372850319015044396625)
                  ·
                    refine ⟨6621279637739261283297469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8828372850319015044396625 6621279637739261283297469)
                    ·
                      refine ⟨2482979864152222981236551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6621279637739261283297469 2482979864152222981236551)
                      ·
                        rfl

theorem cell23_4835586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_4835586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835586 prefixEnd_4835586 := by exact prefixLift 4835586
  have htrace : WordTrace (prefixWord ++ tailWord_4835586) baseStart_4835586 baseEnd_4835586 := by
    simpa [prefixWord, tailWord_4835586, baseEnd_4835586] using wordTrace_append hprefix tailTrace_4835586
  have hstable : (prefixWord ++ tailWord_4835586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835586).length < 2 ^ (prefixWord ++ tailWord_4835586).sum := by decide
  have hdescent : baseEnd_4835586 < baseStart_4835586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835593 : List Nat := [1, 2, 1, 1, 3, 6, 2, 2, 1, 4]
def baseStart_4835593 : Nat := 118140960795 + 4835593 * 2 ^ 59
def prefixEnd_4835593 : Nat := 4983230072969 + 3 ^ 40 * 4835593 * 2
def baseEnd_4835593 : Nat := 827661152838934817949673

theorem tailTrace_4835593 : CollatzResearch.WordTrace tailWord_4835593 prefixEnd_4835593 827661152838934817949673 := by
  unfold tailWord_4835593
  simp only [CollatzResearch.WordTrace]
  refine ⟨176368565970479889379951433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117579043980319926253300955 176368565970479889379951433)
  ·
    refine ⟨132276424477859917034963575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176368565970479889379951433 132276424477859917034963575)
    ·
      refine ⟨198414636716789875552445363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132276424477859917034963575 198414636716789875552445363)
      ·
        refine ⟨297621955075184813328668045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198414636716789875552445363 297621955075184813328668045)
        ·
          refine ⟨111608233153194304998250517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297621955075184813328668045 111608233153194304998250517)
          ·
            refine ⟨5231635929055983046792993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111608233153194304998250517 5231635929055983046792993)
            ·
              refine ⟨3923726946791987285094745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5231635929055983046792993 3923726946791987285094745)
              ·
                refine ⟨2942795210093990463821059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3923726946791987285094745 2942795210093990463821059)
                ·
                  refine ⟨4414192815140985695731589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2942795210093990463821059 4414192815140985695731589)
                  ·
                    refine ⟨827661152838934817949673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4414192815140985695731589 827661152838934817949673)
                    ·
                      rfl

theorem cell23_4835593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 1, 4].length) (baseStart_4835593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835593 prefixEnd_4835593 := by exact prefixLift 4835593
  have htrace : WordTrace (prefixWord ++ tailWord_4835593) baseStart_4835593 baseEnd_4835593 := by
    simpa [prefixWord, tailWord_4835593, baseEnd_4835593] using wordTrace_append hprefix tailTrace_4835593
  have hstable : (prefixWord ++ tailWord_4835593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835593).length < 2 ^ (prefixWord ++ tailWord_4835593).sum := by decide
  have hdescent : baseEnd_4835593 < baseStart_4835593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835616 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 3, 1, 3]
def baseStart_4835616 : Nat := 118140960795 + 4835616 * 2 ^ 59
def prefixEnd_4835616 : Nat := 4983230072969 + 3 ^ 40 * 4835616 * 2
def baseEnd_4835616 : Nat := 2482995268571857863861413

theorem tailTrace_4835616 : CollatzResearch.WordTrace tailWord_4835616 prefixEnd_4835616 2482995268571857863861413 := by
  unfold tailWord_4835616
  simp only [CollatzResearch.WordTrace]
  refine ⟨88184702424698282154019351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117579603232931042872025801 88184702424698282154019351)
  ·
    refine ⟨132277053637047423231029027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88184702424698282154019351 132277053637047423231029027)
    ·
      refine ⟨198415580455571134846543541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132277053637047423231029027 198415580455571134846543541)
      ·
        refine ⟨18601460667709793891863457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198415580455571134846543541 18601460667709793891863457)
        ·
          refine ⟨13951095500782345418897593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18601460667709793891863457 13951095500782345418897593)
          ·
            refine ⟨10463321625586759064173195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13951095500782345418897593 10463321625586759064173195)
            ·
              refine ⟨15694982438380138596259793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10463321625586759064173195 15694982438380138596259793)
              ·
                refine ⟨11771236828785103947194845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15694982438380138596259793 11771236828785103947194845)
                ·
                  refine ⟨4414213810794413980198067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11771236828785103947194845 4414213810794413980198067)
                  ·
                    refine ⟨6621320716191620970297101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4414213810794413980198067 6621320716191620970297101)
                    ·
                      refine ⟨2482995268571857863861413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6621320716191620970297101 2482995268571857863861413)
                      ·
                        rfl

theorem cell23_4835616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_4835616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835616 prefixEnd_4835616 := by exact prefixLift 4835616
  have htrace : WordTrace (prefixWord ++ tailWord_4835616) baseStart_4835616 baseEnd_4835616 := by
    simpa [prefixWord, tailWord_4835616, baseEnd_4835616] using wordTrace_append hprefix tailTrace_4835616
  have hstable : (prefixWord ++ tailWord_4835616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835616).length < 2 ^ (prefixWord ++ tailWord_4835616).sum := by decide
  have hdescent : baseEnd_4835616 < baseStart_4835616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835636 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_4835636 : Nat := 118140960795 + 4835636 * 2 ^ 59
def prefixEnd_4835636 : Nat := 4983230072969 + 3 ^ 40 * 4835636 * 2
def baseEnd_4835636 : Nat := 827668512728315928537107

theorem tailTrace_4835636 : CollatzResearch.WordTrace tailWord_4835636 prefixEnd_4835636 827668512728315928537107 := by
  unfold tailWord_4835636
  simp only [CollatzResearch.WordTrace]
  refine ⟨88185067154662053861883381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117580089539549405149177841 88185067154662053861883381)
  ·
    refine ⟨8267350045749567549551567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88185067154662053861883381 8267350045749567549551567)
    ·
      refine ⟨12401025068624351324327351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8267350045749567549551567 12401025068624351324327351)
      ·
        refine ⟨18601537602936526986491027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12401025068624351324327351 18601537602936526986491027)
        ·
          refine ⟨27902306404404790479736541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18601537602936526986491027 27902306404404790479736541)
          ·
            refine ⟨10463364901651796429901203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27902306404404790479736541 10463364901651796429901203)
            ·
              refine ⟨15695047352477694644851805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10463364901651796429901203 15695047352477694644851805)
              ·
                refine ⟨5885642757179135491819427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15695047352477694644851805 5885642757179135491819427)
                ·
                  refine ⟨8828464135768703237729141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5885642757179135491819427 8828464135768703237729141)
                  ·
                    refine ⟨827668512728315928537107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8828464135768703237729141 827668512728315928537107)
                    ·
                      rfl

theorem cell23_4835636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_4835636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835636 prefixEnd_4835636 := by exact prefixLift 4835636
  have htrace : WordTrace (prefixWord ++ tailWord_4835636) baseStart_4835636 baseEnd_4835636 := by
    simpa [prefixWord, tailWord_4835636, baseEnd_4835636] using wordTrace_append hprefix tailTrace_4835636
  have hstable : (prefixWord ++ tailWord_4835636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835636).length < 2 ^ (prefixWord ++ tailWord_4835636).sum := by decide
  have hdescent : baseEnd_4835636 < baseStart_4835636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835656 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 3, 2, 2]
def baseStart_4835656 : Nat := 118140960795 + 4835656 * 2 ^ 59
def prefixEnd_4835656 : Nat := 4983230072969 + 3 ^ 40 * 4835656 * 2
def baseEnd_4835656 : Nat := 2483015807798037707361229

theorem tailTrace_4835656 : CollatzResearch.WordTrace tailWord_4835656 prefixEnd_4835656 2483015807798037707361229 := by
  unfold tailWord_4835656
  simp only [CollatzResearch.WordTrace]
  refine ⟨88185431884625825569747411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117580575846167767426329881 88185431884625825569747411)
  ·
    refine ⟨132278147826938738354621117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88185431884625825569747411 132278147826938738354621117)
    ·
      refine ⟨49604305435102026882982919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132278147826938738354621117 49604305435102026882982919)
      ·
        refine ⟨74406458152653040324474379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49604305435102026882982919 74406458152653040324474379)
        ·
          refine ⟨111609687228979560486711569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74406458152653040324474379 111609687228979560486711569)
          ·
            refine ⟨83707265421734670365033677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111609687228979560486711569 83707265421734670365033677)
            ·
              refine ⟨31390224533150501386887629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83707265421734670365033677 31390224533150501386887629)
              ·
                refine ⟨11771334199931438020082861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31390224533150501386887629 11771334199931438020082861)
                ·
                  refine ⟨4414250324974289257531073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11771334199931438020082861 4414250324974289257531073)
                  ·
                    refine ⟨3310687743730716943148305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4414250324974289257531073 3310687743730716943148305)
                    ·
                      refine ⟨2483015807798037707361229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3310687743730716943148305 2483015807798037707361229)
                      ·
                        rfl

theorem cell23_4835656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_4835656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835656 prefixEnd_4835656 := by exact prefixLift 4835656
  have htrace : WordTrace (prefixWord ++ tailWord_4835656) baseStart_4835656 baseEnd_4835656 := by
    simpa [prefixWord, tailWord_4835656, baseEnd_4835656] using wordTrace_append hprefix tailTrace_4835656
  have hstable : (prefixWord ++ tailWord_4835656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835656).length < 2 ^ (prefixWord ++ tailWord_4835656).sum := by decide
  have hdescent : baseEnd_4835656 < baseStart_4835656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835669 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_4835669 : Nat := 118140960795 + 4835669 * 2 ^ 59
def prefixEnd_4835669 : Nat := 4983230072969 + 3 ^ 40 * 4835669 * 2
def baseEnd_4835669 : Nat := 2483022483046546156498669

theorem tailTrace_4835669 : CollatzResearch.WordTrace tailWord_4835669 prefixEnd_4835669 2483022483046546156498669 := by
  unfold tailWord_4835669
  simp only [CollatzResearch.WordTrace]
  refine ⟨176371337918204554359718061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117580891945469702906478707 176371337918204554359718061)
  ·
    refine ⟨66139251719326707884894273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176371337918204554359718061 66139251719326707884894273)
    ·
      refine ⟨49604438789495030913670705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66139251719326707884894273 49604438789495030913670705)
      ·
        refine ⟨37203329092121273185253029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49604438789495030913670705 37203329092121273185253029)
        ·
          refine ⟨6975624204772738722234943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37203329092121273185253029 6975624204772738722234943)
          ·
            refine ⟨10463436307159108083352415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6975624204772738722234943 10463436307159108083352415)
            ·
              refine ⟨15695154460738662125028623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10463436307159108083352415 15695154460738662125028623)
              ·
                refine ⟨23542731691107993187542935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15695154460738662125028623 23542731691107993187542935)
                ·
                  refine ⟨35314097536661989781314403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23542731691107993187542935 35314097536661989781314403)
                  ·
                    refine ⟨52971146304992984671971605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35314097536661989781314403 52971146304992984671971605)
                    ·
                      refine ⟨2483022483046546156498669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52971146304992984671971605 2483022483046546156498669)
                      ·
                        rfl

theorem cell23_4835669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_4835669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835669 prefixEnd_4835669 := by exact prefixLift 4835669
  have htrace : WordTrace (prefixWord ++ tailWord_4835669) baseStart_4835669 baseEnd_4835669 := by
    simpa [prefixWord, tailWord_4835669, baseEnd_4835669] using wordTrace_append hprefix tailTrace_4835669
  have hstable : (prefixWord ++ tailWord_4835669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835669).length < 2 ^ (prefixWord ++ tailWord_4835669).sum := by decide
  have hdescent : baseEnd_4835669 < baseStart_4835669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835689 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 6, 1, 3]
def baseStart_4835689 : Nat := 118140960795 + 4835689 * 2 ^ 59
def prefixEnd_4835689 : Nat := 4983230072969 + 3 ^ 40 * 4835689 * 2
def baseEnd_4835689 : Nat := 2483032752659636078248577

theorem tailTrace_4835689 : CollatzResearch.WordTrace tailWord_4835689 prefixEnd_4835689 2483032752659636078248577 := by
  unfold tailWord_4835689
  simp only [CollatzResearch.WordTrace]
  refine ⟨176372067378132097775446121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117581378252088065183630747 176372067378132097775446121)
  ·
    refine ⟨132279050533599073331584591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176372067378132097775446121 132279050533599073331584591)
    ·
      refine ⟨198418575800398609997376887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132279050533599073331584591 198418575800398609997376887)
      ·
        refine ⟨297627863700597914996065331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198418575800398609997376887 297627863700597914996065331)
        ·
          refine ⟨446441795550896872494097997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297627863700597914996065331 446441795550896872494097997)
          ·
            refine ⟨167415673331586327185286749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 446441795550896872494097997 167415673331586327185286749)
            ·
              refine ⟨62780877499344872694482531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167415673331586327185286749 62780877499344872694482531)
              ·
                refine ⟨94171316249017309041723797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62780877499344872694482531 94171316249017309041723797)
                ·
                  refine ⟨4414280449172686361330803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94171316249017309041723797 4414280449172686361330803)
                  ·
                    refine ⟨6621420673759029541996205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4414280449172686361330803 6621420673759029541996205)
                    ·
                      refine ⟨2483032752659636078248577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6621420673759029541996205 2483032752659636078248577)
                      ·
                        rfl

theorem cell23_4835689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 1, 3].length) (baseStart_4835689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835689 prefixEnd_4835689 := by exact prefixLift 4835689
  have htrace : WordTrace (prefixWord ++ tailWord_4835689) baseStart_4835689 baseEnd_4835689 := by
    simpa [prefixWord, tailWord_4835689, baseEnd_4835689] using wordTrace_append hprefix tailTrace_4835689
  have hstable : (prefixWord ++ tailWord_4835689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835689).length < 2 ^ (prefixWord ++ tailWord_4835689).sum := by decide
  have hdescent : baseEnd_4835689 < baseStart_4835689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835716 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_4835716 : Nat := 118140960795 + 4835716 * 2 ^ 59
def prefixEnd_4835716 : Nat := 4983230072969 + 3 ^ 40 * 4835716 * 2
def baseEnd_4835716 : Nat := 2483046616637307472610953

theorem tailTrace_4835716 : CollatzResearch.WordTrace tailWord_4835716 prefixEnd_4835716 2483046616637307472610953 := by
  unfold tailWord_4835716
  simp only [CollatzResearch.WordTrace]
  refine ⟨88186526074517140693339501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117582034766022854257786001 88186526074517140693339501)
  ·
    refine ⟨33069947277943927760002313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88186526074517140693339501 33069947277943927760002313)
    ·
      refine ⟨24802460458457945820001735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33069947277943927760002313 24802460458457945820001735)
      ·
        refine ⟨37203690687686918730002603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24802460458457945820001735 37203690687686918730002603)
        ·
          refine ⟨55805536031530378095003905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37203690687686918730002603 55805536031530378095003905)
          ·
            refine ⟨41854152023647783571252929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55805536031530378095003905 41854152023647783571252929)
            ·
              refine ⟨31390614017735837678439697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41854152023647783571252929 31390614017735837678439697)
              ·
                refine ⟨23542960513301878258829773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31390614017735837678439697 23542960513301878258829773)
                ·
                  refine ⟨8828610192488204347061165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23542960513301878258829773 8828610192488204347061165)
                  ·
                    refine ⟨3310728822183076630147937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8828610192488204347061165 3310728822183076630147937)
                    ·
                      refine ⟨2483046616637307472610953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3310728822183076630147937 2483046616637307472610953)
                      ·
                        rfl

theorem cell23_4835716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_4835716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835716 prefixEnd_4835716 := by exact prefixLift 4835716
  have htrace : WordTrace (prefixWord ++ tailWord_4835716) baseStart_4835716 baseEnd_4835716 := by
    simpa [prefixWord, tailWord_4835716, baseEnd_4835716] using wordTrace_append hprefix tailTrace_4835716
  have hstable : (prefixWord ++ tailWord_4835716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835716).length < 2 ^ (prefixWord ++ tailWord_4835716).sum := by decide
  have hdescent : baseEnd_4835716 < baseStart_4835716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835723 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 2, 1, 3]
def baseStart_4835723 : Nat := 118140960795 + 4835723 * 2 ^ 59
def prefixEnd_4835723 : Nat := 4983230072969 + 3 ^ 40 * 4835723 * 2
def baseEnd_4835723 : Nat := 2483050211001888945223421

theorem tailTrace_4835723 : CollatzResearch.WordTrace tailWord_4835723 prefixEnd_4835723 2483050211001888945223421 := by
  unfold tailWord_4835723
  simp only [CollatzResearch.WordTrace]
  refine ⟨176373307460008921582183823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117582204973339281054789215 176373307460008921582183823)
  ·
    refine ⟨264559961190013382373275735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176373307460008921582183823 264559961190013382373275735)
    ·
      refine ⟨396839941785020073559913603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264559961190013382373275735 396839941785020073559913603)
      ·
        refine ⟨595259912677530110339870405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396839941785020073559913603 595259912677530110339870405)
        ·
          refine ⟨111611233627036895688725701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 595259912677530110339870405 111611233627036895688725701)
          ·
            refine ⟨20927106305069417941636069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111611233627036895688725701 20927106305069417941636069)
            ·
              refine ⟨3923832432200515864056763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20927106305069417941636069 3923832432200515864056763)
              ·
                refine ⟨5885748648300773796085145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923832432200515864056763 5885748648300773796085145)
                ·
                  refine ⟨4414311486225580347063859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5885748648300773796085145 4414311486225580347063859)
                  ·
                    refine ⟨6621467229338370520595789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4414311486225580347063859 6621467229338370520595789)
                    ·
                      refine ⟨2483050211001888945223421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6621467229338370520595789 2483050211001888945223421)
                      ·
                        rfl

theorem cell23_4835723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 2, 1, 3].length) (baseStart_4835723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835723 prefixEnd_4835723 := by exact prefixLift 4835723
  have htrace : WordTrace (prefixWord ++ tailWord_4835723) baseStart_4835723 baseEnd_4835723 := by
    simpa [prefixWord, tailWord_4835723, baseEnd_4835723] using wordTrace_append hprefix tailTrace_4835723
  have hstable : (prefixWord ++ tailWord_4835723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835723).length < 2 ^ (prefixWord ++ tailWord_4835723).sum := by decide
  have hdescent : baseEnd_4835723 < baseStart_4835723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835780 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_4835780 : Nat := 118140960795 + 4835780 * 2 ^ 59
def prefixEnd_4835780 : Nat := 4983230072969 + 3 ^ 40 * 4835780 * 2
def baseEnd_4835780 : Nat := 2483079479399195222210659

theorem tailTrace_4835780 : CollatzResearch.WordTrace tailWord_4835780 prefixEnd_4835780 2483079479399195222210659 := by
  unfold tailWord_4835780
  simp only [CollatzResearch.WordTrace]
  refine ⟨88187693210401210158504397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117583590947201613544672529 88187693210401210158504397)
  ·
    refine ⟨33070384953900453809439149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88187693210401210158504397 33070384953900453809439149)
    ·
      refine ⟨12401394357712670178539681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33070384953900453809439149 12401394357712670178539681)
      ·
        refine ⟨9301045768284502633904761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12401394357712670178539681 9301045768284502633904761)
        ·
          refine ⟨6975784326213376975428571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9301045768284502633904761 6975784326213376975428571)
          ·
            refine ⟨10463676489320065463142857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6975784326213376975428571 10463676489320065463142857)
            ·
              refine ⟨7847757366990049097357143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10463676489320065463142857 7847757366990049097357143)
              ·
                refine ⟨11771636050485073646035715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7847757366990049097357143 11771636050485073646035715)
                ·
                  refine ⟨17657454075727610469053573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11771636050485073646035715 17657454075727610469053573)
                  ·
                    refine ⟨3310772639198926962947545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17657454075727610469053573 3310772639198926962947545)
                    ·
                      refine ⟨2483079479399195222210659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3310772639198926962947545 2483079479399195222210659)
                      ·
                        rfl

theorem cell23_4835780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_4835780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835780 prefixEnd_4835780 := by exact prefixLift 4835780
  have htrace : WordTrace (prefixWord ++ tailWord_4835780) baseStart_4835780 baseEnd_4835780 := by
    simpa [prefixWord, tailWord_4835780, baseEnd_4835780] using wordTrace_append hprefix tailTrace_4835780
  have hstable : (prefixWord ++ tailWord_4835780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835780).length < 2 ^ (prefixWord ++ tailWord_4835780).sum := by decide
  have hdescent : baseEnd_4835780 < baseStart_4835780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835819 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 4]
def baseStart_4835819 : Nat := 118140960795 + 4835819 * 2 ^ 59
def prefixEnd_4835819 : Nat := 4983230072969 + 3 ^ 40 * 4835819 * 2
def baseEnd_4835819 : Nat := 2483099505144720569622979

theorem tailTrace_4835819 : CollatzResearch.WordTrace tailWord_4835819 prefixEnd_4835819 2483099505144720569622979 := by
  unfold tailWord_4835819
  simp only [CollatzResearch.WordTrace]
  refine ⟨176376808867661129977678511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117584539245107419985119007 176376808867661129977678511)
  ·
    refine ⟨264565213301491694966517767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176376808867661129977678511 264565213301491694966517767)
    ·
      refine ⟨396847819952237542449776651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264565213301491694966517767 396847819952237542449776651)
      ·
        refine ⟨595271729928356313674664977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396847819952237542449776651 595271729928356313674664977)
        ·
          refine ⟨446453797446267235255998733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595271729928356313674664977 446453797446267235255998733)
          ·
            refine ⟨167420174042350213220999525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 446453797446267235255998733 167420174042350213220999525)
            ·
              refine ⟨31391282632940664978937411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167420174042350213220999525 31391282632940664978937411)
              ·
                refine ⟨47086923949410997468406117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31391282632940664978937411 47086923949410997468406117)
                ·
                  refine ⟨8828798240514562025326147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47086923949410997468406117 8828798240514562025326147)
                  ·
                    refine ⟨13243197360771843037989221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8828798240514562025326147 13243197360771843037989221)
                    ·
                      refine ⟨2483099505144720569622979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13243197360771843037989221 2483099505144720569622979)
                      ·
                        rfl

theorem cell23_4835819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 4].length) (baseStart_4835819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835819 prefixEnd_4835819 := by exact prefixLift 4835819
  have htrace : WordTrace (prefixWord ++ tailWord_4835819) baseStart_4835819 baseEnd_4835819 := by
    simpa [prefixWord, tailWord_4835819, baseEnd_4835819] using wordTrace_append hprefix tailTrace_4835819
  have hstable : (prefixWord ++ tailWord_4835819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835819).length < 2 ^ (prefixWord ++ tailWord_4835819).sum := by decide
  have hdescent : baseEnd_4835819 < baseStart_4835819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835839 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 3]
def baseStart_4835839 : Nat := 118140960795 + 4835839 * 2 ^ 59
def prefixEnd_4835839 : Nat := 4983230072969 + 3 ^ 40 * 4835839 * 2
def baseEnd_4835839 : Nat := 2483109774757810491372887

theorem tailTrace_4835839 : CollatzResearch.WordTrace tailWord_4835839 prefixEnd_4835839 2483109774757810491372887 := by
  unfold tailWord_4835839
  simp only [CollatzResearch.WordTrace]
  refine ⟨176377538327588673393406571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117585025551725782262271047 176377538327588673393406571)
  ·
    refine ⟨264566307491383010090109857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176377538327588673393406571 264566307491383010090109857)
    ·
      refine ⟨198424730618537257567582393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264566307491383010090109857 198424730618537257567582393)
      ·
        refine ⟨148818547963902943175686795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198424730618537257567582393 148818547963902943175686795)
        ·
          refine ⟨223227821945854414763530193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148818547963902943175686795 223227821945854414763530193)
          ·
            refine ⟨167420866459390811072647645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223227821945854414763530193 167420866459390811072647645)
            ·
              refine ⟨62782824922271554152242867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167420866459390811072647645 62782824922271554152242867)
              ·
                refine ⟨94174237383407331228364301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62782824922271554152242867 94174237383407331228364301)
                ·
                  refine ⟨35315339018777749210636613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94174237383407331228364301 35315339018777749210636613)
                  ·
                    refine ⟨6621626066020827976994365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35315339018777749210636613 6621626066020827976994365)
                    ·
                      refine ⟨2483109774757810491372887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6621626066020827976994365 2483109774757810491372887)
                      ·
                        rfl

theorem cell23_4835839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_4835839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835839 prefixEnd_4835839 := by exact prefixLift 4835839
  have htrace : WordTrace (prefixWord ++ tailWord_4835839) baseStart_4835839 baseEnd_4835839 := by
    simpa [prefixWord, tailWord_4835839, baseEnd_4835839] using wordTrace_append hprefix tailTrace_4835839
  have hstable : (prefixWord ++ tailWord_4835839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835839).length < 2 ^ (prefixWord ++ tailWord_4835839).sum := by decide
  have hdescent : baseEnd_4835839 < baseStart_4835839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835880 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 3, 4]
def baseStart_4835880 : Nat := 118140960795 + 4835880 * 2 ^ 59
def prefixEnd_4835880 : Nat := 4983230072969 + 3 ^ 40 * 4835880 * 2
def baseEnd_4835880 : Nat := 827710275821548276986733

theorem tailTrace_4835880 : CollatzResearch.WordTrace tailWord_4835880 prefixEnd_4835880 827710275821548276986733 := by
  unfold tailWord_4835880
  simp only [CollatzResearch.WordTrace]
  refine ⟨88189516860220068697824547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117586022480293424930432729 88189516860220068697824547)
  ·
    refine ⟨132284275290330103046736821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88189516860220068697824547 132284275290330103046736821)
    ·
      refine ⟨12401650808468447160631577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132284275290330103046736821 12401650808468447160631577)
      ·
        refine ⟨9301238106351335370473683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12401650808468447160631577 9301238106351335370473683)
        ·
          refine ⟨13951857159527003055710525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9301238106351335370473683 13951857159527003055710525)
          ·
            refine ⟨5231946434822626145891447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13951857159527003055710525 5231946434822626145891447)
            ·
              refine ⟨7847919652233939218837171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5231946434822626145891447 7847919652233939218837171)
              ·
                refine ⟨11771879478350908828255757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7847919652233939218837171 11771879478350908828255757)
                ·
                  refine ⟨4414454804381590810595909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11771879478350908828255757 4414454804381590810595909)
                  ·
                    refine ⟨827710275821548276986733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4414454804381590810595909 827710275821548276986733)
                    ·
                      rfl

theorem cell23_4835880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_4835880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835880 prefixEnd_4835880 := by exact prefixLift 4835880
  have htrace : WordTrace (prefixWord ++ tailWord_4835880) baseStart_4835880 baseEnd_4835880 := by
    simpa [prefixWord, tailWord_4835880, baseEnd_4835880] using wordTrace_append hprefix tailTrace_4835880
  have hstable : (prefixWord ++ tailWord_4835880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835880).length < 2 ^ (prefixWord ++ tailWord_4835880).sum := by decide
  have hdescent : baseEnd_4835880 < baseStart_4835880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835919 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 3, 6]
def baseStart_4835919 : Nat := 118140960795 + 4835919 * 2 ^ 59
def prefixEnd_4835919 : Nat := 4983230072969 + 3 ^ 40 * 4835919 * 2
def baseEnd_4835919 : Nat := 827716951070056726124173

theorem tailTrace_4835919 : CollatzResearch.WordTrace tailWord_4835919 prefixEnd_4835919 827716951070056726124173 := by
  unfold tailWord_4835919
  simp only [CollatzResearch.WordTrace]
  refine ⟨176380456167298847056318811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117586970778199231370879207 176380456167298847056318811)
  ·
    refine ⟨264570684250948270584478217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176380456167298847056318811 264570684250948270584478217)
    ·
      refine ⟨198428013188211202938358663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264570684250948270584478217 198428013188211202938358663)
      ·
        refine ⟨297642019782316804407537995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198428013188211202938358663 297642019782316804407537995)
        ·
          refine ⟨446463029673475206611306993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297642019782316804407537995 446463029673475206611306993)
          ·
            refine ⟨334847272255106404958480245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446463029673475206611306993 334847272255106404958480245)
            ·
              refine ⟨31391931773916225464857523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 334847272255106404958480245 31391931773916225464857523)
              ·
                refine ⟨47087897660874338197286285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31391931773916225464857523 47087897660874338197286285)
                ·
                  refine ⟨17657961622827876823982357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47087897660874338197286285 17657961622827876823982357)
                  ·
                    refine ⟨827716951070056726124173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17657961622827876823982357 827716951070056726124173)
                    ·
                      rfl

theorem cell23_4835919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_4835919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835919 prefixEnd_4835919 := by exact prefixLift 4835919
  have htrace : WordTrace (prefixWord ++ tailWord_4835919) baseStart_4835919 baseEnd_4835919 := by
    simpa [prefixWord, tailWord_4835919, baseEnd_4835919] using wordTrace_append hprefix tailTrace_4835919
  have hstable : (prefixWord ++ tailWord_4835919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835919).length < 2 ^ (prefixWord ++ tailWord_4835919).sum := by decide
  have hdescent : baseEnd_4835919 < baseStart_4835919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835936 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 4, 4]
def baseStart_4835936 : Nat := 118140960795 + 4835936 * 2 ^ 59
def prefixEnd_4835936 : Nat := 4983230072969 + 3 ^ 40 * 4835936 * 2
def baseEnd_4835936 : Nat := 827719860793765537286647

theorem tailTrace_4835936 : CollatzResearch.WordTrace tailWord_4835936 prefixEnd_4835936 827719860793765537286647 := by
  unfold tailWord_4835936
  simp only [CollatzResearch.WordTrace]
  refine ⟨88190538104118629479843831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117587384138824839306458441 88190538104118629479843831)
  ·
    refine ⟨132285807156177944219765747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88190538104118629479843831 132285807156177944219765747)
    ·
      refine ⟨198428710734266916329648621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132285807156177944219765747 198428710734266916329648621)
      ·
        refine ⟨74410766525350093623618233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198428710734266916329648621 74410766525350093623618233)
        ·
          refine ⟨55808074894012570217713675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74410766525350093623618233 55808074894012570217713675)
          ·
            refine ⟨83712112341018855326570513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55808074894012570217713675 83712112341018855326570513)
            ·
              refine ⟨62784084255764141494927885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83712112341018855326570513 62784084255764141494927885)
              ·
                refine ⟨23544031595911553060597957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62784084255764141494927885 23544031595911553060597957)
                ·
                  refine ⟨4414505924233416198862117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23544031595911553060597957 4414505924233416198862117)
                  ·
                    refine ⟨827719860793765537286647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4414505924233416198862117 827719860793765537286647)
                    ·
                      rfl

theorem cell23_4835936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4, 4].length) (baseStart_4835936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835936 prefixEnd_4835936 := by exact prefixLift 4835936
  have htrace : WordTrace (prefixWord ++ tailWord_4835936) baseStart_4835936 baseEnd_4835936 := by
    simpa [prefixWord, tailWord_4835936, baseEnd_4835936] using wordTrace_append hprefix tailTrace_4835936
  have hstable : (prefixWord ++ tailWord_4835936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835936).length < 2 ^ (prefixWord ++ tailWord_4835936).sum := by decide
  have hdescent : baseEnd_4835936 < baseStart_4835936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835937 : List Nat := [1, 2, 3, 1, 1, 4, 4, 2, 1, 1, 3]
def baseStart_4835937 : Nat := 118140960795 + 4835937 * 2 ^ 59
def prefixEnd_4835937 : Nat := 4983230072969 + 3 ^ 40 * 4835937 * 2
def baseEnd_4835937 : Nat := 2483160095861951107947437

theorem tailTrace_4835937 : CollatzResearch.WordTrace tailWord_4835937 prefixEnd_4835937 2483160095861951107947437 := by
  unfold tailWord_4835937
  simp only [CollatzResearch.WordTrace]
  refine ⟨176381112681233636130474065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117587408454155757420316043 176381112681233636130474065)
  ·
    refine ⟨132285834510925227097855549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176381112681233636130474065 132285834510925227097855549)
    ·
      refine ⟨49607187941596960161695831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132285834510925227097855549 49607187941596960161695831)
      ·
        refine ⟨74410781912395440242543747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49607187941596960161695831 74410781912395440242543747)
        ·
          refine ⟨111616172868593160363815621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74410781912395440242543747 111616172868593160363815621)
          ·
            refine ⟨20928032412861217568215429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111616172868593160363815621 20928032412861217568215429)
            ·
              refine ⟨3924006077411478294040393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20928032412861217568215429 3924006077411478294040393)
              ·
                refine ⟨2943004558058608720530295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3924006077411478294040393 2943004558058608720530295)
                ·
                  refine ⟨4414506837087913080795443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943004558058608720530295 4414506837087913080795443)
                  ·
                    refine ⟨6621760255631869621193165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4414506837087913080795443 6621760255631869621193165)
                    ·
                      refine ⟨2483160095861951107947437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6621760255631869621193165 2483160095861951107947437)
                      ·
                        rfl

theorem cell23_4835937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_4835937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835937 prefixEnd_4835937 := by exact prefixLift 4835937
  have htrace : WordTrace (prefixWord ++ tailWord_4835937) baseStart_4835937 baseEnd_4835937 := by
    simpa [prefixWord, tailWord_4835937, baseEnd_4835937] using wordTrace_append hprefix tailTrace_4835937
  have hstable : (prefixWord ++ tailWord_4835937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835937).length < 2 ^ (prefixWord ++ tailWord_4835937).sum := by decide
  have hdescent : baseEnd_4835937 < baseStart_4835937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835946 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_4835946 : Nat := 118140960795 + 4835946 * 2 ^ 59
def prefixEnd_4835946 : Nat := 4983230072969 + 3 ^ 40 * 4835946 * 2
def baseEnd_4835946 : Nat := 2483164717187841572734895

theorem tailTrace_4835946 : CollatzResearch.WordTrace tailWord_4835946 prefixEnd_4835946 2483164717187841572734895 := by
  unfold tailWord_4835946
  simp only [CollatzResearch.WordTrace]
  refine ⟨44095360234550257666887923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117587627292134020445034461 44095360234550257666887923)
  ·
    refine ⟨66143040351825386500331885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44095360234550257666887923 66143040351825386500331885)
    ·
      refine ⟨24803640131934519937624457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66143040351825386500331885 24803640131934519937624457)
      ·
        refine ⟨18602730098950889953218343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24803640131934519937624457 18602730098950889953218343)
        ·
          refine ⟨27904095148426334929827515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18602730098950889953218343 27904095148426334929827515)
          ·
            refine ⟨41856142722639502394741273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27904095148426334929827515 41856142722639502394741273)
            ·
              refine ⟨31392107041979626796055955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41856142722639502394741273 31392107041979626796055955)
              ·
                refine ⟨47088160562969440194083933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31392107041979626796055955 47088160562969440194083933)
                ·
                  refine ⟨17658060211113540072781475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47088160562969440194083933 17658060211113540072781475)
                  ·
                    refine ⟨26487090316670310109172213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17658060211113540072781475 26487090316670310109172213)
                    ·
                      refine ⟨2483164717187841572734895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26487090316670310109172213 2483164717187841572734895)
                      ·
                        rfl

theorem cell23_4835946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_4835946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835946 prefixEnd_4835946 := by exact prefixLift 4835946
  have htrace : WordTrace (prefixWord ++ tailWord_4835946) baseStart_4835946 baseEnd_4835946 := by
    simpa [prefixWord, tailWord_4835946, baseEnd_4835946] using wordTrace_append hprefix tailTrace_4835946
  have hstable : (prefixWord ++ tailWord_4835946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835946).length < 2 ^ (prefixWord ++ tailWord_4835946).sum := by decide
  have hdescent : baseEnd_4835946 < baseStart_4835946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835979 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 1, 9]
def baseStart_4835979 : Nat := 118140960795 + 4835979 * 2 ^ 59
def prefixEnd_4835979 : Nat := 4983230072969 + 3 ^ 40 * 4835979 * 2
def baseEnd_4835979 : Nat := 827727220683146647874081

theorem tailTrace_4835979 : CollatzResearch.WordTrace tailWord_4835979 prefixEnd_4835979 827727220683146647874081 := by
  unfold tailWord_4835979
  simp only [CollatzResearch.WordTrace]
  refine ⟨176382644547081477303502991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117588429698054318202335327 176382644547081477303502991)
  ·
    refine ⟨264573966820622215955254487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176382644547081477303502991 264573966820622215955254487)
    ·
      refine ⟨396860950230933323932881731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264573966820622215955254487 396860950230933323932881731)
      ·
        refine ⟨595291425346399985899322597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396860950230933323932881731 595291425346399985899322597)
        ·
          refine ⟨111617142252449997356122987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 595291425346399985899322597 111617142252449997356122987)
          ·
            refine ⟨167425713378674996034184481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111617142252449997356122987 167425713378674996034184481)
            ·
              refine ⟨125569285034006247025638361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167425713378674996034184481 125569285034006247025638361)
              ·
                refine ⟨94176963775504685269228771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125569285034006247025638361 94176963775504685269228771)
                ·
                  refine ⟨141265445663257027903843157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94176963775504685269228771 141265445663257027903843157)
                  ·
                    refine ⟨827727220683146647874081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 141265445663257027903843157 827727220683146647874081)
                    ·
                      rfl

theorem cell23_4835979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 9].length) (baseStart_4835979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835979 prefixEnd_4835979 := by exact prefixLift 4835979
  have htrace : WordTrace (prefixWord ++ tailWord_4835979) baseStart_4835979 baseEnd_4835979 := by
    simpa [prefixWord, tailWord_4835979, baseEnd_4835979] using wordTrace_append hprefix tailTrace_4835979
  have hstable : (prefixWord ++ tailWord_4835979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835979).length < 2 ^ (prefixWord ++ tailWord_4835979).sum := by decide
  have hdescent : baseEnd_4835979 < baseStart_4835979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835993 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 4, 1, 3]
def baseStart_4835993 : Nat := 118140960795 + 4835993 * 2 ^ 59
def prefixEnd_4835993 : Nat := 4983230072969 + 3 ^ 40 * 4835993 * 2
def baseEnd_4835993 : Nat := 2483188850778602888847179

theorem tailTrace_4835993 : CollatzResearch.WordTrace tailWord_4835993 prefixEnd_4835993 2483188850778602888847179 := by
  unfold tailWord_4835993
  simp only [CollatzResearch.WordTrace]
  refine ⟨176383155169030757694512633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117588770112687171796341755 176383155169030757694512633)
  ·
    refine ⟨132287366376773068270884475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176383155169030757694512633 132287366376773068270884475)
    ·
      refine ⟨198431049565159602406326713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132287366376773068270884475 198431049565159602406326713)
      ·
        refine ⟨148823287173869701804745035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198431049565159602406326713 148823287173869701804745035)
        ·
          refine ⟨223234930760804552707117553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148823287173869701804745035 223234930760804552707117553)
          ·
            refine ⟨167426198070603414530338165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223234930760804552707117553 167426198070603414530338165)
            ·
              refine ⟨15696206069119070112219203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167426198070603414530338165 15696206069119070112219203)
              ·
                refine ⟨23544309103678605168328805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15696206069119070112219203 23544309103678605168328805)
                ·
                  refine ⟨4414557956939738469061651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23544309103678605168328805 4414557956939738469061651)
                  ·
                    refine ⟨6621836935409607703592477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4414557956939738469061651 6621836935409607703592477)
                    ·
                      refine ⟨2483188850778602888847179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6621836935409607703592477 2483188850778602888847179)
                      ·
                        rfl

theorem cell23_4835993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_4835993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835993 prefixEnd_4835993 := by exact prefixLift 4835993
  have htrace : WordTrace (prefixWord ++ tailWord_4835993) baseStart_4835993 baseEnd_4835993 := by
    simpa [prefixWord, tailWord_4835993, baseEnd_4835993] using wordTrace_append hprefix tailTrace_4835993
  have hstable : (prefixWord ++ tailWord_4835993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835993).length < 2 ^ (prefixWord ++ tailWord_4835993).sum := by decide
  have hdescent : baseEnd_4835993 < baseStart_4835993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4835994 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4835994 : Nat := 118140960795 + 4835994 * 2 ^ 59
def prefixEnd_4835994 : Nat := 4983230072969 + 3 ^ 40 * 4835994 * 2
def baseEnd_4835994 : Nat := 2483189364259257384934675

theorem tailTrace_4835994 : CollatzResearch.WordTrace tailWord_4835994 prefixEnd_4835994 2483189364259257384934675 := by
  unfold tailWord_4835994
  simp only [CollatzResearch.WordTrace]
  refine ⟨44095797910506783716324759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117588794428018089910199357 44095797910506783716324759)
  ·
    refine ⟨66143696865760175574487139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44095797910506783716324759 66143696865760175574487139)
    ·
      refine ⟨99215545298640263361730709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66143696865760175574487139 99215545298640263361730709)
      ·
        refine ⟨4650728685873762345081127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99215545298640263361730709 4650728685873762345081127)
        ·
          refine ⟨6976093028810643517621691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4650728685873762345081127 6976093028810643517621691)
          ·
            refine ⟨10464139543215965276432537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6976093028810643517621691 10464139543215965276432537)
            ·
              refine ⟨7848104657411973957324403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10464139543215965276432537 7848104657411973957324403)
              ·
                refine ⟨11772156986117960935986605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7848104657411973957324403 11772156986117960935986605)
                ·
                  refine ⟨4414558869794235350994977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11772156986117960935986605 4414558869794235350994977)
                  ·
                    refine ⟨3310919152345676513246233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4414558869794235350994977 3310919152345676513246233)
                    ·
                      refine ⟨2483189364259257384934675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3310919152345676513246233 2483189364259257384934675)
                      ·
                        rfl

theorem cell23_4835994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4835994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4835994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4835994 prefixEnd_4835994 := by exact prefixLift 4835994
  have htrace : WordTrace (prefixWord ++ tailWord_4835994) baseStart_4835994 baseEnd_4835994 := by
    simpa [prefixWord, tailWord_4835994, baseEnd_4835994] using wordTrace_append hprefix tailTrace_4835994
  have hstable : (prefixWord ++ tailWord_4835994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4835994).length < 2 ^ (prefixWord ++ tailWord_4835994).sum := by decide
  have hdescent : baseEnd_4835994 < baseStart_4835994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4835994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836003 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 3, 3, 2]
def baseStart_4836003 : Nat := 118140960795 + 4836003 * 2 ^ 59
def prefixEnd_4836003 : Nat := 4983230072969 + 3 ^ 40 * 4836003 * 2
def baseEnd_4836003 : Nat := 2483193985585147849722133

theorem tailTrace_4836003 : CollatzResearch.WordTrace tailWord_4836003 prefixEnd_4836003 2483193985585147849722133 := by
  unfold tailWord_4836003
  simp only [CollatzResearch.WordTrace]
  refine ⟨176383519898994529402376663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117589013265996352934917775 176383519898994529402376663)
  ·
    refine ⟨264575279848491794103564995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176383519898994529402376663 264575279848491794103564995)
    ·
      refine ⟨396862919772737691155347493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264575279848491794103564995 396862919772737691155347493)
      ·
        refine ⟨74411797457388317091627655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 396862919772737691155347493 74411797457388317091627655)
        ·
          refine ⟨111617696186082475637441483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74411797457388317091627655 111617696186082475637441483)
          ·
            refine ⟨167426544279123713456162225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111617696186082475637441483 167426544279123713456162225)
            ·
              refine ⟨125569908209342785092121669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167426544279123713456162225 125569908209342785092121669)
              ·
                refine ⟨23544357789251772204772813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125569908209342785092121669 23544357789251772204772813)
                ·
                  refine ⟨8829134170969414576789805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23544357789251772204772813 8829134170969414576789805)
                  ·
                    refine ⟨3310925314113530466296177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8829134170969414576789805 3310925314113530466296177)
                    ·
                      refine ⟨2483193985585147849722133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3310925314113530466296177 2483193985585147849722133)
                      ·
                        rfl

theorem cell23_4836003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_4836003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836003 prefixEnd_4836003 := by exact prefixLift 4836003
  have htrace : WordTrace (prefixWord ++ tailWord_4836003) baseStart_4836003 baseEnd_4836003 := by
    simpa [prefixWord, tailWord_4836003, baseEnd_4836003] using wordTrace_append hprefix tailTrace_4836003
  have hstable : (prefixWord ++ tailWord_4836003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836003).length < 2 ^ (prefixWord ++ tailWord_4836003).sum := by decide
  have hdescent : baseEnd_4836003 < baseStart_4836003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836007 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4836007 : Nat := 118140960795 + 4836007 * 2 ^ 59
def prefixEnd_4836007 : Nat := 4983230072969 + 3 ^ 40 * 4836007 * 2
def baseEnd_4836007 : Nat := 2483196039507765834072115

theorem tailTrace_4836007 : CollatzResearch.WordTrace tailWord_4836007 prefixEnd_4836007 2483196039507765834072115 := by
  unfold tailWord_4836007
  simp only [CollatzResearch.WordTrace]
  refine ⟨176383665790980038085522275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117589110527320025390348183 176383665790980038085522275)
  ·
    refine ⟨264575498686470057128283413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176383665790980038085522275 264575498686470057128283413)
    ·
      refine ⟨12401976500928283927888285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 264575498686470057128283413 12401976500928283927888285)
      ·
        refine ⟨4650741187848106472958107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12401976500928283927888285 4650741187848106472958107)
        ·
          refine ⟨6976111781772159709437161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4650741187848106472958107 6976111781772159709437161)
          ·
            refine ⟨5232083836329119782077871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6976111781772159709437161 5232083836329119782077871)
            ·
              refine ⟨7848125754493679673116807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5232083836329119782077871 7848125754493679673116807)
              ·
                refine ⟨11772188631740519509675211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7848125754493679673116807 11772188631740519509675211)
                ·
                  refine ⟨17658282947610779264512817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11772188631740519509675211 17658282947610779264512817)
                  ·
                    refine ⟨13243712210708084448384613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17658282947610779264512817 13243712210708084448384613)
                    ·
                      refine ⟨2483196039507765834072115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13243712210708084448384613 2483196039507765834072115)
                      ·
                        rfl

theorem cell23_4836007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4836007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836007 prefixEnd_4836007 := by exact prefixLift 4836007
  have htrace : WordTrace (prefixWord ++ tailWord_4836007) baseStart_4836007 baseEnd_4836007 := by
    simpa [prefixWord, tailWord_4836007, baseEnd_4836007] using wordTrace_append hprefix tailTrace_4836007
  have hstable : (prefixWord ++ tailWord_4836007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836007).length < 2 ^ (prefixWord ++ tailWord_4836007).sum := by decide
  have hdescent : baseEnd_4836007 < baseStart_4836007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836017 : List Nat := [1, 2, 2, 6, 2, 1, 2, 7]
def baseStart_4836017 : Nat := 118140960795 + 4836017 * 2 ^ 59
def prefixEnd_4836017 : Nat := 4983230072969 + 3 ^ 40 * 4836017 * 2
def baseEnd_4836017 : Nat := 91970413863492992405447

theorem tailTrace_4836017 : CollatzResearch.WordTrace tailWord_4836017 prefixEnd_4836017 91970413863492992405447 := by
  unfold tailWord_4836017
  simp only [CollatzResearch.WordTrace]
  refine ⟨176384030520943809793386305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117589353680629206528924203 176384030520943809793386305)
  ·
    refine ⟨132288022890707857345039729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176384030520943809793386305 132288022890707857345039729)
    ·
      refine ⟨99216017168030893008779797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132288022890707857345039729 99216017168030893008779797)
      ·
        refine ⟨4650750804751448109786553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99216017168030893008779797 4650750804751448109786553)
        ·
          refine ⟨3488063103563586082339915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4650750804751448109786553 3488063103563586082339915)
          ·
            refine ⟨5232094655345379123509873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3488063103563586082339915 5232094655345379123509873)
            ·
              refine ⟨3924070991509034342632405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5232094655345379123509873 3924070991509034342632405)
              ·
                refine ⟨91970413863492992405447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3924070991509034342632405 91970413863492992405447)
                ·
                  rfl

theorem cell23_4836017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 7].length) (baseStart_4836017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836017 prefixEnd_4836017 := by exact prefixLift 4836017
  have htrace : WordTrace (prefixWord ++ tailWord_4836017) baseStart_4836017 baseEnd_4836017 := by
    simpa [prefixWord, tailWord_4836017, baseEnd_4836017] using wordTrace_append hprefix tailTrace_4836017
  have hstable : (prefixWord ++ tailWord_4836017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836017).length < 2 ^ (prefixWord ++ tailWord_4836017).sum := by decide
  have hdescent : baseEnd_4836017 < baseStart_4836017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836210 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_4836210 : Nat := 118140960795 + 4836210 * 2 ^ 59
def prefixEnd_4836210 : Nat := 4983230072969 + 3 ^ 40 * 4836210 * 2
def baseEnd_4836210 : Nat := 827766758693542846611227

theorem tailTrace_4836210 : CollatzResearch.WordTrace tailWord_4836210 prefixEnd_4836210 827766758693542846611227 := by
  unfold tailWord_4836210
  simp only [CollatzResearch.WordTrace]
  refine ⟨44097767452311150938790521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117594046539496402503441389 44097767452311150938790521)
  ·
    refine ⟨33073325589233363204092891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44097767452311150938790521 33073325589233363204092891)
    ·
      refine ⟨49609988383850044806139337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33073325589233363204092891 49609988383850044806139337)
      ·
        refine ⟨37207491287887533604604503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49609988383850044806139337 37207491287887533604604503)
        ·
          refine ⟨55811236931831300406906755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37207491287887533604604503 55811236931831300406906755)
          ·
            refine ⟨83716855397746950610360133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55811236931831300406906755 83716855397746950610360133)
            ·
              refine ⟨15696910387077553239442525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83716855397746950610360133 15696910387077553239442525)
              ·
                refine ⟨5886341395154082464790947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15696910387077553239442525 5886341395154082464790947)
                ·
                  refine ⟨8829512092731123697186421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5886341395154082464790947 8829512092731123697186421)
                  ·
                    refine ⟨827766758693542846611227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8829512092731123697186421 827766758693542846611227)
                    ·
                      rfl

theorem cell23_4836210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_4836210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836210 prefixEnd_4836210 := by exact prefixLift 4836210
  have htrace : WordTrace (prefixWord ++ tailWord_4836210) baseStart_4836210 baseEnd_4836210 := by
    simpa [prefixWord, tailWord_4836210, baseEnd_4836210] using wordTrace_append hprefix tailTrace_4836210
  have hstable : (prefixWord ++ tailWord_4836210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836210).length < 2 ^ (prefixWord ++ tailWord_4836210).sum := by decide
  have hdescent : baseEnd_4836210 < baseStart_4836210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836217 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 2, 3, 2]
def baseStart_4836217 : Nat := 118140960795 + 4836217 * 2 ^ 59
def prefixEnd_4836217 : Nat := 4983230072969 + 3 ^ 40 * 4836217 * 2
def baseEnd_4836217 : Nat := 2483303870445210012446149

theorem tailTrace_4836217 : CollatzResearch.WordTrace tailWord_4836217 prefixEnd_4836217 2483303870445210012446149 := by
  unfold tailWord_4836217
  simp only [CollatzResearch.WordTrace]
  refine ⟨176391325120219243950666905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117594216746812829300444603 176391325120219243950666905)
  ·
    refine ⟨132293493840164432963000179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176391325120219243950666905 132293493840164432963000179)
    ·
      refine ⟨198440240760246649444500269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132293493840164432963000179 198440240760246649444500269)
      ·
        refine ⟨74415090285092493541687601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198440240760246649444500269 74415090285092493541687601)
        ·
          refine ⟨55811317713819370156265701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74415090285092493541687601 55811317713819370156265701)
          ·
            refine ⟨10464622071341131904299819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55811317713819370156265701 10464622071341131904299819)
            ·
              refine ⟨15696933107011697856449729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10464622071341131904299819 15696933107011697856449729)
              ·
                refine ⟨11772699830258773392337297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15696933107011697856449729 11772699830258773392337297)
                ·
                  refine ⟨8829524872694080044252973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11772699830258773392337297 8829524872694080044252973)
                  ·
                    refine ⟨3311071827260280016594865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8829524872694080044252973 3311071827260280016594865)
                    ·
                      refine ⟨2483303870445210012446149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311071827260280016594865 2483303870445210012446149)
                      ·
                        rfl

theorem cell23_4836217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_4836217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836217 prefixEnd_4836217 := by exact prefixLift 4836217
  have htrace : WordTrace (prefixWord ++ tailWord_4836217) baseStart_4836217 baseEnd_4836217 := by
    simpa [prefixWord, tailWord_4836217, baseEnd_4836217] using wordTrace_append hprefix tailTrace_4836217
  have hstable : (prefixWord ++ tailWord_4836217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836217).length < 2 ^ (prefixWord ++ tailWord_4836217).sum := by decide
  have hdescent : baseEnd_4836217 < baseStart_4836217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836247 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 5, 2, 2]
def baseStart_4836247 : Nat := 118140960795 + 4836247 * 2 ^ 59
def prefixEnd_4836247 : Nat := 4983230072969 + 3 ^ 40 * 4836247 * 2
def baseEnd_4836247 : Nat := 2483319274864844895071011

theorem tailTrace_4836247 : CollatzResearch.WordTrace tailWord_4836247 prefixEnd_4836247 2483319274864844895071011 := by
  unfold tailWord_4836247
  simp only [CollatzResearch.WordTrace]
  refine ⟨176392419310110559074258995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117594946206740372716172663 176392419310110559074258995)
  ·
    refine ⟨264588628965165838611388493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176392419310110559074258995 264588628965165838611388493)
    ·
      refine ⟨99220735861937189479270685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264588628965165838611388493 99220735861937189479270685)
      ·
        refine ⟨37207775948226446054726507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99220735861937189479270685 37207775948226446054726507)
        ·
          refine ⟨55811663922339669082089761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37207775948226446054726507 55811663922339669082089761)
          ·
            refine ⟨41858747941754751811567321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55811663922339669082089761 41858747941754751811567321)
            ·
              refine ⟨31394060956316063858675491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41858747941754751811567321 31394060956316063858675491)
              ·
                refine ⟨47091091434474095788013237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31394060956316063858675491 47091091434474095788013237)
                ·
                  refine ⟨4414789821981946480126241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47091091434474095788013237 4414789821981946480126241)
                  ·
                    refine ⟨3311092366486459860094681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4414789821981946480126241 3311092366486459860094681)
                    ·
                      refine ⟨2483319274864844895071011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311092366486459860094681 2483319274864844895071011)
                      ·
                        rfl

theorem cell23_4836247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_4836247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836247 prefixEnd_4836247 := by exact prefixLift 4836247
  have htrace : WordTrace (prefixWord ++ tailWord_4836247) baseStart_4836247 baseEnd_4836247 := by
    simpa [prefixWord, tailWord_4836247, baseEnd_4836247] using wordTrace_append hprefix tailTrace_4836247
  have hstable : (prefixWord ++ tailWord_4836247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836247).length < 2 ^ (prefixWord ++ tailWord_4836247).sum := by decide
  have hdescent : baseEnd_4836247 < baseStart_4836247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836253 : List Nat := [1, 4, 2, 1, 2, 1, 1, 11]
def baseStart_4836253 : Nat := 118140960795 + 4836253 * 2 ^ 59
def prefixEnd_4836253 : Nat := 4983230072969 + 3 ^ 40 * 4836253 * 2
def baseEnd_4836253 : Nat := 91974902064769328577629

theorem tailTrace_4836253 : CollatzResearch.WordTrace tailWord_4836253 prefixEnd_4836253 91974902064769328577629 := by
  unfold tailWord_4836253
  simp only [CollatzResearch.WordTrace]
  refine ⟨176392638148088822098977413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117595092098725881399318275 176392638148088822098977413)
  ·
    refine ⟨33073619652766654143558265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176392638148088822098977413 33073619652766654143558265)
    ·
      refine ⟨24805214739574990607668699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33073619652766654143558265 24805214739574990607668699)
      ·
        refine ⟨37207822109362485911503049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24805214739574990607668699 37207822109362485911503049)
        ·
          refine ⟨27905866582021864433627287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37207822109362485911503049 27905866582021864433627287)
          ·
            refine ⟨41858799873032796650440931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27905866582021864433627287 41858799873032796650440931)
            ·
              refine ⟨62788199809549194975661397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41858799873032796650440931 62788199809549194975661397)
              ·
                refine ⟨91974902064769328577629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 62788199809549194975661397 91974902064769328577629)
                ·
                  rfl

theorem cell23_4836253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 11].length) (baseStart_4836253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836253 prefixEnd_4836253 := by exact prefixLift 4836253
  have htrace : WordTrace (prefixWord ++ tailWord_4836253) baseStart_4836253 baseEnd_4836253 := by
    simpa [prefixWord, tailWord_4836253, baseEnd_4836253] using wordTrace_append hprefix tailTrace_4836253
  have hstable : (prefixWord ++ tailWord_4836253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836253).length < 2 ^ (prefixWord ++ tailWord_4836253).sum := by decide
  have hdescent : baseEnd_4836253 < baseStart_4836253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836260 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_4836260 : Nat := 118140960795 + 4836260 * 2 ^ 59
def prefixEnd_4836260 : Nat := 4983230072969 + 3 ^ 40 * 4836260 * 2
def baseEnd_4836260 : Nat := 2483325950113353344208451

theorem tailTrace_4836260 : CollatzResearch.WordTrace tailWord_4836260 prefixEnd_4836260 2483325950113353344208451 := by
  unfold tailWord_4836260
  simp only [CollatzResearch.WordTrace]
  refine ⟨88196446729531731147241117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117595262306042308196321489 88196446729531731147241117)
  ·
    refine ⟨33073667523574399180215419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88196446729531731147241117 33073667523574399180215419)
    ·
      refine ⟨49610501285361598770323129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33073667523574399180215419 49610501285361598770323129)
      ·
        refine ⟨37207875964021199077742347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49610501285361598770323129 37207875964021199077742347)
        ·
          refine ⟨55811813946031798616613521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37207875964021199077742347 55811813946031798616613521)
          ·
            refine ⟨41858860459523848962460141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55811813946031798616613521 41858860459523848962460141)
            ·
              refine ⟨15697072672321443360922553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41858860459523848962460141 15697072672321443360922553)
              ·
                refine ⟨11772804504241082520691915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15697072672321443360922553 11772804504241082520691915)
                ·
                  refine ⟨17659206756361623781037873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11772804504241082520691915 17659206756361623781037873)
                  ·
                    refine ⟨13244405067271217835778405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17659206756361623781037873 13244405067271217835778405)
                    ·
                      refine ⟨2483325950113353344208451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13244405067271217835778405 2483325950113353344208451)
                      ·
                        rfl

theorem cell23_4836260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_4836260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836260 prefixEnd_4836260 := by exact prefixLift 4836260
  have htrace : WordTrace (prefixWord ++ tailWord_4836260) baseStart_4836260 baseEnd_4836260 := by
    simpa [prefixWord, tailWord_4836260, baseEnd_4836260] using wordTrace_append hprefix tailTrace_4836260
  have hstable : (prefixWord ++ tailWord_4836260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836260).length < 2 ^ (prefixWord ++ tailWord_4836260).sum := by decide
  have hdescent : baseEnd_4836260 < baseStart_4836260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836270 : List Nat := [4, 1, 5, 13]
def baseStart_4836270 : Nat := 118140960795 + 4836270 * 2 ^ 59
def prefixEnd_4836270 : Nat := 4983230072969 + 3 ^ 40 * 4836270 * 2
def baseEnd_4836270 : Nat := 1135496609474119023815

theorem tailTrace_4836270 : CollatzResearch.WordTrace tailWord_4836270 prefixEnd_4836270 1135496609474119023815 := by
  unfold tailWord_4836270
  simp only [CollatzResearch.WordTrace]
  refine ⟨22049157273628404250293283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117595505459351489334897509 22049157273628404250293283)
  ·
    refine ⟨33073735910442606375439925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22049157273628404250293283 33073735910442606375439925)
    ·
      refine ⟨3100662741603994347697493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33073735910442606375439925 3100662741603994347697493)
      ·
        refine ⟨1135496609474119023815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3100662741603994347697493 1135496609474119023815)
        ·
          rfl

theorem cell23_4836270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 13].length) (baseStart_4836270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836270 prefixEnd_4836270 := by exact prefixLift 4836270
  have htrace : WordTrace (prefixWord ++ tailWord_4836270) baseStart_4836270 baseEnd_4836270 := by
    simpa [prefixWord, tailWord_4836270, baseEnd_4836270] using wordTrace_append hprefix tailTrace_4836270
  have hstable : (prefixWord ++ tailWord_4836270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836270).length < 2 ^ (prefixWord ++ tailWord_4836270).sum := by decide
  have hdescent : baseEnd_4836270 < baseStart_4836270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836281 : List Nat := [1, 2, 1, 4, 2, 3, 1, 4, 1, 2, 2]
def baseStart_4836281 : Nat := 118140960795 + 4836281 * 2 ^ 59
def prefixEnd_4836281 : Nat := 4983230072969 + 3 ^ 40 * 4836281 * 2
def baseEnd_4836281 : Nat := 2483336733207097762045855

theorem tailTrace_4836281 : CollatzResearch.WordTrace tailWord_4836281 prefixEnd_4836281 2483336733207097762045855 := by
  unfold tailWord_4836281
  simp only [CollatzResearch.WordTrace]
  refine ⟨176393659391987382880996697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117595772927991588587331131 176393659391987382880996697)
  ·
    refine ⟨132295244543990537160747523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176393659391987382880996697 132295244543990537160747523)
    ·
      refine ⟨198442866815985805741121285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132295244543990537160747523 198442866815985805741121285)
      ·
        refine ⟨37208037527997338576460241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198442866815985805741121285 37208037527997338576460241)
        ·
          refine ⟨27906028145998003932345181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37208037527997338576460241 27906028145998003932345181)
          ·
            refine ⟨10464760554749251474629443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27906028145998003932345181 10464760554749251474629443)
            ·
              refine ⟨15697140832123877211944165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10464760554749251474629443 15697140832123877211944165)
              ·
                refine ⟨2943213906023226977239531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15697140832123877211944165 2943213906023226977239531)
                ·
                  refine ⟨4414820859034840465859297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943213906023226977239531 4414820859034840465859297)
                  ·
                    refine ⟨3311115644276130349394473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4414820859034840465859297 3311115644276130349394473)
                    ·
                      refine ⟨2483336733207097762045855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311115644276130349394473 2483336733207097762045855)
                      ·
                        rfl

theorem cell23_4836281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_4836281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836281 prefixEnd_4836281 := by exact prefixLift 4836281
  have htrace : WordTrace (prefixWord ++ tailWord_4836281) baseStart_4836281 baseEnd_4836281 := by
    simpa [prefixWord, tailWord_4836281, baseEnd_4836281] using wordTrace_append hprefix tailTrace_4836281
  have hstable : (prefixWord ++ tailWord_4836281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836281).length < 2 ^ (prefixWord ++ tailWord_4836281).sum := by decide
  have hdescent : baseEnd_4836281 < baseStart_4836281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836330 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_4836330 : Nat := 118140960795 + 4836330 * 2 ^ 59
def prefixEnd_4836330 : Nat := 4983230072969 + 3 ^ 40 * 4836330 * 2
def baseEnd_4836330 : Nat := 827787297919722690111043

theorem tailTrace_4836330 : CollatzResearch.WordTrace tailWord_4836330 prefixEnd_4836330 827787297919722690111043 := by
  unfold tailWord_4836330
  simp only [CollatzResearch.WordTrace]
  refine ⟨44098861642202466062382611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117596964379206576166353629 44098861642202466062382611)
  ·
    refine ⟨66148292463303699093573917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44098861642202466062382611 66148292463303699093573917)
    ·
      refine ⟨24805609673738887160090219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66148292463303699093573917 24805609673738887160090219)
      ·
        refine ⟨37208414510608330740135329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24805609673738887160090219 37208414510608330740135329)
        ·
          refine ⟨27906310882956248055101497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37208414510608330740135329 27906310882956248055101497)
          ·
            refine ⟨20929733162217186041326123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27906310882956248055101497 20929733162217186041326123)
            ·
              refine ⟨31394599743325779061989185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20929733162217186041326123 31394599743325779061989185)
              ·
                refine ⟨23545949807494334296491889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31394599743325779061989185 23545949807494334296491889)
                ·
                  refine ⟨17659462355620750722368917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23545949807494334296491889 17659462355620750722368917)
                  ·
                    refine ⟨827787297919722690111043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17659462355620750722368917 827787297919722690111043)
                    ·
                      rfl

theorem cell23_4836330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_4836330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836330 prefixEnd_4836330 := by exact prefixLift 4836330
  have htrace : WordTrace (prefixWord ++ tailWord_4836330) baseStart_4836330 baseEnd_4836330 := by
    simpa [prefixWord, tailWord_4836330, baseEnd_4836330] using wordTrace_append hprefix tailTrace_4836330
  have hstable : (prefixWord ++ tailWord_4836330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836330).length < 2 ^ (prefixWord ++ tailWord_4836330).sum := by decide
  have hdescent : baseEnd_4836330 < baseStart_4836330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836360 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 7]
def baseStart_4836360 : Nat := 118140960795 + 4836360 * 2 ^ 59
def prefixEnd_4836360 : Nat := 4983230072969 + 3 ^ 40 * 4836360 * 2
def baseEnd_4836360 : Nat := 275930810908755883661999

theorem tailTrace_4836360 : CollatzResearch.WordTrace tailWord_4836360 prefixEnd_4836360 275930810908755883661999 := by
  unfold tailWord_4836360
  simp only [CollatzResearch.WordTrace]
  refine ⟨88198270379350589686561267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117597693839134119582081689 88198270379350589686561267)
  ·
    refine ⟨132297405569025884529841901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88198270379350589686561267 132297405569025884529841901)
    ·
      refine ⟨49611527088384706698690713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132297405569025884529841901 49611527088384706698690713)
      ·
        refine ⟨37208645316288530024018035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49611527088384706698690713 37208645316288530024018035)
        ·
          refine ⟨55812967974432795036027053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37208645316288530024018035 55812967974432795036027053)
          ·
            refine ⟨20929862990412298138510145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55812967974432795036027053 20929862990412298138510145)
            ·
              refine ⟨15697397242809223603882609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20929862990412298138510145 15697397242809223603882609)
              ·
                refine ⟨11773047932106917702911957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15697397242809223603882609 11773047932106917702911957)
                ·
                  refine ⟨275930810908755883661999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11773047932106917702911957 275930810908755883661999)
                  ·
                    rfl

theorem cell23_4836360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 7].length) (baseStart_4836360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836360 prefixEnd_4836360 := by exact prefixLift 4836360
  have htrace : WordTrace (prefixWord ++ tailWord_4836360) baseStart_4836360 baseEnd_4836360 := by
    simpa [prefixWord, tailWord_4836360, baseEnd_4836360] using wordTrace_append hprefix tailTrace_4836360
  have hstable : (prefixWord ++ tailWord_4836360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836360).length < 2 ^ (prefixWord ++ tailWord_4836360).sum := by decide
  have hdescent : baseEnd_4836360 < baseStart_4836360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836377 : List Nat := [1, 2, 1, 2, 1, 1, 7, 3, 5]
def baseStart_4836377 : Nat := 118140960795 + 4836377 * 2 ^ 59
def prefixEnd_4836377 : Nat := 4983230072969 + 3 ^ 40 * 4836377 * 2
def baseEnd_4836377 : Nat := 275931780816658820716157

theorem tailTrace_4836377 : CollatzResearch.WordTrace tailWord_4836377 prefixEnd_4836377 275931780816658820716157 := by
  unfold tailWord_4836377
  simp only [CollatzResearch.WordTrace]
  refine ⟨176397160799639591276491385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117598107199759727517660923 176397160799639591276491385)
  ·
    refine ⟨132297870599729693457368539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176397160799639591276491385 132297870599729693457368539)
    ·
      refine ⟨198446805899594540186052809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132297870599729693457368539 198446805899594540186052809)
      ·
        refine ⟨148835104424695905139539607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198446805899594540186052809 148835104424695905139539607)
        ·
          refine ⟨223252656637043857709309411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148835104424695905139539607 223252656637043857709309411)
          ·
            refine ⟨334878984955565786563964117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223252656637043857709309411 334878984955565786563964117)
            ·
              refine ⟨7848726209896073122592909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 334878984955565786563964117 7848726209896073122592909)
              ·
                refine ⟨2943272328711027420972341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7848726209896073122592909 2943272328711027420972341)
                ·
                  refine ⟨275931780816658820716157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2943272328711027420972341 275931780816658820716157)
                  ·
                    rfl

theorem cell23_4836377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 5].length) (baseStart_4836377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836377 prefixEnd_4836377 := by exact prefixLift 4836377
  have htrace : WordTrace (prefixWord ++ tailWord_4836377) baseStart_4836377 baseEnd_4836377 := by
    simpa [prefixWord, tailWord_4836377, baseEnd_4836377] using wordTrace_append hprefix tailTrace_4836377
  have hstable : (prefixWord ++ tailWord_4836377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836377).length < 2 ^ (prefixWord ++ tailWord_4836377).sum := by decide
  have hdescent : baseEnd_4836377 < baseStart_4836377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836394 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 7]
def baseStart_4836394 : Nat := 118140960795 + 4836394 * 2 ^ 59
def prefixEnd_4836394 : Nat := 4983230072969 + 3 ^ 40 * 4836394 * 2
def baseEnd_4836394 : Nat := 275932750724561757770315

theorem tailTrace_4836394 : CollatzResearch.WordTrace tailWord_4836394 prefixEnd_4836394 275932750724561757770315 := by
  unfold tailWord_4836394
  simp only [CollatzResearch.WordTrace]
  refine ⟨44099445210144500794965059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117598520560385335453240157 44099445210144500794965059)
  ·
    refine ⟨66149167815216751192447589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44099445210144500794965059 66149167815216751192447589)
    ·
      refine ⟨12402968965353140848583923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66149167815216751192447589 12402968965353140848583923)
      ·
        refine ⟨18604453448029711272875885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12402968965353140848583923 18604453448029711272875885)
        ·
          refine ⟨6976670043011141727328457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18604453448029711272875885 6976670043011141727328457)
          ·
            refine ⟨5232502532258356295496343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6976670043011141727328457 5232502532258356295496343)
            ·
              refine ⟨7848753798387534443244515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5232502532258356295496343 7848753798387534443244515)
              ·
                refine ⟨11773130697581301664866773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7848753798387534443244515 11773130697581301664866773)
                ·
                  refine ⟨275932750724561757770315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11773130697581301664866773 275932750724561757770315)
                  ·
                    rfl

theorem cell23_4836394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_4836394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836394 prefixEnd_4836394 := by exact prefixLift 4836394
  have htrace : WordTrace (prefixWord ++ tailWord_4836394) baseStart_4836394 baseEnd_4836394 := by
    simpa [prefixWord, tailWord_4836394, baseEnd_4836394] using wordTrace_append hprefix tailTrace_4836394
  have hstable : (prefixWord ++ tailWord_4836394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836394).length < 2 ^ (prefixWord ++ tailWord_4836394).sum := by decide
  have hdescent : baseEnd_4836394 < baseStart_4836394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836400 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 5]
def baseStart_4836400 : Nat := 118140960795 + 4836400 * 2 ^ 59
def prefixEnd_4836400 : Nat := 4983230072969 + 3 ^ 40 * 4836400 * 2
def baseEnd_4836400 : Nat := 2483397837404982796457807

theorem tailTrace_4836400 : CollatzResearch.WordTrace tailWord_4836400 prefixEnd_4836400 2483397837404982796457807 := by
  unfold tailWord_4836400
  simp only [CollatzResearch.WordTrace]
  refine ⟨88198999839278133102289327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117598666452370844136385769 88198999839278133102289327)
  ·
    refine ⟨132298499758917199653433991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88198999839278133102289327 132298499758917199653433991)
    ·
      refine ⟨198447749638375799480150987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132298499758917199653433991 198447749638375799480150987)
      ·
        refine ⟨297671624457563699220226481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198447749638375799480150987 297671624457563699220226481)
        ·
          refine ⟨223253718343172774415169861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297671624457563699220226481 223253718343172774415169861)
          ·
            refine ⟨41860072189344895202844349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 223253718343172774415169861 41860072189344895202844349)
            ·
              refine ⟨15697527071004335701066631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41860072189344895202844349 15697527071004335701066631)
              ·
                refine ⟨23546290606506503551599947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15697527071004335701066631 23546290606506503551599947)
                ·
                  refine ⟨35319435909759755327399921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23546290606506503551599947 35319435909759755327399921)
                  ·
                    refine ⟨26489576932319816495549941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35319435909759755327399921 26489576932319816495549941)
                    ·
                      refine ⟨2483397837404982796457807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26489576932319816495549941 2483397837404982796457807)
                      ·
                        rfl

theorem cell23_4836400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_4836400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836400 prefixEnd_4836400 := by exact prefixLift 4836400
  have htrace : WordTrace (prefixWord ++ tailWord_4836400) baseStart_4836400 baseEnd_4836400 := by
    simpa [prefixWord, tailWord_4836400, baseEnd_4836400] using wordTrace_append hprefix tailTrace_4836400
  have hstable : (prefixWord ++ tailWord_4836400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836400).length < 2 ^ (prefixWord ++ tailWord_4836400).sum := by decide
  have hdescent : baseEnd_4836400 < baseStart_4836400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836410 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_4836410 : Nat := 118140960795 + 4836410 * 2 ^ 59
def prefixEnd_4836410 : Nat := 4983230072969 + 3 ^ 40 * 4836410 * 2
def baseEnd_4836410 : Nat := 2483402972211527757332761

theorem tailTrace_4836410 : CollatzResearch.WordTrace tailWord_4836410 prefixEnd_4836410 2483402972211527757332761 := by
  unfold tailWord_4836410
  simp only [CollatzResearch.WordTrace]
  refine ⟨44099591102130009478110671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117598909605680025274961789 44099591102130009478110671)
  ·
    refine ⟨66149386653195014217166007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44099591102130009478110671 66149386653195014217166007)
    ·
      refine ⟨99224079979792521325749011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66149386653195014217166007 99224079979792521325749011)
      ·
        refine ⟨148836119969688781988623517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99224079979792521325749011 148836119969688781988623517)
        ·
          refine ⟨55813544988633293245733819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148836119969688781988623517 55813544988633293245733819)
          ·
            refine ⟨83720317482949939868600729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55813544988633293245733819 83720317482949939868600729)
            ·
              refine ⟨62790238112212454901450547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83720317482949939868600729 62790238112212454901450547)
              ·
                refine ⟨94185357168318682352175821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62790238112212454901450547 94185357168318682352175821)
                ·
                  refine ⟨35319508938119505882065933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94185357168318682352175821 35319508938119505882065933)
                  ·
                    refine ⟨13244815851794814705774725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35319508938119505882065933 13244815851794814705774725)
                    ·
                      refine ⟨2483402972211527757332761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13244815851794814705774725 2483402972211527757332761)
                      ·
                        rfl

theorem cell23_4836410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_4836410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836410 prefixEnd_4836410 := by exact prefixLift 4836410
  have htrace : WordTrace (prefixWord ++ tailWord_4836410) baseStart_4836410 baseEnd_4836410 := by
    simpa [prefixWord, tailWord_4836410, baseEnd_4836410] using wordTrace_append hprefix tailTrace_4836410
  have hstable : (prefixWord ++ tailWord_4836410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836410).length < 2 ^ (prefixWord ++ tailWord_4836410).sum := by decide
  have hdescent : baseEnd_4836410 < baseStart_4836410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836440 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_4836440 : Nat := 118140960795 + 4836440 * 2 ^ 59
def prefixEnd_4836440 : Nat := 4983230072969 + 3 ^ 40 * 4836440 * 2
def baseEnd_4836440 : Nat := 2483418376631162639957623

theorem tailTrace_4836440 : CollatzResearch.WordTrace tailWord_4836440 prefixEnd_4836440 2483418376631162639957623 := by
  unfold tailWord_4836440
  simp only [CollatzResearch.WordTrace]
  refine ⟨88199729299205676518017387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117599639065607568690689849 88199729299205676518017387)
  ·
    refine ⟨132299593948808514777026081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88199729299205676518017387 132299593948808514777026081)
    ·
      refine ⟨99224695461606386082769561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132299593948808514777026081 99224695461606386082769561)
      ·
        refine ⟨74418521596204789562077171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99224695461606386082769561 74418521596204789562077171)
        ·
          refine ⟨111627782394307184343115757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74418521596204789562077171 111627782394307184343115757)
          ·
            refine ⟨41860418397865194128668409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111627782394307184343115757 41860418397865194128668409)
            ·
              refine ⟨31395313798398895596501307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41860418397865194128668409 31395313798398895596501307)
              ·
                refine ⟨47092970697598343394751961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31395313798398895596501307 47092970697598343394751961)
                ·
                  refine ⟨35319728023198757546063971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47092970697598343394751961 35319728023198757546063971)
                  ·
                    refine ⟨52979592034798136319095957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35319728023198757546063971 52979592034798136319095957)
                    ·
                      refine ⟨2483418376631162639957623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52979592034798136319095957 2483418376631162639957623)
                      ·
                        rfl

theorem cell23_4836440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_4836440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836440 prefixEnd_4836440 := by exact prefixLift 4836440
  have htrace : WordTrace (prefixWord ++ tailWord_4836440) baseStart_4836440 baseEnd_4836440 := by
    simpa [prefixWord, tailWord_4836440, baseEnd_4836440] using wordTrace_append hprefix tailTrace_4836440
  have hstable : (prefixWord ++ tailWord_4836440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836440).length < 2 ^ (prefixWord ++ tailWord_4836440).sum := by decide
  have hdescent : baseEnd_4836440 < baseStart_4836440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836444 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_4836444 : Nat := 118140960795 + 4836444 * 2 ^ 59
def prefixEnd_4836444 : Nat := 4983230072969 + 3 ^ 40 * 4836444 * 2
def baseEnd_4836444 : Nat := 2483420430553780624307605

theorem tailTrace_4836444 : CollatzResearch.WordTrace tailWord_4836444 prefixEnd_4836444 2483420430553780624307605 := by
  unfold tailWord_4836444
  simp only [CollatzResearch.WordTrace]
  refine ⟨88199802245198430859590193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117599736326931241146120257 88199802245198430859590193)
  ·
    refine ⟨66149851683898823144692645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88199802245198430859590193 66149851683898823144692645)
    ·
      refine ⟨12403097190731029339629871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66149851683898823144692645 12403097190731029339629871)
      ·
        refine ⟨18604645786096544009444807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12403097190731029339629871 18604645786096544009444807)
        ·
          refine ⟨27906968679144816014167211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18604645786096544009444807 27906968679144816014167211)
          ·
            refine ⟨41860453018717224021250817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27906968679144816014167211 41860453018717224021250817)
            ·
              refine ⟨31395339764037918015938113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41860453018717224021250817 31395339764037918015938113)
              ·
                refine ⟨23546504823028438511953585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31395339764037918015938113 23546504823028438511953585)
                ·
                  refine ⟨17659878617271328883965189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23546504823028438511953585 17659878617271328883965189)
                  ·
                    refine ⟨3311227240738374165743473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17659878617271328883965189 3311227240738374165743473)
                    ·
                      refine ⟨2483420430553780624307605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311227240738374165743473 2483420430553780624307605)
                      ·
                        rfl

theorem cell23_4836444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_4836444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836444 prefixEnd_4836444 := by exact prefixLift 4836444
  have htrace : WordTrace (prefixWord ++ tailWord_4836444) baseStart_4836444 baseEnd_4836444 := by
    simpa [prefixWord, tailWord_4836444, baseEnd_4836444] using wordTrace_append hprefix tailTrace_4836444
  have hstable : (prefixWord ++ tailWord_4836444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836444).length < 2 ^ (prefixWord ++ tailWord_4836444).sum := by decide
  have hdescent : baseEnd_4836444 < baseStart_4836444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836445 : List Nat := [1, 4, 4, 1, 3, 1, 2, 2, 5]
def baseStart_4836445 : Nat := 118140960795 + 4836445 * 2 ^ 59
def prefixEnd_4836445 : Nat := 4983230072969 + 3 ^ 40 * 4836445 * 2
def baseEnd_4836445 : Nat := 275935660448270568932789

theorem tailTrace_4836445 : CollatzResearch.WordTrace tailWord_4836445 prefixEnd_4836445 275935660448270568932789 := by
  unfold tailWord_4836445
  simp only [CollatzResearch.WordTrace]
  refine ⟨176399640963393238889966789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117599760642262159259977859 176399640963393238889966789)
  ·
    refine ⟨33074932680636232291868773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176399640963393238889966789 33074932680636232291868773)
    ·
      refine ⟨6201549877619293554725395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33074932680636232291868773 6201549877619293554725395)
      ·
        refine ⟨9302324816428940332088093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6201549877619293554725395 9302324816428940332088093)
        ·
          refine ⟨3488371806160852624533035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9302324816428940332088093 3488371806160852624533035)
          ·
            refine ⟨5232557709241278936799553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3488371806160852624533035 5232557709241278936799553)
            ·
              refine ⟨3924418281930959202599665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5232557709241278936799553 3924418281930959202599665)
              ·
                refine ⟨2943313711448219401949749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3924418281930959202599665 2943313711448219401949749)
                ·
                  refine ⟨275935660448270568932789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2943313711448219401949749 275935660448270568932789)
                  ·
                    rfl

theorem cell23_4836445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_4836445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836445 prefixEnd_4836445 := by exact prefixLift 4836445
  have htrace : WordTrace (prefixWord ++ tailWord_4836445) baseStart_4836445 baseEnd_4836445 := by
    simpa [prefixWord, tailWord_4836445, baseEnd_4836445] using wordTrace_append hprefix tailTrace_4836445
  have hstable : (prefixWord ++ tailWord_4836445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836445).length < 2 ^ (prefixWord ++ tailWord_4836445).sum := by decide
  have hdescent : baseEnd_4836445 < baseStart_4836445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836447 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 3]
def baseStart_4836447 : Nat := 118140960795 + 4836447 * 2 ^ 59
def prefixEnd_4836447 : Nat := 4983230072969 + 3 ^ 40 * 4836447 * 2
def baseEnd_4836447 : Nat := 2483421970995744112570091

theorem tailTrace_4836447 : CollatzResearch.WordTrace tailWord_4836447 prefixEnd_4836447 2483421970995744112570091 := by
  unfold tailWord_4836447
  simp only [CollatzResearch.WordTrace]
  refine ⟨176399713909385993231539595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117599809272923995487693063 176399713909385993231539595)
  ·
    refine ⟨264599570864078989847309393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176399713909385993231539595 264599570864078989847309393)
    ·
      refine ⟨198449678148059242385482045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264599570864078989847309393 198449678148059242385482045)
      ·
        refine ⟨74418629305522215894555767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198449678148059242385482045 74418629305522215894555767)
        ·
          refine ⟨111627943958283323841833651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74418629305522215894555767 111627943958283323841833651)
          ·
            refine ⟨167441915937424985762750477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111627943958283323841833651 167441915937424985762750477)
            ·
              refine ⟨62790718476534369661031429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167441915937424985762750477 62790718476534369661031429)
              ·
                refine ⟨11773259714350194311443393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62790718476534369661031429 11773259714350194311443393)
                ·
                  refine ⟨8829944785762645733582545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11773259714350194311443393 8829944785762645733582545)
                  ·
                    refine ⟨6622458589321984300186909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8829944785762645733582545 6622458589321984300186909)
                    ·
                      refine ⟨2483421970995744112570091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6622458589321984300186909 2483421970995744112570091)
                      ·
                        rfl

theorem cell23_4836447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_4836447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836447 prefixEnd_4836447 := by exact prefixLift 4836447
  have htrace : WordTrace (prefixWord ++ tailWord_4836447) baseStart_4836447 baseEnd_4836447 := by
    simpa [prefixWord, tailWord_4836447, baseEnd_4836447] using wordTrace_append hprefix tailTrace_4836447
  have hstable : (prefixWord ++ tailWord_4836447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836447).length < 2 ^ (prefixWord ++ tailWord_4836447).sum := by decide
  have hdescent : baseEnd_4836447 < baseStart_4836447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836478 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4836478 : Nat := 118140960795 + 4836478 * 2 ^ 59
def prefixEnd_4836478 : Nat := 4983230072969 + 3 ^ 40 * 4836478 * 2
def baseEnd_4836478 : Nat := 2483437888896033491282449

theorem tailTrace_4836478 : CollatzResearch.WordTrace tailWord_4836478 prefixEnd_4836478 2483437888896033491282449 := by
  unfold tailWord_4836478
  simp only [CollatzResearch.WordTrace]
  refine ⟨22050105571534210690739761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117600563048182457017278725 22050105571534210690739761)
  ·
    refine ⟨16537579178650658018054821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22050105571534210690739761 16537579178650658018054821)
    ·
      refine ⟨3100796095996998378385279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16537579178650658018054821 3100796095996998378385279)
      ·
        refine ⟨4651194143995497567577919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3100796095996998378385279 4651194143995497567577919)
        ·
          refine ⟨6976791215993246351366879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651194143995497567577919 6976791215993246351366879)
          ·
            refine ⟨10465186823989869527050319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6976791215993246351366879 10465186823989869527050319)
            ·
              refine ⟨15697780235984804290575479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10465186823989869527050319 15697780235984804290575479)
              ·
                refine ⟨23546670353977206435863219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15697780235984804290575479 23546670353977206435863219)
                ·
                  refine ⟨35320005530965809653794829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23546670353977206435863219 35320005530965809653794829)
                  ·
                    refine ⟨13245002074112178620173061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35320005530965809653794829 13245002074112178620173061)
                    ·
                      refine ⟨2483437888896033491282449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13245002074112178620173061 2483437888896033491282449)
                      ·
                        rfl

theorem cell23_4836478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4836478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836478 prefixEnd_4836478 := by exact prefixLift 4836478
  have htrace : WordTrace (prefixWord ++ tailWord_4836478) baseStart_4836478 baseEnd_4836478 := by
    simpa [prefixWord, tailWord_4836478, baseEnd_4836478] using wordTrace_append hprefix tailTrace_4836478
  have hstable : (prefixWord ++ tailWord_4836478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836478).length < 2 ^ (prefixWord ++ tailWord_4836478).sum := by decide
  have hdescent : baseEnd_4836478 < baseStart_4836478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836481 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_4836481 : Nat := 118140960795 + 4836481 * 2 ^ 59
def prefixEnd_4836481 : Nat := 4983230072969 + 3 ^ 40 * 4836481 * 2
def baseEnd_4836481 : Nat := 2483439429337996979544935

theorem tailTrace_4836481 : CollatzResearch.WordTrace tailWord_4836481 prefixEnd_4836481 2483439429337996979544935 := by
  unfold tailWord_4836481
  simp only [CollatzResearch.WordTrace]
  refine ⟨176400953991262817038277297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117600635994175211358851531 176400953991262817038277297)
  ·
    refine ⟨132300715493447112778707973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176400953991262817038277297 132300715493447112778707973)
    ·
      refine ⟨24806384155021333646007745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132300715493447112778707973 24806384155021333646007745)
      ·
        refine ⟨18604788116266000234505809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24806384155021333646007745 18604788116266000234505809)
        ·
          refine ⟨13953591087199500175879357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18604788116266000234505809 13953591087199500175879357)
          ·
            refine ⟨5232596657699812565954759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13953591087199500175879357 5232596657699812565954759)
            ·
              refine ⟨7848894986549718848932139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5232596657699812565954759 7848894986549718848932139)
              ·
                refine ⟨11773342479824578273398209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7848894986549718848932139 11773342479824578273398209)
                ·
                  refine ⟨8830006859868433705048657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11773342479824578273398209 8830006859868433705048657)
                  ·
                    refine ⟨6622505144901325278786493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8830006859868433705048657 6622505144901325278786493)
                    ·
                      refine ⟨2483439429337996979544935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6622505144901325278786493 2483439429337996979544935)
                      ·
                        rfl

theorem cell23_4836481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_4836481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836481 prefixEnd_4836481 := by exact prefixLift 4836481
  have htrace : WordTrace (prefixWord ++ tailWord_4836481) baseStart_4836481 baseEnd_4836481 := by
    simpa [prefixWord, tailWord_4836481, baseEnd_4836481] using wordTrace_append hprefix tailTrace_4836481
  have hstable : (prefixWord ++ tailWord_4836481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836481).length < 2 ^ (prefixWord ++ tailWord_4836481).sum := by decide
  have hdescent : baseEnd_4836481 < baseStart_4836481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836488 : List Nat := [2, 1, 3, 4, 2, 1, 2, 3, 1, 4]
def baseStart_4836488 : Nat := 118140960795 + 4836488 * 2 ^ 59
def prefixEnd_4836488 : Nat := 4983230072969 + 3 ^ 40 * 4836488 * 2
def baseEnd_4836488 : Nat := 827814341234192817385801

theorem tailTrace_4836488 : CollatzResearch.WordTrace tailWord_4836488 prefixEnd_4836488 827814341234192817385801 := by
  unfold tailWord_4836488
  simp only [CollatzResearch.WordTrace]
  refine ⟨88200604651118728616891059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117600806201491638155854745 88200604651118728616891059)
  ·
    refine ⟨132300906976678092925336589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88200604651118728616891059 132300906976678092925336589)
    ·
      refine ⟨49612840116254284847001221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132300906976678092925336589 49612840116254284847001221)
      ·
        refine ⟨9302407521797678408812729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49612840116254284847001221 9302407521797678408812729)
        ·
          refine ⟨6976805641348258806609547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9302407521797678408812729 6976805641348258806609547)
          ·
            refine ⟨10465208462022388209914321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6976805641348258806609547 10465208462022388209914321)
            ·
              refine ⟨7848906346516791157435741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10465208462022388209914321 7848906346516791157435741)
              ·
                refine ⟨2943339879943796684038403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7848906346516791157435741 2943339879943796684038403)
                ·
                  refine ⟨4415009819915695026057605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943339879943796684038403 4415009819915695026057605)
                  ·
                    refine ⟨827814341234192817385801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4415009819915695026057605 827814341234192817385801)
                    ·
                      rfl

theorem cell23_4836488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_4836488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836488 prefixEnd_4836488 := by exact prefixLift 4836488
  have htrace : WordTrace (prefixWord ++ tailWord_4836488) baseStart_4836488 baseEnd_4836488 := by
    simpa [prefixWord, tailWord_4836488, baseEnd_4836488] using wordTrace_append hprefix tailTrace_4836488
  have hstable : (prefixWord ++ tailWord_4836488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836488).length < 2 ^ (prefixWord ++ tailWord_4836488).sum := by decide
  have hdescent : baseEnd_4836488 < baseStart_4836488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836527 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 1, 6]
def baseStart_4836527 : Nat := 118140960795 + 4836527 * 2 ^ 59
def prefixEnd_4836527 : Nat := 4983230072969 + 3 ^ 40 * 4836527 * 2
def baseEnd_4836527 : Nat := 827821016482701266523241

theorem tailTrace_4836527 : CollatzResearch.WordTrace tailWord_4836527 prefixEnd_4836527 827821016482701266523241 := by
  unfold tailWord_4836527
  simp only [CollatzResearch.WordTrace]
  refine ⟨176402631749096166894451835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117601754499397444596301223 176402631749096166894451835)
  ·
    refine ⟨264603947623644250341677753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176402631749096166894451835 264603947623644250341677753)
    ·
      refine ⟨198452960717733187756258315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264603947623644250341677753 198452960717733187756258315)
      ·
        refine ⟨297679441076599781634387473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198452960717733187756258315 297679441076599781634387473)
        ·
          refine ⟨223259580807449836225790605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297679441076599781634387473 223259580807449836225790605)
          ·
            refine ⟨83722342802793688584671477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223259580807449836225790605 83722342802793688584671477)
            ·
              refine ⟨7848969637761908304812951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83722342802793688584671477 7848969637761908304812951)
              ·
                refine ⟨11773454456642862457219427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7848969637761908304812951 11773454456642862457219427)
                ·
                  refine ⟨17660181684964293685829141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11773454456642862457219427 17660181684964293685829141)
                  ·
                    refine ⟨827821016482701266523241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17660181684964293685829141 827821016482701266523241)
                    ·
                      rfl

theorem cell23_4836527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 6].length) (baseStart_4836527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836527 prefixEnd_4836527 := by exact prefixLift 4836527
  have htrace : WordTrace (prefixWord ++ tailWord_4836527) baseStart_4836527 baseEnd_4836527 := by
    simpa [prefixWord, tailWord_4836527, baseEnd_4836527] using wordTrace_append hprefix tailTrace_4836527
  have hstable : (prefixWord ++ tailWord_4836527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836527).length < 2 ^ (prefixWord ++ tailWord_4836527).sum := by decide
  have hdescent : baseEnd_4836527 < baseStart_4836527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836545 : List Nat := [1, 2, 6, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_4836545 : Nat := 118140960795 + 4836545 * 2 ^ 59
def prefixEnd_4836545 : Nat := 4983230072969 + 3 ^ 40 * 4836545 * 2
def baseEnd_4836545 : Nat := 2483472292099884729144641

theorem tailTrace_4836545 : CollatzResearch.WordTrace tailWord_4836545 prefixEnd_4836545 2483472292099884729144641 := by
  unfold tailWord_4836545
  simp only [CollatzResearch.WordTrace]
  refine ⟨176403288263030955968607089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117602192175353970645738059 176403288263030955968607089)
  ·
    refine ⟨132302466197273216976455317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176403288263030955968607089 132302466197273216976455317)
    ·
      refine ⟨6201678102997182045771343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132302466197273216976455317 6201678102997182045771343)
      ·
        refine ⟨9302517154495773068657015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6201678102997182045771343 9302517154495773068657015)
        ·
          refine ⟨13953775731743659602985523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9302517154495773068657015 13953775731743659602985523)
          ·
            refine ⟨20930663597615489404478285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13953775731743659602985523 20930663597615489404478285)
            ·
              refine ⟨7848998849105808526679357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20930663597615489404478285 7848998849105808526679357)
              ·
                refine ⟨2943374568414678197504759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7848998849105808526679357 2943374568414678197504759)
                ·
                  refine ⟨4415061852622017296257139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943374568414678197504759 4415061852622017296257139)
                  ·
                    refine ⟨6622592778933025944385709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4415061852622017296257139 6622592778933025944385709)
                    ·
                      refine ⟨2483472292099884729144641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6622592778933025944385709 2483472292099884729144641)
                      ·
                        rfl

theorem cell23_4836545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_4836545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836545 prefixEnd_4836545 := by exact prefixLift 4836545
  have htrace : WordTrace (prefixWord ++ tailWord_4836545) baseStart_4836545 baseEnd_4836545 := by
    simpa [prefixWord, tailWord_4836545, baseEnd_4836545] using wordTrace_append hprefix tailTrace_4836545
  have hstable : (prefixWord ++ tailWord_4836545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836545).length < 2 ^ (prefixWord ++ tailWord_4836545).sum := by decide
  have hdescent : baseEnd_4836545 < baseStart_4836545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836554 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_4836554 : Nat := 118140960795 + 4836554 * 2 ^ 59
def prefixEnd_4836554 : Nat := 4983230072969 + 3 ^ 40 * 4836554 * 2
def baseEnd_4836554 : Nat := 2483476913425775193932099

theorem tailTrace_4836554 : CollatzResearch.WordTrace tailWord_4836554 prefixEnd_4836554 2483476913425775193932099 := by
  unfold tailWord_4836554
  simp only [CollatzResearch.WordTrace]
  refine ⟨44100904129999587626421179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117602411013332233670456477 44100904129999587626421179)
  ·
    refine ⟨66151356194999381439631769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44100904129999587626421179 66151356194999381439631769)
    ·
      refine ⟨49613517146249536079723827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66151356194999381439631769 49613517146249536079723827)
      ·
        refine ⟨74420275719374304119585741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49613517146249536079723827 74420275719374304119585741)
        ·
          refine ⟨27907603394765364044844653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74420275719374304119585741 27907603394765364044844653)
          ·
            refine ⟨10465351273037011516816745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27907603394765364044844653 10465351273037011516816745)
            ·
              refine ⟨7849013454777758637612559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10465351273037011516816745 7849013454777758637612559)
              ·
                refine ⟨11773520182166637956418839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7849013454777758637612559 11773520182166637956418839)
                ·
                  refine ⟨17660280273249956934628259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11773520182166637956418839 17660280273249956934628259)
                  ·
                    refine ⟨26490420409874935401942389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17660280273249956934628259 26490420409874935401942389)
                    ·
                      refine ⟨2483476913425775193932099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26490420409874935401942389 2483476913425775193932099)
                      ·
                        rfl

theorem cell23_4836554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_4836554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836554 prefixEnd_4836554 := by exact prefixLift 4836554
  have htrace : WordTrace (prefixWord ++ tailWord_4836554) baseStart_4836554 baseEnd_4836554 := by
    simpa [prefixWord, tailWord_4836554, baseEnd_4836554] using wordTrace_append hprefix tailTrace_4836554
  have hstable : (prefixWord ++ tailWord_4836554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836554).length < 2 ^ (prefixWord ++ tailWord_4836554).sum := by decide
  have hdescent : baseEnd_4836554 < baseStart_4836554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836584 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_4836584 : Nat := 118140960795 + 4836584 * 2 ^ 59
def prefixEnd_4836584 : Nat := 4983230072969 + 3 ^ 40 * 4836584 * 2
def baseEnd_4836584 : Nat := 2483492317845410076556961

theorem tailTrace_4836584 : CollatzResearch.WordTrace tailWord_4836584 prefixEnd_4836584 2483492317845410076556961 := by
  unfold tailWord_4836584
  simp only [CollatzResearch.WordTrace]
  refine ⟨88202355354944832814638403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117603140473259777086184537 88202355354944832814638403)
  ·
    refine ⟨132303533032417249221957605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88202355354944832814638403 132303533032417249221957605)
    ·
      refine ⟨24806912443578234229117051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132303533032417249221957605 24806912443578234229117051)
      ·
        refine ⟨37210368665367351343675577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24806912443578234229117051 37210368665367351343675577)
        ·
          refine ⟨27907776499025513507756683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37210368665367351343675577 27907776499025513507756683)
          ·
            refine ⟨41861664748538270261635025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27907776499025513507756683 41861664748538270261635025)
            ·
              refine ⟨31396248561403702696226269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41861664748538270261635025 31396248561403702696226269)
              ·
                refine ⟨11773593210526388511084851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31396248561403702696226269 11773593210526388511084851)
                ·
                  refine ⟨17660389815789582766627277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11773593210526388511084851 17660389815789582766627277)
                  ·
                    refine ⟨6622646180921093537485229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17660389815789582766627277 6622646180921093537485229)
                    ·
                      refine ⟨2483492317845410076556961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6622646180921093537485229 2483492317845410076556961)
                      ·
                        rfl

theorem cell23_4836584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_4836584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836584 prefixEnd_4836584 := by exact prefixLift 4836584
  have htrace : WordTrace (prefixWord ++ tailWord_4836584) baseStart_4836584 baseEnd_4836584 := by
    simpa [prefixWord, tailWord_4836584, baseEnd_4836584] using wordTrace_append hprefix tailTrace_4836584
  have hstable : (prefixWord ++ tailWord_4836584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836584).length < 2 ^ (prefixWord ++ tailWord_4836584).sum := by decide
  have hdescent : baseEnd_4836584 < baseStart_4836584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836617 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 2, 6]
def baseStart_4836617 : Nat := 118140960795 + 4836617 * 2 ^ 59
def prefixEnd_4836617 : Nat := 4983230072969 + 3 ^ 40 * 4836617 * 2
def baseEnd_4836617 : Nat := 827836420902336149148103

theorem tailTrace_4836617 : CollatzResearch.WordTrace tailWord_4836617 prefixEnd_4836617 827836420902336149148103 := by
  unfold tailWord_4836617
  simp only [CollatzResearch.WordTrace]
  refine ⟨176405914318770112265228105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117603942879180074843485403 176405914318770112265228105)
  ·
    refine ⟨132304435739077584198921079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176405914318770112265228105 132304435739077584198921079)
    ·
      refine ⟨198456653608616376298381619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132304435739077584198921079 198456653608616376298381619)
      ·
        refine ⟨297684980412924564447572429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198456653608616376298381619 297684980412924564447572429)
        ·
          refine ⟨111631867654846711667839661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297684980412924564447572429 111631867654846711667839661)
          ·
            refine ⟨41861950370567516875439873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111631867654846711667839661 41861950370567516875439873)
            ·
              refine ⟨31396462777925637656579905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41861950370567516875439873 31396462777925637656579905)
              ·
                refine ⟨23547347083444228242434929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31396462777925637656579905 23547347083444228242434929)
                ·
                  refine ⟨17660510312583171181826197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23547347083444228242434929 17660510312583171181826197)
                  ·
                    refine ⟨827836420902336149148103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17660510312583171181826197 827836420902336149148103)
                    ·
                      rfl

theorem cell23_4836617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_4836617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836617 prefixEnd_4836617 := by exact prefixLift 4836617
  have htrace : WordTrace (prefixWord ++ tailWord_4836617) baseStart_4836617 baseEnd_4836617 := by
    simpa [prefixWord, tailWord_4836617, baseEnd_4836617] using wordTrace_append hprefix tailTrace_4836617
  have hstable : (prefixWord ++ tailWord_4836617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836617).length < 2 ^ (prefixWord ++ tailWord_4836617).sum := by decide
  have hdescent : baseEnd_4836617 < baseStart_4836617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836634 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_4836634 : Nat := 118140960795 + 4836634 * 2 ^ 59
def prefixEnd_4836634 : Nat := 4983230072969 + 3 ^ 40 * 4836634 * 2
def baseEnd_4836634 : Nat := 827839330626044960310577

theorem tailTrace_4836634 : CollatzResearch.WordTrace tailWord_4836634 prefixEnd_4836634 827839330626044960310577 := by
  unfold tailWord_4836634
  simp only [CollatzResearch.WordTrace]
  refine ⟨44101633589927131042149239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117604356239805682779064637 44101633589927131042149239)
  ·
    refine ⟨66152450384890696563223859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44101633589927131042149239 66152450384890696563223859)
    ·
      refine ⟨99228675577336044844835789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66152450384890696563223859 99228675577336044844835789)
      ·
        refine ⟨37210753341501016816813421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99228675577336044844835789 37210753341501016816813421)
        ·
          refine ⟨13954032503062881306305033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37210753341501016816813421 13954032503062881306305033)
          ·
            refine ⟨10465524377297160979728775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13954032503062881306305033 10465524377297160979728775)
            ·
              refine ⟨15698286565945741469593163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10465524377297160979728775 15698286565945741469593163)
              ·
                refine ⟨23547429848918612204389745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15698286565945741469593163 23547429848918612204389745)
                ·
                  refine ⟨17660572386688959153292309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23547429848918612204389745 17660572386688959153292309)
                  ·
                    refine ⟨827839330626044960310577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17660572386688959153292309 827839330626044960310577)
                    ·
                      rfl

theorem cell23_4836634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_4836634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836634 prefixEnd_4836634 := by exact prefixLift 4836634
  have htrace : WordTrace (prefixWord ++ tailWord_4836634) baseStart_4836634 baseEnd_4836634 := by
    simpa [prefixWord, tailWord_4836634, baseEnd_4836634] using wordTrace_append hprefix tailTrace_4836634
  have hstable : (prefixWord ++ tailWord_4836634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836634).length < 2 ^ (prefixWord ++ tailWord_4836634).sum := by decide
  have hdescent : baseEnd_4836634 < baseStart_4836634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836641 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 6, 2, 2]
def baseStart_4836641 : Nat := 118140960795 + 4836641 * 2 ^ 59
def prefixEnd_4836641 : Nat := 4983230072969 + 3 ^ 40 * 4836641 * 2
def baseEnd_4836641 : Nat := 2483521586242716353544199

theorem tailTrace_4836641 : CollatzResearch.WordTrace tailWord_4836641 prefixEnd_4836641 2483521586242716353544199 := by
  unfold tailWord_4836641
  simp only [CollatzResearch.WordTrace]
  refine ⟨176406789670683164364101777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117604526447122109576067851 176406789670683164364101777)
  ·
    refine ⟨132305092253012373273076333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176406789670683164364101777 132305092253012373273076333)
    ·
      refine ⟨49614409594879639977403625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132305092253012373273076333 49614409594879639977403625)
      ·
        refine ⟨37210807196159729983052719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49614409594879639977403625 37210807196159729983052719)
        ·
          refine ⟨55816210794239594974579079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37210807196159729983052719 55816210794239594974579079)
          ·
            refine ⟨83724316191359392461868619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55816210794239594974579079 83724316191359392461868619)
            ·
              refine ⟨125586474287039088692802929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83724316191359392461868619 125586474287039088692802929)
              ·
                refine ⟨94189855715279316519602197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125586474287039088692802929 94189855715279316519602197)
                ·
                  refine ⟨4415149486653717961856353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94189855715279316519602197 4415149486653717961856353)
                  ·
                    refine ⟨3311362114990288471392265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4415149486653717961856353 3311362114990288471392265)
                    ·
                      refine ⟨2483521586242716353544199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311362114990288471392265 2483521586242716353544199)
                      ·
                        rfl

theorem cell23_4836641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_4836641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836641 prefixEnd_4836641 := by exact prefixLift 4836641
  have htrace : WordTrace (prefixWord ++ tailWord_4836641) baseStart_4836641 baseEnd_4836641 := by
    simpa [prefixWord, tailWord_4836641, baseEnd_4836641] using wordTrace_append hprefix tailTrace_4836641
  have hstable : (prefixWord ++ tailWord_4836641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836641).length < 2 ^ (prefixWord ++ tailWord_4836641).sum := by decide
  have hdescent : baseEnd_4836641 < baseStart_4836641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836644 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_4836644 : Nat := 118140960795 + 4836644 * 2 ^ 59
def prefixEnd_4836644 : Nat := 4983230072969 + 3 ^ 40 * 4836644 * 2
def baseEnd_4836644 : Nat := 2483523126684679841806685

theorem tailTrace_4836644 : CollatzResearch.WordTrace tailWord_4836644 prefixEnd_4836644 2483523126684679841806685 := by
  unfold tailWord_4836644
  simp only [CollatzResearch.WordTrace]
  refine ⟨88203449544836147938230493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117604599393114863917640657 88203449544836147938230493)
  ·
    refine ⟨33076293579313555476836435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88203449544836147938230493 33076293579313555476836435)
    ·
      refine ⟨49614440368970333215254653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33076293579313555476836435 49614440368970333215254653)
      ·
        refine ⟨18605415138363874955720495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49614440368970333215254653 18605415138363874955720495)
        ·
          refine ⟨27908122707545812433580743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18605415138363874955720495 27908122707545812433580743)
          ·
            refine ⟨41862184061318718650371115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27908122707545812433580743 41862184061318718650371115)
            ·
              refine ⟨62793276091978077975556673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41862184061318718650371115 62793276091978077975556673)
              ·
                refine ⟨47094957068983558481667505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62793276091978077975556673 47094957068983558481667505)
                ·
                  refine ⟨35321217801737668861250629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47094957068983558481667505 35321217801737668861250629)
                  ·
                    refine ⟨6622728337825812911484493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35321217801737668861250629 6622728337825812911484493)
                    ·
                      refine ⟨2483523126684679841806685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6622728337825812911484493 2483523126684679841806685)
                      ·
                        rfl

theorem cell23_4836644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_4836644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836644 prefixEnd_4836644 := by exact prefixLift 4836644
  have htrace : WordTrace (prefixWord ++ tailWord_4836644) baseStart_4836644 baseEnd_4836644 := by
    simpa [prefixWord, tailWord_4836644, baseEnd_4836644] using wordTrace_append hprefix tailTrace_4836644
  have hstable : (prefixWord ++ tailWord_4836644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836644).length < 2 ^ (prefixWord ++ tailWord_4836644).sum := by decide
  have hdescent : baseEnd_4836644 < baseStart_4836644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836662 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4836662 : Nat := 118140960795 + 4836662 * 2 ^ 59
def prefixEnd_4836662 : Nat := 4983230072969 + 3 ^ 40 * 4836662 * 2
def baseEnd_4836662 : Nat := 2483532369336460771381603

theorem tailTrace_4836662 : CollatzResearch.WordTrace tailWord_4836662 prefixEnd_4836662 2483532369336460771381603 := by
  unfold tailWord_4836662
  simp only [CollatzResearch.WordTrace]
  refine ⟨11025472225225442809413515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117605037069071389967077493 11025472225225442809413515)
  ·
    refine ⟨16538208337838164214120273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11025472225225442809413515 16538208337838164214120273)
    ·
      refine ⟨12403656253378623160590205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16538208337838164214120273 12403656253378623160590205)
      ·
        refine ⟨4651371095016983685221327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12403656253378623160590205 4651371095016983685221327)
        ·
          refine ⟨6977056642525475527831991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651371095016983685221327 6977056642525475527831991)
          ·
            refine ⟨10465584963788213291747987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6977056642525475527831991 10465584963788213291747987)
            ·
              refine ⟨15698377445682319937621981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10465584963788213291747987 15698377445682319937621981)
              ·
                refine ⟨5886891542130869976608243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15698377445682319937621981 5886891542130869976608243)
                ·
                  refine ⟨8830337313196304964912365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5886891542130869976608243 8830337313196304964912365)
                  ·
                    refine ⟨3311376492448614361842137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8830337313196304964912365 3311376492448614361842137)
                    ·
                      refine ⟨2483532369336460771381603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311376492448614361842137 2483532369336460771381603)
                      ·
                        rfl

theorem cell23_4836662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4836662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836662 prefixEnd_4836662 := by exact prefixLift 4836662
  have htrace : WordTrace (prefixWord ++ tailWord_4836662) baseStart_4836662 baseEnd_4836662 := by
    simpa [prefixWord, tailWord_4836662, baseEnd_4836662] using wordTrace_append hprefix tailTrace_4836662
  have hstable : (prefixWord ++ tailWord_4836662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836662).length < 2 ^ (prefixWord ++ tailWord_4836662).sum := by decide
  have hdescent : baseEnd_4836662 < baseStart_4836662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836687 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_4836687 : Nat := 118140960795 + 4836687 * 2 ^ 59
def prefixEnd_4836687 : Nat := 4983230072969 + 3 ^ 40 * 4836687 * 2
def baseEnd_4836687 : Nat := 2483545206352823173568987

theorem tailTrace_4836687 : CollatzResearch.WordTrace tailWord_4836687 prefixEnd_4836687 2483545206352823173568987 := by
  unfold tailWord_4836687
  simp only [CollatzResearch.WordTrace]
  refine ⟨176408467428516514220276315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117605644952344342813517543 176408467428516514220276315)
  ·
    refine ⟨264612701142774771330414473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176408467428516514220276315 264612701142774771330414473)
    ·
      refine ⟨198459525857081078497810855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264612701142774771330414473 198459525857081078497810855)
      ·
        refine ⟨297689288785621617746716283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198459525857081078497810855 297689288785621617746716283)
        ·
          refine ⟨446533933178432426620074425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297689288785621617746716283 446533933178432426620074425)
          ·
            refine ⟨334900449883824319965055819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446533933178432426620074425 334900449883824319965055819)
            ·
              refine ⟨502350674825736479947583729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334900449883824319965055819 502350674825736479947583729)
              ·
                refine ⟨376763006119302359960687797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502350674825736479947583729 376763006119302359960687797)
                ·
                  refine ⟨35321531823684596246314481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 376763006119302359960687797 35321531823684596246314481)
                  ·
                    refine ⟨26491148867763447184735861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35321531823684596246314481 26491148867763447184735861)
                    ·
                      refine ⟨2483545206352823173568987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26491148867763447184735861 2483545206352823173568987)
                      ·
                        rfl

theorem cell23_4836687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_4836687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836687 prefixEnd_4836687 := by exact prefixLift 4836687
  have htrace : WordTrace (prefixWord ++ tailWord_4836687) baseStart_4836687 baseEnd_4836687 := by
    simpa [prefixWord, tailWord_4836687, baseEnd_4836687] using wordTrace_append hprefix tailTrace_4836687
  have hstable : (prefixWord ++ tailWord_4836687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836687).length < 2 ^ (prefixWord ++ tailWord_4836687).sum := by decide
  have hdescent : baseEnd_4836687 < baseStart_4836687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836738 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_4836738 : Nat := 118140960795 + 4836738 * 2 ^ 59
def prefixEnd_4836738 : Nat := 4983230072969 + 3 ^ 40 * 4836738 * 2
def baseEnd_4836738 : Nat := 2483571393866202474031253

theorem tailTrace_4836738 : CollatzResearch.WordTrace tailWord_4836738 prefixEnd_4836738 2483571393866202474031253 := by
  unfold tailWord_4836738
  simp only [CollatzResearch.WordTrace]
  refine ⟨44102581887832937482595717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117606885034221166620255245 44102581887832937482595717)
  ·
    refine ⟨8269234103968675777986697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44102581887832937482595717 8269234103968675777986697)
    ·
      refine ⟨6201925577976506833490023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8269234103968675777986697 6201925577976506833490023)
      ·
        refine ⟨9302888366964760250235035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6201925577976506833490023 9302888366964760250235035)
        ·
          refine ⟨13954332550447140375352553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9302888366964760250235035 13954332550447140375352553)
          ·
            refine ⟨10465749412835355281514415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13954332550447140375352553 10465749412835355281514415)
            ·
              refine ⟨15698624119253032922271623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10465749412835355281514415 15698624119253032922271623)
              ·
                refine ⟨23547936178879549383407435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15698624119253032922271623 23547936178879549383407435)
                ·
                  refine ⟨35321904268319324075111153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23547936178879549383407435 35321904268319324075111153)
                  ·
                    refine ⟨26491428201239493056333365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35321904268319324075111153 26491428201239493056333365)
                    ·
                      refine ⟨2483571393866202474031253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26491428201239493056333365 2483571393866202474031253)
                      ·
                        rfl

theorem cell23_4836738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_4836738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836738 prefixEnd_4836738 := by exact prefixLift 4836738
  have htrace : WordTrace (prefixWord ++ tailWord_4836738) baseStart_4836738 baseEnd_4836738 := by
    simpa [prefixWord, tailWord_4836738, baseEnd_4836738] using wordTrace_append hprefix tailTrace_4836738
  have hstable : (prefixWord ++ tailWord_4836738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836738).length < 2 ^ (prefixWord ++ tailWord_4836738).sum := by decide
  have hdescent : baseEnd_4836738 < baseStart_4836738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836741 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 3, 4]
def baseStart_4836741 : Nat := 118140960795 + 4836741 * 2 ^ 59
def prefixEnd_4836741 : Nat := 4983230072969 + 3 ^ 40 * 4836741 * 2
def baseEnd_4836741 : Nat := 827857644769388654097913

theorem tailTrace_4836741 : CollatzResearch.WordTrace tailWord_4836741 prefixEnd_4836741 827857644769388654097913 := by
  unfold tailWord_4836741
  simp only [CollatzResearch.WordTrace]
  refine ⟨176410436970320881442742077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117606957980213920961828051 176410436970320881442742077)
  ·
    refine ⟨66153913863870330541028279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176410436970320881442742077 66153913863870330541028279)
    ·
      refine ⟨99230870795805495811542419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66153913863870330541028279 99230870795805495811542419)
      ·
        refine ⟨148846306193708243717313629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99230870795805495811542419 148846306193708243717313629)
        ·
          refine ⟨55817364822640591393992611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148846306193708243717313629 55817364822640591393992611)
          ·
            refine ⟨83726047233960887090988917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55817364822640591393992611 83726047233960887090988917)
            ·
              refine ⟨7849316928183833164780211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83726047233960887090988917 7849316928183833164780211)
              ·
                refine ⟨11773975392275749747170317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7849316928183833164780211 11773975392275749747170317)
                ·
                  refine ⟨4415240772103406155188869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11773975392275749747170317 4415240772103406155188869)
                  ·
                    refine ⟨827857644769388654097913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4415240772103406155188869 827857644769388654097913)
                    ·
                      rfl

theorem cell23_4836741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_4836741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836741 prefixEnd_4836741 := by exact prefixLift 4836741
  have htrace : WordTrace (prefixWord ++ tailWord_4836741) baseStart_4836741 baseEnd_4836741 := by
    simpa [prefixWord, tailWord_4836741, baseEnd_4836741] using wordTrace_append hprefix tailTrace_4836741
  have hstable : (prefixWord ++ tailWord_4836741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836741).length < 2 ^ (prefixWord ++ tailWord_4836741).sum := by decide
  have hdescent : baseEnd_4836741 < baseStart_4836741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836798 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_4836798 : Nat := 118140960795 + 4836798 * 2 ^ 59
def prefixEnd_4836798 : Nat := 4983230072969 + 3 ^ 40 * 4836798 * 2
def baseEnd_4836798 : Nat := 2483602202705472239280977

theorem tailTrace_4836798 : CollatzResearch.WordTrace tailWord_4836798 prefixEnd_4836798 2483602202705472239280977 := by
  unfold tailWord_4836798
  simp only [CollatzResearch.WordTrace]
  refine ⟨22051564491389297522195881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117608343954076253451711365 22051564491389297522195881)
  ·
    refine ⟨16538673368541973141646911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22051564491389297522195881 16538673368541973141646911)
    ·
      refine ⟨24808010052812959712470367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16538673368541973141646911 24808010052812959712470367)
      ·
        refine ⟨37212015079219439568705551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24808010052812959712470367 37212015079219439568705551)
        ·
          refine ⟨55818022618829159353058327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37212015079219439568705551 55818022618829159353058327)
          ·
            refine ⟨83727033928243739029587491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55818022618829159353058327 83727033928243739029587491)
            ·
              refine ⟨125590550892365608544381237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83727033928243739029587491 125590550892365608544381237)
              ·
                refine ⟨11774114146159275801035741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125590550892365608544381237 11774114146159275801035741)
                ·
                  refine ⟨4415292804809728425388403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11774114146159275801035741 4415292804809728425388403)
                  ·
                    refine ⟨6622939207214592638082605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4415292804809728425388403 6622939207214592638082605)
                    ·
                      refine ⟨2483602202705472239280977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6622939207214592638082605 2483602202705472239280977)
                      ·
                        rfl

theorem cell23_4836798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_4836798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836798 prefixEnd_4836798 := by exact prefixLift 4836798
  have htrace : WordTrace (prefixWord ++ tailWord_4836798) baseStart_4836798 baseEnd_4836798 := by
    simpa [prefixWord, tailWord_4836798, baseEnd_4836798] using wordTrace_append hprefix tailTrace_4836798
  have hstable : (prefixWord ++ tailWord_4836798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836798).length < 2 ^ (prefixWord ++ tailWord_4836798).sum := by decide
  have hdescent : baseEnd_4836798 < baseStart_4836798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836821 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4836821 : Nat := 118140960795 + 4836821 * 2 ^ 59
def prefixEnd_4836821 : Nat := 4983230072969 + 3 ^ 40 * 4836821 * 2
def baseEnd_4836821 : Nat := 2483614012760525649293371

theorem tailTrace_4836821 : CollatzResearch.WordTrace tailWord_4836821 prefixEnd_4836821 2483614012760525649293371 := by
  unfold tailWord_4836821
  simp only [CollatzResearch.WordTrace]
  refine ⟨176413354810031055105654317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117608903206687370070436211 176413354810031055105654317)
  ·
    refine ⟨66155008053761645664620369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176413354810031055105654317 66155008053761645664620369)
    ·
      refine ⟨49616256040321234248465277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66155008053761645664620369 49616256040321234248465277)
      ·
        refine ⟨18606096015120462843174479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49616256040321234248465277 18606096015120462843174479)
        ·
          refine ⟨27909144022680694264761719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18606096015120462843174479 27909144022680694264761719)
          ·
            refine ⟨41863716034021041397142579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27909144022680694264761719 41863716034021041397142579)
            ·
              refine ⟨62795574051031562095713869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41863716034021041397142579 62795574051031562095713869)
              ·
                refine ⟨23548340269136835785892701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62795574051031562095713869 23548340269136835785892701)
                ·
                  refine ⟨8830627600926313419709763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23548340269136835785892701 8830627600926313419709763)
                  ·
                    refine ⟨13245941401389470129564645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8830627600926313419709763 13245941401389470129564645)
                    ·
                      refine ⟨2483614012760525649293371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13245941401389470129564645 2483614012760525649293371)
                      ·
                        rfl

theorem cell23_4836821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4836821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836821 prefixEnd_4836821 := by exact prefixLift 4836821
  have htrace : WordTrace (prefixWord ++ tailWord_4836821) baseStart_4836821 baseEnd_4836821 := by
    simpa [prefixWord, tailWord_4836821, baseEnd_4836821] using wordTrace_append hprefix tailTrace_4836821
  have hstable : (prefixWord ++ tailWord_4836821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836821).length < 2 ^ (prefixWord ++ tailWord_4836821).sum := by decide
  have hdescent : baseEnd_4836821 < baseStart_4836821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836825 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 2, 3, 2]
def baseStart_4836825 : Nat := 118140960795 + 4836825 * 2 ^ 59
def prefixEnd_4836825 : Nat := 4983230072969 + 3 ^ 40 * 4836825 * 2
def baseEnd_4836825 : Nat := 2483616066683143633643353

theorem tailTrace_4836825 : CollatzResearch.WordTrace tailWord_4836825 prefixEnd_4836825 2483616066683143633643353 := by
  unfold tailWord_4836825
  simp only [CollatzResearch.WordTrace]
  refine ⟨176413500702016563788799929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117609000468011042525866619 176413500702016563788799929)
  ·
    refine ⟨132310125526512422841599947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176413500702016563788799929 132310125526512422841599947)
    ·
      refine ⟨198465188289768634262399921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132310125526512422841599947 198465188289768634262399921)
      ·
        refine ⟨148848891217326475696799941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198465188289768634262399921 148848891217326475696799941)
        ·
          refine ⟨27909167103248714193149989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148848891217326475696799941 27909167103248714193149989)
          ·
            refine ⟨5232968831859133911215623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27909167103248714193149989 5232968831859133911215623)
            ·
              refine ⟨7849453247788700866823435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5232968831859133911215623 7849453247788700866823435)
              ·
                refine ⟨11774179871683051300235153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7849453247788700866823435 11774179871683051300235153)
                ·
                  refine ⟨8830634903762288475176365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11774179871683051300235153 8830634903762288475176365)
                  ·
                    refine ⟨3311488088910858178191137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8830634903762288475176365 3311488088910858178191137)
                    ·
                      refine ⟨2483616066683143633643353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311488088910858178191137 2483616066683143633643353)
                      ·
                        rfl

theorem cell23_4836825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 3, 2].length) (baseStart_4836825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836825 prefixEnd_4836825 := by exact prefixLift 4836825
  have htrace : WordTrace (prefixWord ++ tailWord_4836825) baseStart_4836825 baseEnd_4836825 := by
    simpa [prefixWord, tailWord_4836825, baseEnd_4836825] using wordTrace_append hprefix tailTrace_4836825
  have hstable : (prefixWord ++ tailWord_4836825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836825).length < 2 ^ (prefixWord ++ tailWord_4836825).sum := by decide
  have hdescent : baseEnd_4836825 < baseStart_4836825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836831 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 4, 4]
def baseStart_4836831 : Nat := 118140960795 + 4836831 * 2 ^ 59
def prefixEnd_4836831 : Nat := 4983230072969 + 3 ^ 40 * 4836831 * 2
def baseEnd_4836831 : Nat := 827873049189023536722775

theorem tailTrace_4836831 : CollatzResearch.WordTrace tailWord_4836831 prefixEnd_4836831 827873049189023536722775 := by
  unfold tailWord_4836831
  simp only [CollatzResearch.WordTrace]
  refine ⟨176413719539994826813518347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117609146359996551209012231 176413719539994826813518347)
  ·
    refine ⟨264620579309992240220277521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176413719539994826813518347 264620579309992240220277521)
    ·
      refine ⟨198465434482494180165208141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264620579309992240220277521 198465434482494180165208141)
      ·
        refine ⟨74424537930935317561953053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198465434482494180165208141 74424537930935317561953053)
        ·
          refine ⟨27909201724100744085732395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74424537930935317561953053 27909201724100744085732395)
          ·
            refine ⟨41863802586151116128598593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27909201724100744085732395 41863802586151116128598593)
            ·
              refine ⟨31397851939613337096448945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41863802586151116128598593 31397851939613337096448945)
              ·
                refine ⟨23548388954710002822336709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31397851939613337096448945 23548388954710002822336709)
                ·
                  refine ⟨4415322929008125529188133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23548388954710002822336709 4415322929008125529188133)
                  ·
                    refine ⟨827873049189023536722775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4415322929008125529188133 827873049189023536722775)
                    ·
                      rfl

theorem cell23_4836831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 4].length) (baseStart_4836831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836831 prefixEnd_4836831 := by exact prefixLift 4836831
  have htrace : WordTrace (prefixWord ++ tailWord_4836831) baseStart_4836831 baseEnd_4836831 := by
    simpa [prefixWord, tailWord_4836831, baseEnd_4836831] using wordTrace_append hprefix tailTrace_4836831
  have hstable : (prefixWord ++ tailWord_4836831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836831).length < 2 ^ (prefixWord ++ tailWord_4836831).sum := by decide
  have hdescent : baseEnd_4836831 < baseStart_4836831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836835 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 1, 5]
def baseStart_4836835 : Nat := 118140960795 + 4836835 * 2 ^ 59
def prefixEnd_4836835 : Nat := 4983230072969 + 3 ^ 40 * 4836835 * 2
def baseEnd_4836835 : Nat := 827873733829896198172769

theorem tailTrace_4836835 : CollatzResearch.WordTrace tailWord_4836835 prefixEnd_4836835 827873733829896198172769 := by
  unfold tailWord_4836835
  simp only [CollatzResearch.WordTrace]
  refine ⟨176413865431980335496663959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117609243621320223664442639 176413865431980335496663959)
  ·
    refine ⟨264620798147970503244995939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176413865431980335496663959 264620798147970503244995939)
    ·
      refine ⟨396931197221955754867493909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264620798147970503244995939 396931197221955754867493909)
      ·
        refine ⟨18606149869779176009413777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 396931197221955754867493909 18606149869779176009413777)
        ·
          refine ⟨13954612402334382007060333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18606149869779176009413777 13954612402334382007060333)
          ·
            refine ⟨5232979650875393252647625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13954612402334382007060333 5232979650875393252647625)
            ·
              refine ⟨3924734738156544939485719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5232979650875393252647625 3924734738156544939485719)
              ·
                refine ⟨5887102107234817409228579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3924734738156544939485719 5887102107234817409228579)
                ·
                  refine ⟨8830653160852226113842869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5887102107234817409228579 8830653160852226113842869)
                  ·
                    refine ⟨827873733829896198172769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8830653160852226113842869 827873733829896198172769)
                    ·
                      rfl

theorem cell23_4836835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 5].length) (baseStart_4836835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836835 prefixEnd_4836835 := by exact prefixLift 4836835
  have htrace : WordTrace (prefixWord ++ tailWord_4836835) baseStart_4836835 baseEnd_4836835 := by
    simpa [prefixWord, tailWord_4836835, baseEnd_4836835] using wordTrace_append hprefix tailTrace_4836835
  have hstable : (prefixWord ++ tailWord_4836835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836835).length < 2 ^ (prefixWord ++ tailWord_4836835).sum := by decide
  have hdescent : baseEnd_4836835 < baseStart_4836835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836848 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 2, 4]
def baseStart_4836848 : Nat := 118140960795 + 4836848 * 2 ^ 59
def prefixEnd_4836848 : Nat := 4983230072969 + 3 ^ 40 * 4836848 * 2
def baseEnd_4836848 : Nat := 827875958912732347885249

theorem tailTrace_4836848 : CollatzResearch.WordTrace tailWord_4836848 prefixEnd_4836848 827875958912732347885249 := by
  unfold tailWord_4836848
  simp only [CollatzResearch.WordTrace]
  refine ⟨88207169790466619358443599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117609559720622159144591465 88207169790466619358443599)
  ·
    refine ⟨132310754685699929037665399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88207169790466619358443599 132310754685699929037665399)
    ·
      refine ⟨198466132028549893556498099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132310754685699929037665399 198466132028549893556498099)
      ·
        refine ⟨297699198042824840334747149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198466132028549893556498099 297699198042824840334747149)
        ·
          refine ⟨111637199266059315125530181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297699198042824840334747149 111637199266059315125530181)
          ·
            refine ⟨20931974862386121586036909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111637199266059315125530181 20931974862386121586036909)
            ·
              refine ⟨7849490573394795594763841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20931974862386121586036909 7849490573394795594763841)
              ·
                refine ⟨5887117930046096696072881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7849490573394795594763841 5887117930046096696072881)
                ·
                  refine ⟨4415338447534572522054661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5887117930046096696072881 4415338447534572522054661)
                  ·
                    refine ⟨827875958912732347885249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4415338447534572522054661 827875958912732347885249)
                    ·
                      rfl

theorem cell23_4836848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2, 4].length) (baseStart_4836848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836848 prefixEnd_4836848 := by exact prefixLift 4836848
  have htrace : WordTrace (prefixWord ++ tailWord_4836848) baseStart_4836848 baseEnd_4836848 := by
    simpa [prefixWord, tailWord_4836848, baseEnd_4836848] using wordTrace_append hprefix tailTrace_4836848
  have hstable : (prefixWord ++ tailWord_4836848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836848).length < 2 ^ (prefixWord ++ tailWord_4836848).sum := by decide
  have hdescent : baseEnd_4836848 < baseStart_4836848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836865 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 1, 6]
def baseStart_4836865 : Nat := 118140960795 + 4836865 * 2 ^ 59
def prefixEnd_4836865 : Nat := 4983230072969 + 3 ^ 40 * 4836865 * 2
def baseEnd_4836865 : Nat := 827878868636441159047723

theorem tailTrace_4836865 : CollatzResearch.WordTrace tailWord_4836865 prefixEnd_4836865 827878868636441159047723 := by
  unfold tailWord_4836865
  simp only [CollatzResearch.WordTrace]
  refine ⟨176414959621871650620256049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117609973081247767080170699 176414959621871650620256049)
  ·
    refine ⟨132311219716403737965192037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176414959621871650620256049 132311219716403737965192037)
    ·
      refine ⟨24808353696825700868473507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132311219716403737965192037 24808353696825700868473507)
      ·
        refine ⟨37212530545238551302710261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24808353696825700868473507 37212530545238551302710261)
        ·
          refine ⟨3488674738616114184629087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37212530545238551302710261 3488674738616114184629087)
          ·
            refine ⟨5233012107924171276943631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3488674738616114184629087 5233012107924171276943631)
            ·
              refine ⟨7849518161886256915415447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5233012107924171276943631 7849518161886256915415447)
              ·
                refine ⟨11774277242829385373123171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7849518161886256915415447 11774277242829385373123171)
                ·
                  refine ⟨17661415864244078059684757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11774277242829385373123171 17661415864244078059684757)
                  ·
                    refine ⟨827878868636441159047723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17661415864244078059684757 827878868636441159047723)
                    ·
                      rfl

theorem cell23_4836865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_4836865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836865 prefixEnd_4836865 := by exact prefixLift 4836865
  have htrace : WordTrace (prefixWord ++ tailWord_4836865) baseStart_4836865 baseEnd_4836865 := by
    simpa [prefixWord, tailWord_4836865, baseEnd_4836865] using wordTrace_append hprefix tailTrace_4836865
  have hstable : (prefixWord ++ tailWord_4836865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836865).length < 2 ^ (prefixWord ++ tailWord_4836865).sum := by decide
  have hdescent : baseEnd_4836865 < baseStart_4836865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836868 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4836868 : Nat := 118140960795 + 4836868 * 2 ^ 59
def prefixEnd_4836868 : Nat := 4983230072969 + 3 ^ 40 * 4836868 * 2
def baseEnd_4836868 : Nat := 2483638146351286965405655

theorem tailTrace_4836868 : CollatzResearch.WordTrace tailWord_4836868 prefixEnd_4836868 2483638146351286965405655 := by
  unfold tailWord_4836868
  simp only [CollatzResearch.WordTrace]
  refine ⟨88207534520430391066307629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117610046027240521421743505 88207534520430391066307629)
  ·
    refine ⟨33077825445161396649865361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88207534520430391066307629 33077825445161396649865361)
    ·
      refine ⟨24808369083871047487399021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33077825445161396649865361 24808369083871047487399021)
      ·
        refine ⟨9303138406451642807774633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24808369083871047487399021 9303138406451642807774633)
        ·
          refine ⟨6977353804838732105830975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9303138406451642807774633 6977353804838732105830975)
          ·
            refine ⟨10466030707258098158746463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6977353804838732105830975 10466030707258098158746463)
            ·
              refine ⟨15699046060887147238119695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10466030707258098158746463 15699046060887147238119695)
              ·
                refine ⟨23548569091330720857179543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15699046060887147238119695 23548569091330720857179543)
                ·
                  refine ⟨35322853636996081285769315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23548569091330720857179543 35322853636996081285769315)
                  ·
                    refine ⟨52984280455494121928653973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35322853636996081285769315 52984280455494121928653973)
                    ·
                      refine ⟨2483638146351286965405655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52984280455494121928653973 2483638146351286965405655)
                      ·
                        rfl

theorem cell23_4836868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4836868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836868 prefixEnd_4836868 := by exact prefixLift 4836868
  have htrace : WordTrace (prefixWord ++ tailWord_4836868) baseStart_4836868 baseEnd_4836868 := by
    simpa [prefixWord, tailWord_4836868, baseEnd_4836868] using wordTrace_append hprefix tailTrace_4836868
  have hstable : (prefixWord ++ tailWord_4836868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836868).length < 2 ^ (prefixWord ++ tailWord_4836868).sum := by decide
  have hdescent : baseEnd_4836868 < baseStart_4836868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836875 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 1, 2, 3]
def baseStart_4836875 : Nat := 118140960795 + 4836875 * 2 ^ 59
def prefixEnd_4836875 : Nat := 4983230072969 + 3 ^ 40 * 4836875 * 2
def baseEnd_4836875 : Nat := 2483641740715868438018123

theorem tailTrace_4836875 : CollatzResearch.WordTrace tailWord_4836875 prefixEnd_4836875 2483641740715868438018123 := by
  unfold tailWord_4836875
  simp only [CollatzResearch.WordTrace]
  refine ⟨176415324351835422328120079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117610216234556948218746719 176415324351835422328120079)
  ·
    refine ⟨264622986527753133492180119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176415324351835422328120079 264622986527753133492180119)
    ·
      refine ⟨396934479791629700238270179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264622986527753133492180119 396934479791629700238270179)
      ·
        refine ⟨595401719687444550357405269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396934479791629700238270179 595401719687444550357405269)
        ·
          refine ⟨6977363902587240824500843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 595401719687444550357405269 6977363902587240824500843)
          ·
            refine ⟨10466045853880861236751265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6977363902587240824500843 10466045853880861236751265)
            ·
              refine ⟨7849534390410645927563449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10466045853880861236751265 7849534390410645927563449)
              ·
                refine ⟨5887150792807984445672587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7849534390410645927563449 5887150792807984445672587)
                ·
                  refine ⟨8830726189211976668508881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5887150792807984445672587 8830726189211976668508881)
                  ·
                    refine ⟨6623044641908982501381661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8830726189211976668508881 6623044641908982501381661)
                    ·
                      refine ⟨2483641740715868438018123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6623044641908982501381661 2483641740715868438018123)
                      ·
                        rfl

theorem cell23_4836875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 2, 3].length) (baseStart_4836875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836875 prefixEnd_4836875 := by exact prefixLift 4836875
  have htrace : WordTrace (prefixWord ++ tailWord_4836875) baseStart_4836875 baseEnd_4836875 := by
    simpa [prefixWord, tailWord_4836875, baseEnd_4836875] using wordTrace_append hprefix tailTrace_4836875
  have hstable : (prefixWord ++ tailWord_4836875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836875).length < 2 ^ (prefixWord ++ tailWord_4836875).sum := by decide
  have hdescent : baseEnd_4836875 < baseStart_4836875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836928 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 1, 4, 2]
def baseStart_4836928 : Nat := 118140960795 + 4836928 * 2 ^ 59
def prefixEnd_4836928 : Nat := 4983230072969 + 3 ^ 40 * 4836928 * 2
def baseEnd_4836928 : Nat := 2483668955190556730655379

theorem tailTrace_4836928 : CollatzResearch.WordTrace tailWord_4836928 prefixEnd_4836928 2483668955190556730655379 := by
  unfold tailWord_4836928
  simp only [CollatzResearch.WordTrace]
  refine ⟨88208628710321706189899719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117611504947095608253199625 88208628710321706189899719)
  ·
    refine ⟨132312943065482559284849579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88208628710321706189899719 132312943065482559284849579)
    ·
      refine ⟨198469414598223838927274369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132312943065482559284849579 198469414598223838927274369)
      ·
        refine ⟨148852060948667879195455777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198469414598223838927274369 148852060948667879195455777)
        ·
          refine ⟨111639045711500909396591833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148852060948667879195455777 111639045711500909396591833)
          ·
            refine ⟨83729284283625682047443875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111639045711500909396591833 83729284283625682047443875)
            ·
              refine ⟨125593926425438523071165813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83729284283625682047443875 125593926425438523071165813)
              ·
                refine ⟨11774430602384861537921795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125593926425438523071165813 11774430602384861537921795)
                ·
                  refine ⟨17661645903577292306882693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11774430602384861537921795 17661645903577292306882693)
                  ·
                    refine ⟨3311558606920742307540505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17661645903577292306882693 3311558606920742307540505)
                    ·
                      refine ⟨2483668955190556730655379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311558606920742307540505 2483668955190556730655379)
                      ·
                        rfl

theorem cell23_4836928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 4, 2].length) (baseStart_4836928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836928 prefixEnd_4836928 := by exact prefixLift 4836928
  have htrace : WordTrace (prefixWord ++ tailWord_4836928) baseStart_4836928 baseEnd_4836928 := by
    simpa [prefixWord, tailWord_4836928, baseEnd_4836928] using wordTrace_append hprefix tailTrace_4836928
  have hstable : (prefixWord ++ tailWord_4836928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836928).length < 2 ^ (prefixWord ++ tailWord_4836928).sum := by decide
  have hdescent : baseEnd_4836928 < baseStart_4836928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836978 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_4836978 : Nat := 118140960795 + 4836978 * 2 ^ 59
def prefixEnd_4836978 : Nat := 4983230072969 + 3 ^ 40 * 4836978 * 2
def baseEnd_4836978 : Nat := 2483694629223281535030149

theorem tailTrace_4836978 : CollatzResearch.WordTrace tailWord_4836978 prefixEnd_4836978 2483694629223281535030149 := by
  unfold tailWord_4836978
  simp only [CollatzResearch.WordTrace]
  refine ⟨44104770267615567729779897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117612720713641513946079725 44104770267615567729779897)
  ·
    refine ⟨33078577700711675797334923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44104770267615567729779897 33078577700711675797334923)
    ·
      refine ⟨49617866551067513696002385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33078577700711675797334923 49617866551067513696002385)
      ·
        refine ⟨37213399913300635272001789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49617866551067513696002385 37213399913300635272001789)
        ·
          refine ⟨13955024967487738227000671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37213399913300635272001789 13955024967487738227000671)
          ·
            refine ⟨20932537451231607340501007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13955024967487738227000671 20932537451231607340501007)
            ·
              refine ⟨31398806176847411010751511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20932537451231607340501007 31398806176847411010751511)
              ·
                refine ⟨47098209265271116516127267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31398806176847411010751511 47098209265271116516127267)
                ·
                  refine ⟨70647313897906674774190901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47098209265271116516127267 70647313897906674774190901)
                  ·
                    refine ⟨6623185677928750760080397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70647313897906674774190901 6623185677928750760080397)
                    ·
                      refine ⟨2483694629223281535030149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6623185677928750760080397 2483694629223281535030149)
                      ·
                        rfl

theorem cell23_4836978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_4836978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836978 prefixEnd_4836978 := by exact prefixLift 4836978
  have htrace : WordTrace (prefixWord ++ tailWord_4836978) baseStart_4836978 baseEnd_4836978 := by
    simpa [prefixWord, tailWord_4836978, baseEnd_4836978] using wordTrace_append hprefix tailTrace_4836978
  have hstable : (prefixWord ++ tailWord_4836978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836978).length < 2 ^ (prefixWord ++ tailWord_4836978).sum := by decide
  have hdescent : baseEnd_4836978 < baseStart_4836978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4836988 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 4, 5, 2]
def baseStart_4836988 : Nat := 118140960795 + 4836988 * 2 ^ 59
def prefixEnd_4836988 : Nat := 4983230072969 + 3 ^ 40 * 4836988 * 2
def baseEnd_4836988 : Nat := 2483699764029826495905103

theorem tailTrace_4836988 : CollatzResearch.WordTrace tailWord_4836988 prefixEnd_4836988 2483699764029826495905103 := by
  unfold tailWord_4836988
  simp only [CollatzResearch.WordTrace]
  refine ⟨88209722900213021313491809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117612963866950695084655745 88209722900213021313491809)
  ·
    refine ⟨66157292175159765985118857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88209722900213021313491809 66157292175159765985118857)
    ·
      refine ⟨49617969131369824488839143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66157292175159765985118857 49617969131369824488839143)
      ·
        refine ⟨74426953697054736733258715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49617969131369824488839143 74426953697054736733258715)
        ·
          refine ⟨111640430545582105099888073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74426953697054736733258715 111640430545582105099888073)
          ·
            refine ⟨83730322909186578824916055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111640430545582105099888073 83730322909186578824916055)
            ·
              refine ⟨125595484363779868237374083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83730322909186578824916055 125595484363779868237374083)
              ·
                refine ⟨188393226545669802356061125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125595484363779868237374083 188393226545669802356061125)
                ·
                  refine ⟨35323729977313087941761461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188393226545669802356061125 35323729977313087941761461)
                  ·
                    refine ⟨3311599685373101994540137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35323729977313087941761461 3311599685373101994540137)
                    ·
                      refine ⟨2483699764029826495905103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311599685373101994540137 2483699764029826495905103)
                      ·
                        rfl

theorem cell23_4836988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_4836988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4836988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4836988 prefixEnd_4836988 := by exact prefixLift 4836988
  have htrace : WordTrace (prefixWord ++ tailWord_4836988) baseStart_4836988 baseEnd_4836988 := by
    simpa [prefixWord, tailWord_4836988, baseEnd_4836988] using wordTrace_append hprefix tailTrace_4836988
  have hstable : (prefixWord ++ tailWord_4836988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4836988).length < 2 ^ (prefixWord ++ tailWord_4836988).sum := by decide
  have hdescent : baseEnd_4836988 < baseStart_4836988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4836988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837061 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_4837061 : Nat := 118140960795 + 4837061 * 2 ^ 59
def prefixEnd_4837061 : Nat := 4983230072969 + 3 ^ 40 * 4837061 * 2
def baseEnd_4837061 : Nat := 2483737248117604710292267

theorem tailTrace_4837061 : CollatzResearch.WordTrace tailWord_4837061 prefixEnd_4837061 2483737248117604710292267 := by
  unfold tailWord_4837061
  simp only [CollatzResearch.WordTrace]
  refine ⟨176422108329161576094391037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117614738886107717396260691 176422108329161576094391037)
  ·
    refine ⟨66158290623435591035396639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176422108329161576094391037 66158290623435591035396639)
    ·
      refine ⟨99237435935153386553094959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66158290623435591035396639 99237435935153386553094959)
      ·
        refine ⟨148856153902730079829642439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99237435935153386553094959 148856153902730079829642439)
        ·
          refine ⟨223284230854095119744463659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148856153902730079829642439 223284230854095119744463659)
          ·
            refine ⟨334926346281142679616695489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223284230854095119744463659 334926346281142679616695489)
            ·
              refine ⟨251194759710857009712521617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334926346281142679616695489 251194759710857009712521617)
              ·
                refine ⟨188396069783142757284391213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251194759710857009712521617 188396069783142757284391213)
                ·
                  refine ⟨70648526168678533981646705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188396069783142757284391213 70648526168678533981646705)
                  ·
                    refine ⟨52986394626508900486235029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70648526168678533981646705 52986394626508900486235029)
                    ·
                      refine ⟨2483737248117604710292267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52986394626508900486235029 2483737248117604710292267)
                      ·
                        rfl

theorem cell23_4837061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_4837061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837061 prefixEnd_4837061 := by exact prefixLift 4837061
  have htrace : WordTrace (prefixWord ++ tailWord_4837061) baseStart_4837061 baseEnd_4837061 := by
    simpa [prefixWord, tailWord_4837061, baseEnd_4837061] using wordTrace_append hprefix tailTrace_4837061
  have hstable : (prefixWord ++ tailWord_4837061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837061).length < 2 ^ (prefixWord ++ tailWord_4837061).sum := by decide
  have hdescent : baseEnd_4837061 < baseStart_4837061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837105 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 1, 5]
def baseStart_4837105 : Nat := 118140960795 + 4837105 * 2 ^ 59
def prefixEnd_4837105 : Nat := 4983230072969 + 3 ^ 40 * 4837105 * 2
def baseEnd_4837105 : Nat := 827919947088800846047355

theorem tailTrace_4837105 : CollatzResearch.WordTrace tailWord_4837105 prefixEnd_4837105 827919947088800846047355 := by
  unfold tailWord_4837105
  simp only [CollatzResearch.WordTrace]
  refine ⟨176423713141002171608992769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117615808760668114405995179 176423713141002171608992769)
  ·
    refine ⟨132317784855751628706744577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176423713141002171608992769 132317784855751628706744577)
    ·
      refine ⟨99238338641813721530058433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132317784855751628706744577 99238338641813721530058433)
      ·
        refine ⟨74428753981360291147543825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99238338641813721530058433 74428753981360291147543825)
        ·
          refine ⟨55821565486020218360657869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74428753981360291147543825 55821565486020218360657869)
          ·
            refine ⟨20933087057257581885246701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55821565486020218360657869 20933087057257581885246701)
            ·
              refine ⟨7849907646471593206967513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20933087057257581885246701 7849907646471593206967513)
              ·
                refine ⟨5887430734853694905225635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7849907646471593206967513 5887430734853694905225635)
                ·
                  refine ⟨8831146102280542357838453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5887430734853694905225635 8831146102280542357838453)
                  ·
                    refine ⟨827919947088800846047355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8831146102280542357838453 827919947088800846047355)
                    ·
                      rfl

theorem cell23_4837105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_4837105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837105 prefixEnd_4837105 := by exact prefixLift 4837105
  have htrace : WordTrace (prefixWord ++ tailWord_4837105) baseStart_4837105 baseEnd_4837105 := by
    simpa [prefixWord, tailWord_4837105, baseEnd_4837105] using wordTrace_append hprefix tailTrace_4837105
  have hstable : (prefixWord ++ tailWord_4837105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837105).length < 2 ^ (prefixWord ++ tailWord_4837105).sum := by decide
  have hdescent : baseEnd_4837105 < baseStart_4837105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837172 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_4837172 : Nat := 118140960795 + 4837172 * 2 ^ 59
def prefixEnd_4837172 : Nat := 4983230072969 + 3 ^ 40 * 4837172 * 2
def baseEnd_4837172 : Nat := 2483794244470253776004257

theorem tailTrace_4837172 : CollatzResearch.WordTrace tailWord_4837172 prefixEnd_4837172 2483794244470253776004257 := by
  unfold tailWord_4837172
  simp only [CollatzResearch.WordTrace]
  refine ⟨88213078415879721025840885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117617437887839628034454513 88213078415879721025840885)
  ·
    refine ⟨8269976101488723846172583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88213078415879721025840885 8269976101488723846172583)
    ·
      refine ⟨12404964152233085769258875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8269976101488723846172583 12404964152233085769258875)
      ·
        refine ⟨18607446228349628653888313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12404964152233085769258875 18607446228349628653888313)
        ·
          refine ⟨13955584671262221490416235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18607446228349628653888313 13955584671262221490416235)
          ·
            refine ⟨20933377006893332235624353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13955584671262221490416235 20933377006893332235624353)
            ·
              refine ⟨15700032755169999176718265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20933377006893332235624353 15700032755169999176718265)
              ·
                refine ⟨11775024566377499382538699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15700032755169999176718265 11775024566377499382538699)
                ·
                  refine ⟨17662536849566249073808049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11775024566377499382538699 17662536849566249073808049)
                  ·
                    refine ⟨13246902637174686805356037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17662536849566249073808049 13246902637174686805356037)
                    ·
                      refine ⟨2483794244470253776004257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13246902637174686805356037 2483794244470253776004257)
                      ·
                        rfl

theorem cell23_4837172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_4837172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837172 prefixEnd_4837172 := by exact prefixLift 4837172
  have htrace : WordTrace (prefixWord ++ tailWord_4837172) baseStart_4837172 baseEnd_4837172 := by
    simpa [prefixWord, tailWord_4837172, baseEnd_4837172] using wordTrace_append hprefix tailTrace_4837172
  have hstable : (prefixWord ++ tailWord_4837172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837172).length < 2 ^ (prefixWord ++ tailWord_4837172).sum := by decide
  have hdescent : baseEnd_4837172 < baseStart_4837172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837176 : List Nat := [2, 1, 2, 1, 3, 4, 2, 3, 1, 2, 2]
def baseStart_4837176 : Nat := 118140960795 + 4837176 * 2 ^ 59
def prefixEnd_4837176 : Nat := 4983230072969 + 3 ^ 40 * 4837176 * 2
def baseEnd_4837176 : Nat := 2483796298392871760354239

theorem tailTrace_4837176 : CollatzResearch.WordTrace tailWord_4837176 prefixEnd_4837176 2483796298392871760354239 := by
  unfold tailWord_4837176
  simp only [CollatzResearch.WordTrace]
  refine ⟨88213151361872475367413691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117617535149163300489884921 88213151361872475367413691)
  ·
    refine ⟨132319727042808713051120537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88213151361872475367413691 132319727042808713051120537)
    ·
      refine ⟨99239795282106534788340403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132319727042808713051120537 99239795282106534788340403)
      ·
        refine ⟨148859692923159802182510605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99239795282106534788340403 148859692923159802182510605)
        ·
          refine ⟨55822384846184925818441477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148859692923159802182510605 55822384846184925818441477)
          ·
            refine ⟨10466697158659673590957777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55822384846184925818441477 10466697158659673590957777)
            ·
              refine ⟨7850022868994755193218333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10466697158659673590957777 7850022868994755193218333)
              ·
                refine ⟨2943758575873033197456875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7850022868994755193218333 2943758575873033197456875)
                ·
                  refine ⟨4415637863809549796185313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943758575873033197456875 4415637863809549796185313)
                  ·
                    refine ⟨3311728397857162347138985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4415637863809549796185313 3311728397857162347138985)
                    ·
                      refine ⟨2483796298392871760354239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311728397857162347138985 2483796298392871760354239)
                      ·
                        rfl

theorem cell23_4837176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 1, 2, 2].length) (baseStart_4837176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837176 prefixEnd_4837176 := by exact prefixLift 4837176
  have htrace : WordTrace (prefixWord ++ tailWord_4837176) baseStart_4837176 baseEnd_4837176 := by
    simpa [prefixWord, tailWord_4837176, baseEnd_4837176] using wordTrace_append hprefix tailTrace_4837176
  have hstable : (prefixWord ++ tailWord_4837176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837176).length < 2 ^ (prefixWord ++ tailWord_4837176).sum := by decide
  have hdescent : baseEnd_4837176 < baseStart_4837176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837192 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_4837192 : Nat := 118140960795 + 4837192 * 2 ^ 59
def prefixEnd_4837192 : Nat := 4983230072969 + 3 ^ 40 * 4837192 * 2
def baseEnd_4837192 : Nat := 2483804514083343697754165

theorem tailTrace_4837192 : CollatzResearch.WordTrace tailWord_4837192 prefixEnd_4837192 2483804514083343697754165 := by
  unfold tailWord_4837192
  simp only [CollatzResearch.WordTrace]
  refine ⟨88213443145843492733704915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117617924194457990311606553 88213443145843492733704915)
  ·
    refine ⟨132320164718765239100557373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88213443145843492733704915 132320164718765239100557373)
    ·
      refine ⟨49620061769536964662709015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132320164718765239100557373 49620061769536964662709015)
      ·
        refine ⟨74430092654305446994063523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49620061769536964662709015 74430092654305446994063523)
        ·
          refine ⟨111645138981458170491095285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74430092654305446994063523 111645138981458170491095285)
          ·
            refine ⟨10466731779511703483540183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111645138981458170491095285 10466731779511703483540183)
            ·
              refine ⟨15700097669267555225310275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10466731779511703483540183 15700097669267555225310275)
              ·
                refine ⟨23550146503901332837965413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15700097669267555225310275 23550146503901332837965413)
                ·
                  refine ⟨4415652469481499907118515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23550146503901332837965413 4415652469481499907118515)
                  ·
                    refine ⟨6623478704222249860677773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4415652469481499907118515 6623478704222249860677773)
                    ·
                      refine ⟨2483804514083343697754165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6623478704222249860677773 2483804514083343697754165)
                      ·
                        rfl

theorem cell23_4837192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_4837192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837192 prefixEnd_4837192 := by exact prefixLift 4837192
  have htrace : WordTrace (prefixWord ++ tailWord_4837192) baseStart_4837192 baseEnd_4837192 := by
    simpa [prefixWord, tailWord_4837192, baseEnd_4837192] using wordTrace_append hprefix tailTrace_4837192
  have hstable : (prefixWord ++ tailWord_4837192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837192).length < 2 ^ (prefixWord ++ tailWord_4837192).sum := by decide
  have hdescent : baseEnd_4837192 < baseStart_4837192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837209 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 2, 1, 3]
def baseStart_4837209 : Nat := 118140960795 + 4837209 * 2 ^ 59
def prefixEnd_4837209 : Nat := 4983230072969 + 3 ^ 40 * 4837209 * 2
def baseEnd_4837209 : Nat := 2483813243254470131241587

theorem tailTrace_4837209 : CollatzResearch.WordTrace tailWord_4837209 prefixEnd_4837209 2483813243254470131241587 := by
  unfold tailWord_4837209
  simp only [CollatzResearch.WordTrace]
  refine ⟨176427506332625397370778681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117618337555083598247185787 176427506332625397370778681)
  ·
    refine ⟨132320629749469048028084011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176427506332625397370778681 132320629749469048028084011)
    ·
      refine ⟨198480944624203572042126017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132320629749469048028084011 198480944624203572042126017)
      ·
        refine ⟨148860708468152679031594513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198480944624203572042126017 148860708468152679031594513)
        ·
          refine ⟨111645531351114509273695885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148860708468152679031594513 111645531351114509273695885)
          ·
            refine ⟨41867074256667940977635957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111645531351114509273695885 41867074256667940977635957)
            ·
              refine ⟨3925038211562619466653371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41867074256667940977635957 3925038211562619466653371)
              ·
                refine ⟨5887557317343929199980057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925038211562619466653371 5887557317343929199980057)
                ·
                  refine ⟨4415667988007946899985043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5887557317343929199980057 4415667988007946899985043)
                  ·
                    refine ⟨6623501982011920349977565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4415667988007946899985043 6623501982011920349977565)
                    ·
                      refine ⟨2483813243254470131241587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6623501982011920349977565 2483813243254470131241587)
                      ·
                        rfl

theorem cell23_4837209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 2, 1, 3].length) (baseStart_4837209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837209 prefixEnd_4837209 := by exact prefixLift 4837209
  have htrace : WordTrace (prefixWord ++ tailWord_4837209) baseStart_4837209 baseEnd_4837209 := by
    simpa [prefixWord, tailWord_4837209, baseEnd_4837209] using wordTrace_append hprefix tailTrace_4837209
  have hstable : (prefixWord ++ tailWord_4837209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837209).length < 2 ^ (prefixWord ++ tailWord_4837209).sum := by decide
  have hdescent : baseEnd_4837209 < baseStart_4837209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837248 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_4837248 : Nat := 118140960795 + 4837248 * 2 ^ 59
def prefixEnd_4837248 : Nat := 4983230072969 + 3 ^ 40 * 4837248 * 2
def baseEnd_4837248 : Nat := 2483833268999995478653907

theorem tailTrace_4837248 : CollatzResearch.WordTrace tailWord_4837248 prefixEnd_4837248 2483833268999995478653907 := by
  unfold tailWord_4837248
  simp only [CollatzResearch.WordTrace]
  refine ⟨88214464389742053515724199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117619285852989404687632265 88214464389742053515724199)
  ·
    refine ⟨132321696584613080273586299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88214464389742053515724199 132321696584613080273586299)
    ·
      refine ⟨198482544876919620410379449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132321696584613080273586299 198482544876919620410379449)
      ·
        refine ⟨148861908657689715307784587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198482544876919620410379449 148861908657689715307784587)
        ·
          refine ⟨223292862986534572961676881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148861908657689715307784587 223292862986534572961676881)
          ·
            refine ⟨167469647239900929721257661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223292862986534572961676881 167469647239900929721257661)
            ·
              refine ⟨62801117714962848645471623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167469647239900929721257661 62801117714962848645471623)
              ·
                refine ⟨94201676572444272968207435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62801117714962848645471623 94201676572444272968207435)
                ·
                  refine ⟨141302514858666409452311153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94201676572444272968207435 141302514858666409452311153)
                  ·
                    refine ⟨105976886143999807089233365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141302514858666409452311153 105976886143999807089233365)
                    ·
                      refine ⟨2483833268999995478653907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105976886143999807089233365 2483833268999995478653907)
                      ·
                        rfl

theorem cell23_4837248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_4837248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837248 prefixEnd_4837248 := by exact prefixLift 4837248
  have htrace : WordTrace (prefixWord ++ tailWord_4837248) baseStart_4837248 baseEnd_4837248 := by
    simpa [prefixWord, tailWord_4837248, baseEnd_4837248] using wordTrace_append hprefix tailTrace_4837248
  have hstable : (prefixWord ++ tailWord_4837248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837248).length < 2 ^ (prefixWord ++ tailWord_4837248).sum := by decide
  have hdescent : baseEnd_4837248 < baseStart_4837248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837265 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 3]
def baseStart_4837265 : Nat := 118140960795 + 4837265 * 2 ^ 59
def prefixEnd_4837265 : Nat := 4983230072969 + 3 ^ 40 * 4837265 * 2
def baseEnd_4837265 : Nat := 2483841998171121912141329

theorem tailTrace_4837265 : CollatzResearch.WordTrace tailWord_4837265 prefixEnd_4837265 2483841998171121912141329 := by
  unfold tailWord_4837265
  simp only [CollatzResearch.WordTrace]
  refine ⟨176429548820422518934817249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117619699213615012623211499 176429548820422518934817249)
  ·
    refine ⟨132322161615316889201112937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176429548820422518934817249 132322161615316889201112937)
    ·
      refine ⟨99241621211487666900834703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132322161615316889201112937 99241621211487666900834703)
      ·
        refine ⟨148862431817231500351252055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99241621211487666900834703 148862431817231500351252055)
        ·
          refine ⟨223293647725847250526878083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148862431817231500351252055 223293647725847250526878083)
          ·
            refine ⟨334940471588770875790317125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223293647725847250526878083 334940471588770875790317125)
            ·
              refine ⟨62801338422894539210684461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 334940471588770875790317125 62801338422894539210684461)
              ·
                refine ⟨23550501908585452204006673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62801338422894539210684461 23550501908585452204006673)
                ·
                  refine ⟨17662876431439089153005005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23550501908585452204006673 17662876431439089153005005)
                  ·
                    refine ⟨6623578661789658432376877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17662876431439089153005005 6623578661789658432376877)
                    ·
                      refine ⟨2483841998171121912141329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6623578661789658432376877 2483841998171121912141329)
                      ·
                        rfl

theorem cell23_4837265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_4837265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837265 prefixEnd_4837265 := by exact prefixLift 4837265
  have htrace : WordTrace (prefixWord ++ tailWord_4837265) baseStart_4837265 baseEnd_4837265 := by
    simpa [prefixWord, tailWord_4837265, baseEnd_4837265] using wordTrace_append hprefix tailTrace_4837265
  have hstable : (prefixWord ++ tailWord_4837265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837265).length < 2 ^ (prefixWord ++ tailWord_4837265).sum := by decide
  have hdescent : baseEnd_4837265 < baseStart_4837265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837300 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_4837300 : Nat := 118140960795 + 4837300 * 2 ^ 59
def prefixEnd_4837300 : Nat := 4983230072969 + 3 ^ 40 * 4837300 * 2
def baseEnd_4837300 : Nat := 2483859969994029275203669

theorem tailTrace_4837300 : CollatzResearch.WordTrace tailWord_4837300 prefixEnd_4837300 2483859969994029275203669 := by
  unfold tailWord_4837300
  simp only [CollatzResearch.WordTrace]
  refine ⟨88215412687647859956170677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117620550250197146608227569 88215412687647859956170677)
  ·
    refine ⟨8270194939466986870891001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88215412687647859956170677 8270194939466986870891001)
    ·
      refine ⟨6202646204600240153168251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8270194939466986870891001 6202646204600240153168251)
      ·
        refine ⟨9303969306900360229752377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6202646204600240153168251 9303969306900360229752377)
        ·
          refine ⟨6977976980175270172314283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9303969306900360229752377 6977976980175270172314283)
          ·
            refine ⟨10466965470262905258471425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6977976980175270172314283 10466965470262905258471425)
            ·
              refine ⟨7850224102697178943853569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10466965470262905258471425 7850224102697178943853569)
              ·
                refine ⟨5887668077022884207890177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7850224102697178943853569 5887668077022884207890177)
                ·
                  refine ⟨4415751057767163155917633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5887668077022884207890177 4415751057767163155917633)
                  ·
                    refine ⟨3311813293325372366938225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4415751057767163155917633 3311813293325372366938225)
                    ·
                      refine ⟨2483859969994029275203669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311813293325372366938225 2483859969994029275203669)
                      ·
                        rfl

theorem cell23_4837300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_4837300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837300 prefixEnd_4837300 := by exact prefixLift 4837300
  have htrace : WordTrace (prefixWord ++ tailWord_4837300) baseStart_4837300 baseEnd_4837300 := by
    simpa [prefixWord, tailWord_4837300, baseEnd_4837300] using wordTrace_append hprefix tailTrace_4837300
  have hstable : (prefixWord ++ tailWord_4837300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837300).length < 2 ^ (prefixWord ++ tailWord_4837300).sum := by decide
  have hdescent : baseEnd_4837300 < baseStart_4837300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837322 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2]
def baseStart_4837322 : Nat := 118140960795 + 4837322 * 2 ^ 59
def prefixEnd_4837322 : Nat := 4983230072969 + 3 ^ 40 * 4837322 * 2
def baseEnd_4837322 : Nat := 2483871266568428189128567

theorem tailTrace_4837322 : CollatzResearch.WordTrace tailWord_4837322 prefixEnd_4837322 2483871266568428189128567 := by
  unfold tailWord_4837322
  simp only [CollatzResearch.WordTrace]
  refine ⟨44107906945304004417410555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117621085187477345113094813 44107906945304004417410555)
  ·
    refine ⟨66161860417956006626115833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44107906945304004417410555 66161860417956006626115833)
    ·
      refine ⟨49621395313467004969586875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66161860417956006626115833 49621395313467004969586875)
      ·
        refine ⟨74432092970200507454380313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49621395313467004969586875 74432092970200507454380313)
        ·
          refine ⟨55824069727650380590785235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74432092970200507454380313 55824069727650380590785235)
          ·
            refine ⟨83736104591475570886177853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55824069727650380590785235 83736104591475570886177853)
            ·
              refine ⟨31401039221803339082316695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83736104591475570886177853 31401039221803339082316695)
              ·
                refine ⟨47101558832705008623475043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31401039221803339082316695 47101558832705008623475043)
                ·
                  refine ⟨70652338249057512935212565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47101558832705008623475043 70652338249057512935212565)
                  ·
                    refine ⟨3311828355424570918838089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70652338249057512935212565 3311828355424570918838089)
                    ·
                      refine ⟨2483871266568428189128567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311828355424570918838089 2483871266568428189128567)
                      ·
                        rfl

theorem cell23_4837322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_4837322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837322 prefixEnd_4837322 := by exact prefixLift 4837322
  have htrace : WordTrace (prefixWord ++ tailWord_4837322) baseStart_4837322 baseEnd_4837322 := by
    simpa [prefixWord, tailWord_4837322, baseEnd_4837322] using wordTrace_append hprefix tailTrace_4837322
  have hstable : (prefixWord ++ tailWord_4837322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837322).length < 2 ^ (prefixWord ++ tailWord_4837322).sum := by decide
  have hdescent : baseEnd_4837322 < baseStart_4837322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837355 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 3]
def baseStart_4837355 : Nat := 118140960795 + 4837355 * 2 ^ 59
def prefixEnd_4837355 : Nat := 4983230072969 + 3 ^ 40 * 4837355 * 2
def baseEnd_4837355 : Nat := 2483888211430026560015915

theorem tailTrace_4837355 : CollatzResearch.WordTrace tailWord_4837355 prefixEnd_4837355 2483888211430026560015915 := by
  unfold tailWord_4837355
  simp only [CollatzResearch.WordTrace]
  refine ⟨176432831390096464305593519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117621887593397642870395679 176432831390096464305593519)
  ·
    refine ⟨264649247085144696458390279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176432831390096464305593519 264649247085144696458390279)
    ·
      refine ⟨396973870627717044687585419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264649247085144696458390279 396973870627717044687585419)
      ·
        refine ⟨595460805941575567031378129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396973870627717044687585419 595460805941575567031378129)
        ·
          refine ⟨446595604456181675273533597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595460805941575567031378129 446595604456181675273533597)
          ·
            refine ⟨167473351671068128227575099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 446595604456181675273533597 167473351671068128227575099)
            ·
              refine ⟨251210027506602192341362649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167473351671068128227575099 251210027506602192341362649)
              ·
                refine ⟨188407520629951644256021987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251210027506602192341362649 188407520629951644256021987)
                ·
                  refine ⟨282611280944927466384032981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188407520629951644256021987 282611280944927466384032981)
                  ·
                    refine ⟨6623701897146737493375773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 282611280944927466384032981 6623701897146737493375773)
                    ·
                      refine ⟨2483888211430026560015915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6623701897146737493375773 2483888211430026560015915)
                      ·
                        rfl

theorem cell23_4837355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 3].length) (baseStart_4837355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837355 prefixEnd_4837355 := by exact prefixLift 4837355
  have htrace : WordTrace (prefixWord ++ tailWord_4837355) baseStart_4837355 baseEnd_4837355 := by
    simpa [prefixWord, tailWord_4837355, baseEnd_4837355] using wordTrace_append hprefix tailTrace_4837355
  have hstable : (prefixWord ++ tailWord_4837355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837355).length < 2 ^ (prefixWord ++ tailWord_4837355).sum := by decide
  have hdescent : baseEnd_4837355 < baseStart_4837355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837366 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_4837366 : Nat := 118140960795 + 4837366 * 2 ^ 59
def prefixEnd_4837366 : Nat := 4983230072969 + 3 ^ 40 * 4837366 * 2
def baseEnd_4837366 : Nat := 827964619905742005659455

theorem tailTrace_4837366 : CollatzResearch.WordTrace tailWord_4837366 prefixEnd_4837366 827964619905742005659455 := by
  unfold tailWord_4837366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11027077037066038324015247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117622155062037742122829301 11027077037066038324015247)
  ·
    refine ⟨16540615555599057486022871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11027077037066038324015247 16540615555599057486022871)
    ·
      refine ⟨24810923333398586229034307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16540615555599057486022871 24810923333398586229034307)
      ·
        refine ⟨37216385000097879343551461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24810923333398586229034307 37216385000097879343551461)
        ·
          refine ⟨6978072187518352376915899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37216385000097879343551461 6978072187518352376915899)
          ·
            refine ⟨10467108281277528565373849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6978072187518352376915899 10467108281277528565373849)
            ·
              refine ⟨7850331210958146424030387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10467108281277528565373849 7850331210958146424030387)
              ·
                refine ⟨11775496816437219636045581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7850331210958146424030387 11775496816437219636045581)
                ·
                  refine ⟨4415811306163957363517093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11775496816437219636045581 4415811306163957363517093)
                  ·
                    refine ⟨827964619905742005659455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4415811306163957363517093 827964619905742005659455)
                    ·
                      rfl

theorem cell23_4837366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_4837366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837366 prefixEnd_4837366 := by exact prefixLift 4837366
  have htrace : WordTrace (prefixWord ++ tailWord_4837366) baseStart_4837366 baseEnd_4837366 := by
    simpa [prefixWord, tailWord_4837366, baseEnd_4837366] using wordTrace_append hprefix tailTrace_4837366
  have hstable : (prefixWord ++ tailWord_4837366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837366).length < 2 ^ (prefixWord ++ tailWord_4837366).sum := by decide
  have hdescent : baseEnd_4837366 < baseStart_4837366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837375 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 5, 5]
def baseStart_4837375 : Nat := 118140960795 + 4837375 * 2 ^ 59
def prefixEnd_4837375 : Nat := 4983230072969 + 3 ^ 40 * 4837375 * 2
def baseEnd_4837375 : Nat := 827966160347705493921941

theorem tailTrace_4837375 : CollatzResearch.WordTrace tailWord_4837375 prefixEnd_4837375 827966160347705493921941 := by
  unfold tailWord_4837375
  simp only [CollatzResearch.WordTrace]
  refine ⟨176433560850024007721321579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117622373900016005147547719 176433560850024007721321579)
  ·
    refine ⟨264650341275036011581982369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176433560850024007721321579 264650341275036011581982369)
    ·
      refine ⟨198487755956277008686486777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264650341275036011581982369 198487755956277008686486777)
      ·
        refine ⟨148865816967207756514865083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198487755956277008686486777 148865816967207756514865083)
        ·
          refine ⟨223298725450811634772297625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148865816967207756514865083 223298725450811634772297625)
          ·
            refine ⟨167474044088108726079223219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223298725450811634772297625 167474044088108726079223219)
            ·
              refine ⟨251211066132163089118834829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167474044088108726079223219 251211066132163089118834829)
              ·
                refine ⟨94204149799561158419563061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251211066132163089118834829 94204149799561158419563061)
                ·
                  refine ⟨8831639043708858601834037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94204149799561158419563061 8831639043708858601834037)
                  ·
                    refine ⟨827966160347705493921941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8831639043708858601834037 827966160347705493921941)
                    ·
                      rfl

theorem cell23_4837375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_4837375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837375 prefixEnd_4837375 := by exact prefixLift 4837375
  have htrace : WordTrace (prefixWord ++ tailWord_4837375) baseStart_4837375 baseEnd_4837375 := by
    simpa [prefixWord, tailWord_4837375, baseEnd_4837375] using wordTrace_append hprefix tailTrace_4837375
  have hstable : (prefixWord ++ tailWord_4837375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837375).length < 2 ^ (prefixWord ++ tailWord_4837375).sum := by decide
  have hdescent : baseEnd_4837375 < baseStart_4837375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837446 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_4837446 : Nat := 118140960795 + 4837446 * 2 ^ 59
def prefixEnd_4837446 : Nat := 4983230072969 + 3 ^ 40 * 4837446 * 2
def baseEnd_4837446 : Nat := 2483934938169585703977997

theorem tailTrace_4837446 : CollatzResearch.WordTrace tailWord_4837446 prefixEnd_4837446 2483934938169585703977997 := by
  unfold tailWord_4837446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513629701023962088973631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 117624100288511191231437461 5513629701023962088973631)
  ·
    refine ⟨8270444551535943133460447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5513629701023962088973631 8270444551535943133460447)
    ·
      refine ⟨12405666827303914700190671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8270444551535943133460447 12405666827303914700190671)
      ·
        refine ⟨18608500240955872050286007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12405666827303914700190671 18608500240955872050286007)
        ·
          refine ⟨27912750361433808075429011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18608500240955872050286007 27912750361433808075429011)
          ·
            refine ⟨41869125542150712113143517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27912750361433808075429011 41869125542150712113143517)
            ·
              refine ⟨15700922078306517042428819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41869125542150712113143517 15700922078306517042428819)
              ·
                refine ⟨23551383117459775563643229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15700922078306517042428819 23551383117459775563643229)
                ·
                  refine ⟨8831768669047415836366211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23551383117459775563643229 8831768669047415836366211)
                  ·
                    refine ⟨13247653003571123754549317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8831768669047415836366211 13247653003571123754549317)
                    ·
                      refine ⟨2483934938169585703977997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13247653003571123754549317 2483934938169585703977997)
                      ·
                        rfl

theorem cell23_4837446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_4837446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837446 prefixEnd_4837446 := by exact prefixLift 4837446
  have htrace : WordTrace (prefixWord ++ tailWord_4837446) baseStart_4837446 baseEnd_4837446 := by
    simpa [prefixWord, tailWord_4837446, baseEnd_4837446] using wordTrace_append hprefix tailTrace_4837446
  have hstable : (prefixWord ++ tailWord_4837446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837446).length < 2 ^ (prefixWord ++ tailWord_4837446).sum := by decide
  have hdescent : baseEnd_4837446 < baseStart_4837446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837455 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_4837455 : Nat := 118140960795 + 4837455 * 2 ^ 59
def prefixEnd_4837455 : Nat := 4983230072969 + 3 ^ 40 * 4837455 * 2
def baseEnd_4837455 : Nat := 2483939559495476168765455

theorem tailTrace_4837455 : CollatzResearch.WordTrace tailWord_4837455 prefixEnd_4837455 2483939559495476168765455 := by
  unfold tailWord_4837455
  simp only [CollatzResearch.WordTrace]
  refine ⟨176436478689734181384233819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117624319126489454256155879 176436478689734181384233819)
  ·
    refine ⟨264654718034601272076350729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176436478689734181384233819 264654718034601272076350729)
    ·
      refine ⟨198491038525950954057263047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264654718034601272076350729 198491038525950954057263047)
      ·
        refine ⟨297736557788926431085894571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198491038525950954057263047 297736557788926431085894571)
        ·
          refine ⟨446604836683389646628841857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297736557788926431085894571 446604836683389646628841857)
          ·
            refine ⟨334953627512542234971631393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446604836683389646628841857 334953627512542234971631393)
            ·
              refine ⟨251215220634406676228723545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334953627512542234971631393 251215220634406676228723545)
              ·
                refine ⟨188411415475805007171542659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251215220634406676228723545 188411415475805007171542659)
                ·
                  refine ⟨282617123213707510757313989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188411415475805007171542659 282617123213707510757313989)
                  ·
                    refine ⟨52990710602570158266996373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 282617123213707510757313989 52990710602570158266996373)
                    ·
                      refine ⟨2483939559495476168765455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52990710602570158266996373 2483939559495476168765455)
                      ·
                        rfl

theorem cell23_4837455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_4837455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837455 prefixEnd_4837455 := by exact prefixLift 4837455
  have htrace : WordTrace (prefixWord ++ tailWord_4837455) baseStart_4837455 baseEnd_4837455 := by
    simpa [prefixWord, tailWord_4837455, baseEnd_4837455] using wordTrace_append hprefix tailTrace_4837455
  have hstable : (prefixWord ++ tailWord_4837455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837455).length < 2 ^ (prefixWord ++ tailWord_4837455).sum := by decide
  have hdescent : baseEnd_4837455 < baseStart_4837455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837466 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3]
def baseStart_4837466 : Nat := 118140960795 + 4837466 * 2 ^ 59
def prefixEnd_4837466 : Nat := 4983230072969 + 3 ^ 40 * 4837466 * 2
def baseEnd_4837466 : Nat := 2483945207782675625727905

theorem tailTrace_4837466 : CollatzResearch.WordTrace tailWord_4837466 prefixEnd_4837466 2483945207782675625727905 := by
  unfold tailWord_4837466
  simp only [CollatzResearch.WordTrace]
  refine ⟨44109219973173582565721063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117624586595129553508589501 44109219973173582565721063)
  ·
    refine ⟨66163829959760373848581595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44109219973173582565721063 66163829959760373848581595)
    ·
      refine ⟨99245744939640560772872393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66163829959760373848581595 99245744939640560772872393)
      ·
        refine ⟨74434308704730420579654295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99245744939640560772872393 74434308704730420579654295)
        ·
          refine ⟨111651463057095630869481443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74434308704730420579654295 111651463057095630869481443)
          ·
            refine ⟨167477194585643446304222165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111651463057095630869481443 167477194585643446304222165)
            ·
              refine ⟨3925246748101018272755207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 167477194585643446304222165 3925246748101018272755207)
              ·
                refine ⟨5887870122151527409132811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925246748101018272755207 5887870122151527409132811)
                ·
                  refine ⟨8831805183227291113699217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5887870122151527409132811 8831805183227291113699217)
                  ·
                    refine ⟨6623853887420468335274413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8831805183227291113699217 6623853887420468335274413)
                    ·
                      refine ⟨2483945207782675625727905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6623853887420468335274413 2483945207782675625727905)
                      ·
                        rfl

theorem cell23_4837466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_4837466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837466 prefixEnd_4837466 := by exact prefixLift 4837466
  have htrace : WordTrace (prefixWord ++ tailWord_4837466) baseStart_4837466 baseEnd_4837466 := by
    simpa [prefixWord, tailWord_4837466, baseEnd_4837466] using wordTrace_append hprefix tailTrace_4837466
  have hstable : (prefixWord ++ tailWord_4837466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837466).length < 2 ^ (prefixWord ++ tailWord_4837466).sum := by decide
  have hdescent : baseEnd_4837466 < baseStart_4837466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837474 : List Nat := [3, 3, 2, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_4837474 : Nat := 118140960795 + 4837474 * 2 ^ 59
def prefixEnd_4837474 : Nat := 4983230072969 + 3 ^ 40 * 4837474 * 2
def baseEnd_4837474 : Nat := 2483949315627911594427869

theorem tailTrace_4837474 : CollatzResearch.WordTrace tailWord_4837474 prefixEnd_4837474 2483949315627911594427869 := by
  unfold tailWord_4837474
  simp only [CollatzResearch.WordTrace]
  refine ⟨44109292919166336907293869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117624781117776898419450317 44109292919166336907293869)
  ·
    refine ⟨16540984844687376340235201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44109292919166336907293869 16540984844687376340235201)
    ·
      refine ⟨12405738633515532255176401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16540984844687376340235201 12405738633515532255176401)
      ·
        refine ⟨9304303975136649191382301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12405738633515532255176401 9304303975136649191382301)
        ·
          refine ⟨3489113990676243446768363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9304303975136649191382301 3489113990676243446768363)
          ·
            refine ⟨5233670986014365170152545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489113990676243446768363 5233670986014365170152545)
            ·
              refine ⟨3925253239510773877614409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5233670986014365170152545 3925253239510773877614409)
              ·
                refine ⟨2943939929633080408210807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3925253239510773877614409 2943939929633080408210807)
                ·
                  refine ⟨4415909894449620612316211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943939929633080408210807 4415909894449620612316211)
                  ·
                    refine ⟨6623864841674430918474317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4415909894449620612316211 6623864841674430918474317)
                    ·
                      refine ⟨2483949315627911594427869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6623864841674430918474317 2483949315627911594427869)
                      ·
                        rfl

theorem cell23_4837474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_4837474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837474 prefixEnd_4837474 := by exact prefixLift 4837474
  have htrace : WordTrace (prefixWord ++ tailWord_4837474) baseStart_4837474 baseEnd_4837474 := by
    simpa [prefixWord, tailWord_4837474, baseEnd_4837474] using wordTrace_append hprefix tailTrace_4837474
  have hstable : (prefixWord ++ tailWord_4837474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837474).length < 2 ^ (prefixWord ++ tailWord_4837474).sum := by decide
  have hdescent : baseEnd_4837474 < baseStart_4837474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837489 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 5, 3, 2]
def baseStart_4837489 : Nat := 118140960795 + 4837489 * 2 ^ 59
def prefixEnd_4837489 : Nat := 4983230072969 + 3 ^ 40 * 4837489 * 2
def baseEnd_4837489 : Nat := 2483957017837729035740299

theorem tailTrace_4837489 : CollatzResearch.WordTrace tailWord_4837489 prefixEnd_4837489 2483957017837729035740299 := by
  unfold tailWord_4837489
  simp only [CollatzResearch.WordTrace]
  refine ⟨176437718771611005190971521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117625145847740670127314347 176437718771611005190971521)
  ·
    refine ⟨132328289078708253893228641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176437718771611005190971521 132328289078708253893228641)
    ·
      refine ⟨99246216809031190419921481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132328289078708253893228641 99246216809031190419921481)
      ·
        refine ⟨74434662606773392814941111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99246216809031190419921481 74434662606773392814941111)
        ·
          refine ⟨111651993910160089222411667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74434662606773392814941111 111651993910160089222411667)
          ·
            refine ⟨167477990865240133833617501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111651993910160089222411667 167477990865240133833617501)
            ·
              refine ⟨62804246574465050187606563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167477990865240133833617501 62804246574465050187606563)
              ·
                refine ⟨94206369861697575281409845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62804246574465050187606563 94206369861697575281409845)
                ·
                  refine ⟨8831847174534147682632173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94206369861697575281409845 8831847174534147682632173)
                  ·
                    refine ⟨3311942690450305380987065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8831847174534147682632173 3311942690450305380987065)
                    ·
                      refine ⟨2483957017837729035740299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3311942690450305380987065 2483957017837729035740299)
                      ·
                        rfl

theorem cell23_4837489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_4837489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837489 prefixEnd_4837489 := by exact prefixLift 4837489
  have htrace : WordTrace (prefixWord ++ tailWord_4837489) baseStart_4837489 baseEnd_4837489 := by
    simpa [prefixWord, tailWord_4837489, baseEnd_4837489] using wordTrace_append hprefix tailTrace_4837489
  have hstable : (prefixWord ++ tailWord_4837489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837489).length < 2 ^ (prefixWord ++ tailWord_4837489).sum := by decide
  have hdescent : baseEnd_4837489 < baseStart_4837489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837530 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3]
def baseStart_4837530 : Nat := 118140960795 + 4837530 * 2 ^ 59
def prefixEnd_4837530 : Nat := 4983230072969 + 3 ^ 40 * 4837530 * 2
def baseEnd_4837530 : Nat := 2483978070544563375327611

theorem tailTrace_4837530 : CollatzResearch.WordTrace tailWord_4837530 prefixEnd_4837530 2483978070544563375327611 := by
  unfold tailWord_4837530
  simp only [CollatzResearch.WordTrace]
  refine ⟨44109803541115617298303511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117626142776308312795476029 44109803541115617298303511)
  ·
    refine ⟨66164705311673425947455267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44109803541115617298303511 66164705311673425947455267)
    ·
      refine ⟨99247057967510138921182901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66164705311673425947455267 99247057967510138921182901)
      ·
        refine ⟨9304411684454075523860897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99247057967510138921182901 9304411684454075523860897)
        ·
          refine ⟨6978308763340556642895673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9304411684454075523860897 6978308763340556642895673)
          ·
            refine ⟨5233731572505417482171755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6978308763340556642895673 5233731572505417482171755)
            ·
              refine ⟨7850597358758126223257633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5233731572505417482171755 7850597358758126223257633)
              ·
                refine ⟨5887948019068594667443225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7850597358758126223257633 5887948019068594667443225)
                ·
                  refine ⟨4415961014301446000582419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5887948019068594667443225 4415961014301446000582419)
                  ·
                    refine ⟨6623941521452169000873629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4415961014301446000582419 6623941521452169000873629)
                    ·
                      refine ⟨2483978070544563375327611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6623941521452169000873629 2483978070544563375327611)
                      ·
                        rfl

theorem cell23_4837530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_4837530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837530 prefixEnd_4837530 := by exact prefixLift 4837530
  have htrace : WordTrace (prefixWord ++ tailWord_4837530) baseStart_4837530 baseEnd_4837530 := by
    simpa [prefixWord, tailWord_4837530, baseEnd_4837530] using wordTrace_append hprefix tailTrace_4837530
  have hstable : (prefixWord ++ tailWord_4837530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837530).length < 2 ^ (prefixWord ++ tailWord_4837530).sum := by decide
  have hdescent : baseEnd_4837530 < baseStart_4837530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837619 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 5, 4]
def baseStart_4837619 : Nat := 118140960795 + 4837619 * 2 ^ 59
def prefixEnd_4837619 : Nat := 4983230072969 + 3 ^ 40 * 4837619 * 2
def baseEnd_4837619 : Nat := 828007923440937842371567

theorem tailTrace_4837619 : CollatzResearch.WordTrace tailWord_4837619 prefixEnd_4837619 828007923440937842371567 := by
  unfold tailWord_4837619
  simp only [CollatzResearch.WordTrace]
  refine ⟨176442460261140037393203911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117628306840760024928802607 176442460261140037393203911)
  ·
    refine ⟨264663690391710056089805867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176442460261140037393203911 264663690391710056089805867)
    ·
      refine ⟨396995535587565084134708801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264663690391710056089805867 396995535587565084134708801)
      ·
        refine ⟨297746651690673813101031601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396995535587565084134708801 297746651690673813101031601)
        ·
          refine ⟨223309988768005359825773701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297746651690673813101031601 223309988768005359825773701)
          ·
            refine ⟨41870622894001004967332569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 223309988768005359825773701 41870622894001004967332569)
            ·
              refine ⟨31402967170500753725499427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41870622894001004967332569 31402967170500753725499427)
              ·
                refine ⟨47104450755751130588249141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31402967170500753725499427 47104450755751130588249141)
                ·
                  refine ⟨4416042258351668492648357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47104450755751130588249141 4416042258351668492648357)
                  ·
                    refine ⟨828007923440937842371567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4416042258351668492648357 828007923440937842371567)
                    ·
                      rfl

theorem cell23_4837619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 4].length) (baseStart_4837619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837619 prefixEnd_4837619 := by exact prefixLift 4837619
  have htrace : WordTrace (prefixWord ++ tailWord_4837619) baseStart_4837619 baseEnd_4837619 := by
    simpa [prefixWord, tailWord_4837619, baseEnd_4837619] using wordTrace_append hprefix tailTrace_4837619
  have hstable : (prefixWord ++ tailWord_4837619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837619).length < 2 ^ (prefixWord ++ tailWord_4837619).sum := by decide
  have hdescent : baseEnd_4837619 < baseStart_4837619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837626 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4]
def baseStart_4837626 : Nat := 118140960795 + 4837626 * 2 ^ 59
def prefixEnd_4837626 : Nat := 4983230072969 + 3 ^ 40 * 4837626 * 2
def baseEnd_4837626 : Nat := 2484027364687394999727169

theorem tailTrace_4837626 : CollatzResearch.WordTrace tailWord_4837626 prefixEnd_4837626 2484027364687394999727169 := by
  unfold tailWord_4837626
  simp only [CollatzResearch.WordTrace]
  refine ⟨44110678893028669397177183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117628477048076451725805821 44110678893028669397177183)
  ·
    refine ⟨66166018339543004095765775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44110678893028669397177183 66166018339543004095765775)
    ·
      refine ⟨99249027509314506143648663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66166018339543004095765775 99249027509314506143648663)
      ·
        refine ⟨148873541263971759215472995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99249027509314506143648663 148873541263971759215472995)
        ·
          refine ⟨223310311895957638823209493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148873541263971759215472995 223310311895957638823209493)
          ·
            refine ⟨10467670870123014319837945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 223310311895957638823209493 10467670870123014319837945)
            ·
              refine ⟨7850753152592260739878459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10467670870123014319837945 7850753152592260739878459)
              ·
                refine ⟨11776129728888391109817689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7850753152592260739878459 11776129728888391109817689)
                ·
                  refine ⟨8832097296666293332363267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11776129728888391109817689 8832097296666293332363267)
                  ·
                    refine ⟨13248145944999439998544901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8832097296666293332363267 13248145944999439998544901)
                    ·
                      refine ⟨2484027364687394999727169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13248145944999439998544901 2484027364687394999727169)
                      ·
                        rfl

theorem cell23_4837626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_4837626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837626 prefixEnd_4837626 := by exact prefixLift 4837626
  have htrace : WordTrace (prefixWord ++ tailWord_4837626) baseStart_4837626 baseEnd_4837626 := by
    simpa [prefixWord, tailWord_4837626, baseEnd_4837626] using wordTrace_append hprefix tailTrace_4837626
  have hstable : (prefixWord ++ tailWord_4837626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837626).length < 2 ^ (prefixWord ++ tailWord_4837626).sum := by decide
  have hdescent : baseEnd_4837626 < baseStart_4837626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837629 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_4837629 : Nat := 118140960795 + 4837629 * 2 ^ 59
def prefixEnd_4837629 : Nat := 4983230072969 + 3 ^ 40 * 4837629 * 2
def baseEnd_4837629 : Nat := 2484028905129358487989655

theorem tailTrace_4837629 : CollatzResearch.WordTrace tailWord_4837629 prefixEnd_4837629 2484028905129358487989655 := by
  unfold tailWord_4837629
  simp only [CollatzResearch.WordTrace]
  refine ⟨176442824991103809101067941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117628549994069206067378627 176442824991103809101067941)
  ·
    refine ⟨33083029685831964206450239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176442824991103809101067941 33083029685831964206450239)
    ·
      refine ⟨49624544528747946309675359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33083029685831964206450239 49624544528747946309675359)
      ·
        refine ⟨74436816793121919464513039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49624544528747946309675359 74436816793121919464513039)
        ·
          refine ⟨111655225189682879196769559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74436816793121919464513039 111655225189682879196769559)
          ·
            refine ⟨167482837784524318795154339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111655225189682879196769559 167482837784524318795154339)
            ·
              refine ⟨251224256676786478192731509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167482837784524318795154339 251224256676786478192731509)
              ·
                refine ⟨23552274063448732330568579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 251224256676786478192731509 23552274063448732330568579)
                ·
                  refine ⟨35328411095173098495852869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23552274063448732330568579 35328411095173098495852869)
                  ·
                    refine ⟨6624077080344955967972413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35328411095173098495852869 6624077080344955967972413)
                    ·
                      refine ⟨2484028905129358487989655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6624077080344955967972413 2484028905129358487989655)
                      ·
                        rfl

theorem cell23_4837629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_4837629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837629 prefixEnd_4837629 := by exact prefixLift 4837629
  have htrace : WordTrace (prefixWord ++ tailWord_4837629) baseStart_4837629 baseEnd_4837629 := by
    simpa [prefixWord, tailWord_4837629, baseEnd_4837629] using wordTrace_append hprefix tailTrace_4837629
  have hstable : (prefixWord ++ tailWord_4837629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837629).length < 2 ^ (prefixWord ++ tailWord_4837629).sum := by decide
  have hdescent : baseEnd_4837629 < baseStart_4837629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837632 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 10]
def baseStart_4837632 : Nat := 118140960795 + 4837632 * 2 ^ 59
def prefixEnd_4837632 : Nat := 4983230072969 + 3 ^ 40 * 4837632 * 2
def baseEnd_4837632 : Nat := 276003382841257997361349

theorem tailTrace_4837632 : CollatzResearch.WordTrace tailWord_4837632 prefixEnd_4837632 276003382841257997361349 := by
  unfold tailWord_4837632
  simp only [CollatzResearch.WordTrace]
  refine ⟨88221467205046470306713575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117628622940061960408951433 88221467205046470306713575)
  ·
    refine ⟨132332200807569705460070363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88221467205046470306713575 132332200807569705460070363)
    ·
      refine ⟨198498301211354558190105545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132332200807569705460070363 198498301211354558190105545)
      ·
        refine ⟨148873725908515918642579159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198498301211354558190105545 148873725908515918642579159)
        ·
          refine ⟨223310588862773877963868739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148873725908515918642579159 223310588862773877963868739)
          ·
            refine ⟨334965883294160816945803109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223310588862773877963868739 334965883294160816945803109)
            ·
              refine ⟨62806103117655153177338083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 334965883294160816945803109 62806103117655153177338083)
              ·
                refine ⟨94209154676482729766007125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62806103117655153177338083 94209154676482729766007125)
                ·
                  refine ⟨276003382841257997361349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 94209154676482729766007125 276003382841257997361349)
                  ·
                    rfl

theorem cell23_4837632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 10].length) (baseStart_4837632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837632 prefixEnd_4837632 := by exact prefixLift 4837632
  have htrace : WordTrace (prefixWord ++ tailWord_4837632) baseStart_4837632 baseEnd_4837632 := by
    simpa [prefixWord, tailWord_4837632, baseEnd_4837632] using wordTrace_append hprefix tailTrace_4837632
  have hstable : (prefixWord ++ tailWord_4837632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837632).length < 2 ^ (prefixWord ++ tailWord_4837632).sum := by decide
  have hdescent : baseEnd_4837632 < baseStart_4837632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837646 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_4837646 : Nat := 118140960795 + 4837646 * 2 ^ 59
def prefixEnd_4837646 : Nat := 4983230072969 + 3 ^ 40 * 4837646 * 2
def baseEnd_4837646 : Nat := 2484037634300484921477077

theorem tailTrace_4837646 : CollatzResearch.WordTrace tailWord_4837646 prefixEnd_4837646 2484037634300484921477077 := by
  unfold tailWord_4837646
  simp only [CollatzResearch.WordTrace]
  refine ⟨22055430629005277625554599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117628963354694814002957861 22055430629005277625554599)
  ·
    refine ⟨33083145943507916438331899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22055430629005277625554599 33083145943507916438331899)
    ·
      refine ⟨49624718915261874657497849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33083145943507916438331899 49624718915261874657497849)
      ·
        refine ⟨37218539186446405993123387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49624718915261874657497849 37218539186446405993123387)
        ·
          refine ⟨55827808779669608989685081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37218539186446405993123387 55827808779669608989685081)
          ·
            refine ⟨41870856584752206742263811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55827808779669608989685081 41870856584752206742263811)
            ·
              refine ⟨62806284877128310113395717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41870856584752206742263811 62806284877128310113395717)
              ·
                refine ⟨11776178414461558146261697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62806284877128310113395717 11776178414461558146261697)
                ·
                  refine ⟨8832133810846168609696273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11776178414461558146261697 8832133810846168609696273)
                  ·
                    refine ⟨6624100358134626457272205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8832133810846168609696273 6624100358134626457272205)
                    ·
                      refine ⟨2484037634300484921477077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6624100358134626457272205 2484037634300484921477077)
                      ·
                        rfl

theorem cell23_4837646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_4837646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837646 prefixEnd_4837646 := by exact prefixLift 4837646
  have htrace : WordTrace (prefixWord ++ tailWord_4837646) baseStart_4837646 baseEnd_4837646 := by
    simpa [prefixWord, tailWord_4837646, baseEnd_4837646] using wordTrace_append hprefix tailTrace_4837646
  have hstable : (prefixWord ++ tailWord_4837646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837646).length < 2 ^ (prefixWord ++ tailWord_4837646).sum := by decide
  have hdescent : baseEnd_4837646 < baseStart_4837646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837649 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 6]
def baseStart_4837649 : Nat := 118140960795 + 4837649 * 2 ^ 59
def prefixEnd_4837649 : Nat := 4983230072969 + 3 ^ 40 * 4837649 * 2
def baseEnd_4837649 : Nat := 276004352749160934415507

theorem tailTrace_4837649 : CollatzResearch.WordTrace tailWord_4837649 prefixEnd_4837649 276004352749160934415507 := by
  unfold tailWord_4837649
  simp only [CollatzResearch.WordTrace]
  refine ⟨176443554451031352516796001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117629036300687568344530667 176443554451031352516796001)
  ·
    refine ⟨132332665838273514387597001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176443554451031352516796001 132332665838273514387597001)
    ·
      refine ⟨99249499378705135790697751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132332665838273514387597001 99249499378705135790697751)
      ·
        refine ⟨148874249068057703686046627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99249499378705135790697751 148874249068057703686046627)
        ·
          refine ⟨223311373602086555529069941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148874249068057703686046627 223311373602086555529069941)
          ·
            refine ⟨20935441275195614580850307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 223311373602086555529069941 20935441275195614580850307)
            ·
              refine ⟨31403161912793421871275461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20935441275195614580850307 31403161912793421871275461)
              ·
                refine ⟨5888092858648766600864149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31403161912793421871275461 5888092858648766600864149)
                ·
                  refine ⟨276004352749160934415507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5888092858648766600864149 276004352749160934415507)
                  ·
                    rfl

theorem cell23_4837649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 6].length) (baseStart_4837649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837649 prefixEnd_4837649 := by exact prefixLift 4837649
  have htrace : WordTrace (prefixWord ++ tailWord_4837649) baseStart_4837649 baseEnd_4837649 := by
    simpa [prefixWord, tailWord_4837649, baseEnd_4837649] using wordTrace_append hprefix tailTrace_4837649
  have hstable : (prefixWord ++ tailWord_4837649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837649).length < 2 ^ (prefixWord ++ tailWord_4837649).sum := by decide
  have hdescent : baseEnd_4837649 < baseStart_4837649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837666 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 6]
def baseStart_4837666 : Nat := 118140960795 + 4837666 * 2 ^ 59
def prefixEnd_4837666 : Nat := 4983230072969 + 3 ^ 40 * 4837666 * 2
def baseEnd_4837666 : Nat := 276005322657063871469665

theorem tailTrace_4837666 : CollatzResearch.WordTrace tailWord_4837666 prefixEnd_4837666 276005322657063871469665 := by
  unfold tailWord_4837666
  simp only [CollatzResearch.WordTrace]
  refine ⟨44111043622992441105041213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117629449661313176280109901 44111043622992441105041213)
  ·
    refine ⟨16541641358622165414390455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44111043622992441105041213 16541641358622165414390455)
    ·
      refine ⟨24812462037933248121585683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16541641358622165414390455 24812462037933248121585683)
      ·
        refine ⟨37218693056899872182378525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24812462037933248121585683 37218693056899872182378525)
        ·
          refine ⟨13957009896337452068391947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37218693056899872182378525 13957009896337452068391947)
          ·
            refine ⟨20935514844506178102587921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13957009896337452068391947 20935514844506178102587921)
            ·
              refine ⟨15701636133379633576940941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20935514844506178102587921 15701636133379633576940941)
              ·
                refine ⟨5888113550017362591352853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15701636133379633576940941 5888113550017362591352853)
                ·
                  refine ⟨276005322657063871469665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5888113550017362591352853 276005322657063871469665)
                  ·
                    rfl

theorem cell23_4837666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_4837666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837666 prefixEnd_4837666 := by exact prefixLift 4837666
  have htrace : WordTrace (prefixWord ++ tailWord_4837666) baseStart_4837666 baseEnd_4837666 := by
    simpa [prefixWord, tailWord_4837666, baseEnd_4837666] using wordTrace_append hprefix tailTrace_4837666
  have hstable : (prefixWord ++ tailWord_4837666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837666).length < 2 ^ (prefixWord ++ tailWord_4837666).sum := by decide
  have hdescent : baseEnd_4837666 < baseStart_4837666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837676 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 3]
def baseStart_4837676 : Nat := 118140960795 + 4837676 * 2 ^ 59
def prefixEnd_4837676 : Nat := 4983230072969 + 3 ^ 40 * 4837676 * 2
def baseEnd_4837676 : Nat := 2484053038720119804101939

theorem tailTrace_4837676 : CollatzResearch.WordTrace tailWord_4837676 prefixEnd_4837676 2484053038720119804101939 := by
  unfold tailWord_4837676
  simp only [CollatzResearch.WordTrace]
  refine ⟨88222269610966768064014441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117629692814622357418685921 88222269610966768064014441)
  ·
    refine ⟨66166702208225076048010831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88222269610966768064014441 66166702208225076048010831)
    ·
      refine ⟨99250053312337614072016247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66166702208225076048010831 99250053312337614072016247)
      ·
        refine ⟨148875079968506421108024371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99250053312337614072016247 148875079968506421108024371)
        ·
          refine ⟨223312619952759631662036557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148875079968506421108024371 223312619952759631662036557)
          ·
            refine ⟨83742232482284861873263709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223312619952759631662036557 83742232482284861873263709)
            ·
              refine ⟨31403337180856823202473891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83742232482284861873263709 31403337180856823202473891)
              ·
                refine ⟨47105005771285234803710837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31403337180856823202473891 47105005771285234803710837)
                ·
                  refine ⟨4416094291057990762847891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47105005771285234803710837 4416094291057990762847891)
                  ·
                    refine ⟨6624141436586986144271837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4416094291057990762847891 6624141436586986144271837)
                    ·
                      refine ⟨2484053038720119804101939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6624141436586986144271837 2484053038720119804101939)
                      ·
                        rfl

theorem cell23_4837676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_4837676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837676 prefixEnd_4837676 := by exact prefixLift 4837676
  have htrace : WordTrace (prefixWord ++ tailWord_4837676) baseStart_4837676 baseEnd_4837676 := by
    simpa [prefixWord, tailWord_4837676, baseEnd_4837676] using wordTrace_append hprefix tailTrace_4837676
  have hstable : (prefixWord ++ tailWord_4837676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837676).length < 2 ^ (prefixWord ++ tailWord_4837676).sum := by decide
  have hdescent : baseEnd_4837676 < baseStart_4837676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837677 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_4837677 : Nat := 118140960795 + 4837677 * 2 ^ 59
def prefixEnd_4837677 : Nat := 4983230072969 + 3 ^ 40 * 4837677 * 2
def baseEnd_4837677 : Nat := 2484053552200774300189435

theorem tailTrace_4837677 : CollatzResearch.WordTrace tailWord_4837677 prefixEnd_4837677 2484053552200774300189435 := by
  unfold tailWord_4837677
  simp only [CollatzResearch.WordTrace]
  refine ⟨176444575694929913298815285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117629717129953275532543523 176444575694929913298815285)
  ·
    refine ⟨16541678971399679371763933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176444575694929913298815285 16541678971399679371763933)
    ·
      refine ⟨6203129614274879764411475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16541678971399679371763933 6203129614274879764411475)
      ·
        refine ⟨9304694421412319646617213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6203129614274879764411475 9304694421412319646617213)
        ·
          refine ⟨3489260408029619867481455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9304694421412319646617213 3489260408029619867481455)
          ·
            refine ⟨5233890612044429801222183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489260408029619867481455 5233890612044429801222183)
            ·
              refine ⟨7850835918066644701833275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5233890612044429801222183 7850835918066644701833275)
              ·
                refine ⟨11776253877099967052749913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7850835918066644701833275 11776253877099967052749913)
                ·
                  refine ⟨8832190407824975289562435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11776253877099967052749913 8832190407824975289562435)
                  ·
                    refine ⟨13248285611737462934343653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8832190407824975289562435 13248285611737462934343653)
                    ·
                      refine ⟨2484053552200774300189435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13248285611737462934343653 2484053552200774300189435)
                      ·
                        rfl

theorem cell23_4837677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_4837677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837677 prefixEnd_4837677 := by exact prefixLift 4837677
  have htrace : WordTrace (prefixWord ++ tailWord_4837677) baseStart_4837677 baseEnd_4837677 := by
    simpa [prefixWord, tailWord_4837677, baseEnd_4837677] using wordTrace_append hprefix tailTrace_4837677
  have hstable : (prefixWord ++ tailWord_4837677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837677).length < 2 ^ (prefixWord ++ tailWord_4837677).sum := by decide
  have hdescent : baseEnd_4837677 < baseStart_4837677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837679 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 3, 5]
def baseStart_4837679 : Nat := 118140960795 + 4837679 * 2 ^ 59
def prefixEnd_4837679 : Nat := 4983230072969 + 3 ^ 40 * 4837679 * 2
def baseEnd_4837679 : Nat := 828018193054027764121475

theorem tailTrace_4837679 : CollatzResearch.WordTrace tailWord_4837679 prefixEnd_4837679 828018193054027764121475 := by
  unfold tailWord_4837679
  simp only [CollatzResearch.WordTrace]
  refine ⟨176444648640922667640388091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117629765760615111760258727 176444648640922667640388091)
  ·
    refine ⟨264666972961384001460582137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176444648640922667640388091 264666972961384001460582137)
    ·
      refine ⟨198500229721038001095436603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264666972961384001460582137 198500229721038001095436603)
      ·
        refine ⟨297750344581557001643154905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198500229721038001095436603 297750344581557001643154905)
        ·
          refine ⟨223312758436167751232366179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297750344581557001643154905 223312758436167751232366179)
          ·
            refine ⟨334969137654251626848549269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223312758436167751232366179 334969137654251626848549269)
            ·
              refine ⟨15701678327543045008525747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 334969137654251626848549269 15701678327543045008525747)
              ·
                refine ⟨23552517491314567512788621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15701678327543045008525747 23552517491314567512788621)
                ·
                  refine ⟨8832194059242962817295733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23552517491314567512788621 8832194059242962817295733)
                  ·
                    refine ⟨828018193054027764121475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8832194059242962817295733 828018193054027764121475)
                    ·
                      rfl

theorem cell23_4837679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_4837679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837679 prefixEnd_4837679 := by exact prefixLift 4837679
  have htrace : WordTrace (prefixWord ++ tailWord_4837679) baseStart_4837679 baseEnd_4837679 := by
    simpa [prefixWord, tailWord_4837679, baseEnd_4837679] using wordTrace_append hprefix tailTrace_4837679
  have hstable : (prefixWord ++ tailWord_4837679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837679).length < 2 ^ (prefixWord ++ tailWord_4837679).sum := by decide
  have hdescent : baseEnd_4837679 < baseStart_4837679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837700 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 6]
def baseStart_4837700 : Nat := 118140960795 + 4837700 * 2 ^ 59
def prefixEnd_4837700 : Nat := 4983230072969 + 3 ^ 40 * 4837700 * 2
def baseEnd_4837700 : Nat := 276007262472869745577981

theorem tailTrace_4837700 : CollatzResearch.WordTrace tailWord_4837700 prefixEnd_4837700 276007262472869745577981 := by
  unfold tailWord_4837700
  simp only [CollatzResearch.WordTrace]
  refine ⟨88222707286923294113451277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117630276382564392151268369 88222707286923294113451277)
  ·
    refine ⟨33083515232596235292544229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88222707286923294113451277 33083515232596235292544229)
    ·
      refine ⟨6203159106111794117352043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33083515232596235292544229 6203159106111794117352043)
      ·
        refine ⟨9304738659167691176028065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6203159106111794117352043 9304738659167691176028065)
        ·
          refine ⟨6978553994375768382021049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9304738659167691176028065 6978553994375768382021049)
          ·
            refine ⟨5233915495781826286515787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6978553994375768382021049 5233915495781826286515787)
            ·
              refine ⟨7850873243672739429773681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5233915495781826286515787 7850873243672739429773681)
              ·
                refine ⟨5888154932754554572330261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7850873243672739429773681 5888154932754554572330261)
                ·
                  refine ⟨276007262472869745577981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5888154932754554572330261 276007262472869745577981)
                  ·
                    rfl

theorem cell23_4837700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_4837700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837700 prefixEnd_4837700 := by exact prefixLift 4837700
  have htrace : WordTrace (prefixWord ++ tailWord_4837700) baseStart_4837700 baseEnd_4837700 := by
    simpa [prefixWord, tailWord_4837700, baseEnd_4837700] using wordTrace_append hprefix tailTrace_4837700
  have hstable : (prefixWord ++ tailWord_4837700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837700).length < 2 ^ (prefixWord ++ tailWord_4837700).sum := by decide
  have hdescent : baseEnd_4837700 < baseStart_4837700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837733 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 4]
def baseStart_4837733 : Nat := 118140960795 + 4837733 * 2 ^ 59
def prefixEnd_4837733 : Nat := 4983230072969 + 3 ^ 40 * 4837733 * 2
def baseEnd_4837733 : Nat := 2484082307117426081089177

theorem tailTrace_4837733 : CollatzResearch.WordTrace tailWord_4837733 prefixEnd_4837733 2484082307117426081089177 := by
  unfold tailWord_4837733
  simp only [CollatzResearch.WordTrace]
  refine ⟨176446618182727034862853853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117631078788484689908569235 176446618182727034862853853)
  ·
    refine ⟨66167481818522638073570195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176446618182727034862853853 66167481818522638073570195)
    ·
      refine ⟨99251222727783957110355293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66167481818522638073570195 99251222727783957110355293)
      ·
        refine ⟨37219208522918983916383235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99251222727783957110355293 37219208522918983916383235)
        ·
          refine ⟨55828812784378475874574853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37219208522918983916383235 55828812784378475874574853)
          ·
            refine ⟨10467902397070964226482785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55828812784378475874574853 10467902397070964226482785)
            ·
              refine ⟨7850926797803223169862089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10467902397070964226482785 7850926797803223169862089)
              ·
                refine ⟨5888195098352417377396567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7850926797803223169862089 5888195098352417377396567)
                ·
                  refine ⟨8832292647528626066094851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5888195098352417377396567 8832292647528626066094851)
                  ·
                    refine ⟨13248438971292939099142277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8832292647528626066094851 13248438971292939099142277)
                    ·
                      refine ⟨2484082307117426081089177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13248438971292939099142277 2484082307117426081089177)
                      ·
                        rfl

theorem cell23_4837733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_4837733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837733 prefixEnd_4837733 := by exact prefixLift 4837733
  have htrace : WordTrace (prefixWord ++ tailWord_4837733) baseStart_4837733 baseEnd_4837733 := by
    simpa [prefixWord, tailWord_4837733, baseEnd_4837733] using wordTrace_append hprefix tailTrace_4837733
  have hstable : (prefixWord ++ tailWord_4837733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837733).length < 2 ^ (prefixWord ++ tailWord_4837733).sum := by decide
  have hdescent : baseEnd_4837733 < baseStart_4837733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837800 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_4837800 : Nat := 118140960795 + 4837800 * 2 ^ 59
def prefixEnd_4837800 : Nat := 4983230072969 + 3 ^ 40 * 4837800 * 2
def baseEnd_4837800 : Nat := 2484116710321277318951369

theorem tailTrace_4837800 : CollatzResearch.WordTrace tailWord_4837800 prefixEnd_4837800 2484116710321277318951369 := by
  unfold tailWord_4837800
  simp only [CollatzResearch.WordTrace]
  refine ⟨88224530936742152652771427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117632707915656203537028569 88224530936742152652771427)
  ·
    refine ⟨132336796405113228979157141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88224530936742152652771427 132336796405113228979157141)
    ·
      refine ⟨6203287331489682608397991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132336796405113228979157141 6203287331489682608397991)
      ·
        refine ⟨9304930997234523912596987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6203287331489682608397991 9304930997234523912596987)
        ·
          refine ⟨13957396495851785868895481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9304930997234523912596987 13957396495851785868895481)
          ·
            refine ⟨10468047371888839401671611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13957396495851785868895481 10468047371888839401671611)
            ·
              refine ⟨15702071057833259102507417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10468047371888839401671611 15702071057833259102507417)
              ·
                refine ⟨11776553293374944326880563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15702071057833259102507417 11776553293374944326880563)
                ·
                  refine ⟨17664829940062416490320845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11776553293374944326880563 17664829940062416490320845)
                  ·
                    refine ⟨6624311227523406183870317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17664829940062416490320845 6624311227523406183870317)
                    ·
                      refine ⟨2484116710321277318951369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6624311227523406183870317 2484116710321277318951369)
                      ·
                        rfl

theorem cell23_4837800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_4837800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837800 prefixEnd_4837800 := by exact prefixLift 4837800
  have htrace : WordTrace (prefixWord ++ tailWord_4837800) baseStart_4837800 baseEnd_4837800 := by
    simpa [prefixWord, tailWord_4837800, baseEnd_4837800] using wordTrace_append hprefix tailTrace_4837800
  have hstable : (prefixWord ++ tailWord_4837800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837800).length < 2 ^ (prefixWord ++ tailWord_4837800).sum := by decide
  have hdescent : baseEnd_4837800 < baseStart_4837800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837829 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 13]
def baseStart_4837829 : Nat := 118140960795 + 4837829 * 2 ^ 59
def prefixEnd_4837829 : Nat := 4983230072969 + 3 ^ 40 * 4837829 * 2
def baseEnd_4837829 : Nat := 276014622362250856165415

theorem tailTrace_4837829 : CollatzResearch.WordTrace tailWord_4837829 prefixEnd_4837829 276014622362250856165415 := by
  unfold tailWord_4837829
  simp only [CollatzResearch.WordTrace]
  refine ⟨176450119590379243258348541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117633413060252828838899027 176450119590379243258348541)
  ·
    refine ⟨66168794846392216221880703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176450119590379243258348541 66168794846392216221880703)
    ·
      refine ⟨99253192269588324332821055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66168794846392216221880703 99253192269588324332821055)
      ·
        refine ⟨148879788404382486499231583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99253192269588324332821055 148879788404382486499231583)
        ·
          refine ⟨223319682606573729748847375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148879788404382486499231583 223319682606573729748847375)
          ·
            refine ⟨334979523909860594623271063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223319682606573729748847375 334979523909860594623271063)
            ·
              refine ⟨502469285864790891934906595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334979523909860594623271063 502469285864790891934906595)
              ·
                refine ⟨753703928797186337902359893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502469285864790891934906595 753703928797186337902359893)
                ·
                  refine ⟨276014622362250856165415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 753703928797186337902359893 276014622362250856165415)
                  ·
                    rfl

theorem cell23_4837829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_4837829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837829 prefixEnd_4837829 := by exact prefixLift 4837829
  have htrace : WordTrace (prefixWord ++ tailWord_4837829) baseStart_4837829 baseEnd_4837829 := by
    simpa [prefixWord, tailWord_4837829, baseEnd_4837829] using wordTrace_append hprefix tailTrace_4837829
  have hstable : (prefixWord ++ tailWord_4837829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837829).length < 2 ^ (prefixWord ++ tailWord_4837829).sum := by decide
  have hdescent : baseEnd_4837829 < baseStart_4837829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837856 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 3]
def baseStart_4837856 : Nat := 118140960795 + 4837856 * 2 ^ 59
def prefixEnd_4837856 : Nat := 4983230072969 + 3 ^ 40 * 4837856 * 2
def baseEnd_4837856 : Nat := 2484145465237929099851111

theorem tailTrace_4837856 : CollatzResearch.WordTrace tailWord_4837856 prefixEnd_4837856 2484145465237929099851111 := by
  unfold tailWord_4837856
  simp only [CollatzResearch.WordTrace]
  refine ⟨88225552180640713434790711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117634069574187617913054281 88225552180640713434790711)
  ·
    refine ⟨132338328270961070152186067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88225552180640713434790711 132338328270961070152186067)
    ·
      refine ⟨198507492406441605228279101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132338328270961070152186067 198507492406441605228279101)
      ·
        refine ⟨74440309652415601960604663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198507492406441605228279101 74440309652415601960604663)
        ·
          refine ⟨111660464478623402940906995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74440309652415601960604663 111660464478623402940906995)
          ·
            refine ⟨167490696717935104411360493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111660464478623402940906995 167490696717935104411360493)
            ·
              refine ⟨62809011269225664154260185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167490696717935104411360493 62809011269225664154260185)
              ·
                refine ⟨47106758451919248115695139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62809011269225664154260185 47106758451919248115695139)
                ·
                  refine ⟨70660137677878872173542709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47106758451919248115695139 70660137677878872173542709)
                  ·
                    refine ⟨6624387907301144266269629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70660137677878872173542709 6624387907301144266269629)
                    ·
                      refine ⟨2484145465237929099851111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6624387907301144266269629 2484145465237929099851111)
                      ·
                        rfl

theorem cell23_4837856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_4837856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837856 prefixEnd_4837856 := by exact prefixLift 4837856
  have htrace : WordTrace (prefixWord ++ tailWord_4837856) baseStart_4837856 baseEnd_4837856 := by
    simpa [prefixWord, tailWord_4837856, baseEnd_4837856] using wordTrace_append hprefix tailTrace_4837856
  have hstable : (prefixWord ++ tailWord_4837856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837856).length < 2 ^ (prefixWord ++ tailWord_4837856).sum := by decide
  have hdescent : baseEnd_4837856 < baseStart_4837856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837861 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 1, 3, 2]
def baseStart_4837861 : Nat := 118140960795 + 4837861 * 2 ^ 59
def prefixEnd_4837861 : Nat := 4983230072969 + 3 ^ 40 * 4837861 * 2
def baseEnd_4837861 : Nat := 2484148032641201580288589

theorem tailTrace_4837861 : CollatzResearch.WordTrace tailWord_4837861 prefixEnd_4837861 2484148032641201580288589 := by
  unfold tailWord_4837861
  simp only [CollatzResearch.WordTrace]
  refine ⟨176451286726263312723513437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117634191150842208482342291 176451286726263312723513437)
  ·
    refine ⟨66169232522348742271317539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176451286726263312723513437 66169232522348742271317539)
    ·
      refine ⟨99253848783523113406976309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66169232522348742271317539 99253848783523113406976309)
      ·
        refine ⟨9305048323455291881904029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99253848783523113406976309 9305048323455291881904029)
        ·
          refine ⟨3489393121295734455714011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9305048323455291881904029 3489393121295734455714011)
          ·
            refine ⟨5234089681943601683571017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489393121295734455714011 5234089681943601683571017)
            ·
              refine ⟨3925567261457701262678263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5234089681943601683571017 3925567261457701262678263)
              ·
                refine ⟨5888350892186551894017395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925567261457701262678263 5888350892186551894017395)
                ·
                  refine ⟨8832526338279827841026093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5888350892186551894017395 8832526338279827841026093)
                  ·
                    refine ⟨3312197376854935440384785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8832526338279827841026093 3312197376854935440384785)
                    ·
                      refine ⟨2484148032641201580288589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3312197376854935440384785 2484148032641201580288589)
                      ·
                        rfl

theorem cell23_4837861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_4837861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837861 prefixEnd_4837861 := by exact prefixLift 4837861
  have htrace : WordTrace (prefixWord ++ tailWord_4837861) baseStart_4837861 baseEnd_4837861 := by
    simpa [prefixWord, tailWord_4837861, baseEnd_4837861] using wordTrace_append hprefix tailTrace_4837861
  have hstable : (prefixWord ++ tailWord_4837861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837861).length < 2 ^ (prefixWord ++ tailWord_4837861).sum := by decide
  have hdescent : baseEnd_4837861 < baseStart_4837861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837927 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4837927 : Nat := 118140960795 + 4837927 * 2 ^ 59
def prefixEnd_4837927 : Nat := 4983230072969 + 3 ^ 40 * 4837927 * 2
def baseEnd_4837927 : Nat := 828060640788132774021095

theorem tailTrace_4837927 : CollatzResearch.WordTrace tailWord_4837927 prefixEnd_4837927 828060640788132774021095 := by
  unfold tailWord_4837927
  simp only [CollatzResearch.WordTrace]
  refine ⟨176453693944024205995416035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117635795962682803996944023 176453693944024205995416035)
  ·
    refine ⟨264680540916036308993124053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176453693944024205995416035 264680540916036308993124053)
    ·
      refine ⟨6203450177719600992026345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 264680540916036308993124053 6203450177719600992026345)
      ·
        refine ⟨4652587633289700744019759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6203450177719600992026345 4652587633289700744019759)
        ·
          refine ⟨6978881449934551116029639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4652587633289700744019759 6978881449934551116029639)
          ·
            refine ⟨10468322174901826674044459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6978881449934551116029639 10468322174901826674044459)
            ·
              refine ⟨15702483262352740011066689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10468322174901826674044459 15702483262352740011066689)
              ·
                refine ⟨11776862446764555008300017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15702483262352740011066689 11776862446764555008300017)
                ·
                  refine ⟨8832646835073416256225013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11776862446764555008300017 8832646835073416256225013)
                  ·
                    refine ⟨828060640788132774021095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8832646835073416256225013 828060640788132774021095)
                    ·
                      rfl

theorem cell23_4837927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4837927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837927 prefixEnd_4837927 := by exact prefixLift 4837927
  have htrace : WordTrace (prefixWord ++ tailWord_4837927) baseStart_4837927 baseEnd_4837927 := by
    simpa [prefixWord, tailWord_4837927, baseEnd_4837927] using wordTrace_append hprefix tailTrace_4837927
  have hstable : (prefixWord ++ tailWord_4837927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837927).length < 2 ^ (prefixWord ++ tailWord_4837927).sum := by decide
  have hdescent : baseEnd_4837927 < baseStart_4837927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837930 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4837930 : Nat := 118140960795 + 4837930 * 2 ^ 59
def prefixEnd_4837930 : Nat := 4983230072969 + 3 ^ 40 * 4837930 * 2
def baseEnd_4837930 : Nat := 2484183462806361810325771

theorem tailTrace_4837930 : CollatzResearch.WordTrace tailWord_4837930 prefixEnd_4837930 2484183462806361810325771 := by
  unfold tailWord_4837930
  simp only [CollatzResearch.WordTrace]
  refine ⟨44113450840753334376943811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117635868908675558338516829 44113450840753334376943811)
  ·
    refine ⟨66170176261130001565415717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44113450840753334376943811 66170176261130001565415717)
    ·
      refine ⟨12406908048961875293515447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66170176261130001565415717 12406908048961875293515447)
      ·
        refine ⟨18610362073442812940273171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12406908048961875293515447 18610362073442812940273171)
        ·
          refine ⟨27915543110164219410409757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18610362073442812940273171 27915543110164219410409757)
          ·
            refine ⟨10468328666311582278903659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27915543110164219410409757 10468328666311582278903659)
            ·
              refine ⟨15702492999467373418355489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10468328666311582278903659 15702492999467373418355489)
              ·
                refine ⟨11776869749600530063766617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15702492999467373418355489 11776869749600530063766617)
                ·
                  refine ⟨8832652312200397547824963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11776869749600530063766617 8832652312200397547824963)
                  ·
                    refine ⟨13248978468300596321737445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8832652312200397547824963 13248978468300596321737445)
                    ·
                      refine ⟨2484183462806361810325771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13248978468300596321737445 2484183462806361810325771)
                      ·
                        rfl

theorem cell23_4837930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4837930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837930 prefixEnd_4837930 := by exact prefixLift 4837930
  have htrace : WordTrace (prefixWord ++ tailWord_4837930) baseStart_4837930 baseEnd_4837930 := by
    simpa [prefixWord, tailWord_4837930, baseEnd_4837930] using wordTrace_append hprefix tailTrace_4837930
  have hstable : (prefixWord ++ tailWord_4837930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837930).length < 2 ^ (prefixWord ++ tailWord_4837930).sum := by decide
  have hdescent : baseEnd_4837930 < baseStart_4837930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837936 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 8]
def baseStart_4837936 : Nat := 118140960795 + 4837936 * 2 ^ 59
def prefixEnd_4837936 : Nat := 4983230072969 + 3 ^ 40 * 4837936 * 2
def baseEnd_4837936 : Nat := 276020727076698754094527

theorem tailTrace_4837936 : CollatzResearch.WordTrace tailWord_4837936 prefixEnd_4837936 276020727076698754094527 := by
  unfold tailWord_4837936
  simp only [CollatzResearch.WordTrace]
  refine ⟨88227011100495800266246831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117636014800661067021662441 88227011100495800266246831)
  ·
    refine ⟨132340516650743700399370247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88227011100495800266246831 132340516650743700399370247)
    ·
      refine ⟨198510774976115550599055371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132340516650743700399370247 198510774976115550599055371)
      ·
        refine ⟨297766162464173325898583057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198510774976115550599055371 297766162464173325898583057)
        ·
          refine ⟨223324621848129994423937293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297766162464173325898583057 223324621848129994423937293)
          ·
            refine ⟨83746733193048747908976485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223324621848129994423937293 83746733193048747908976485)
            ·
              refine ⟨15702512473696640232933091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83746733193048747908976485 15702512473696640232933091)
              ·
                refine ⟨23553768710544960349399637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15702512473696640232933091 23553768710544960349399637)
                ·
                  refine ⟨276020727076698754094527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23553768710544960349399637 276020727076698754094527)
                  ·
                    rfl

theorem cell23_4837936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 8].length) (baseStart_4837936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837936 prefixEnd_4837936 := by exact prefixLift 4837936
  have htrace : WordTrace (prefixWord ++ tailWord_4837936) baseStart_4837936 baseEnd_4837936 := by
    simpa [prefixWord, tailWord_4837936, baseEnd_4837936] using wordTrace_append hprefix tailTrace_4837936
  have hstable : (prefixWord ++ tailWord_4837936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837936).length < 2 ^ (prefixWord ++ tailWord_4837936).sum := by decide
  have hdescent : baseEnd_4837936 < baseStart_4837936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4837983 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 1, 5]
def baseStart_4837983 : Nat := 118140960795 + 4837983 * 2 ^ 59
def prefixEnd_4837983 : Nat := 4983230072969 + 3 ^ 40 * 4837983 * 2
def baseEnd_4837983 : Nat := 828070225760350034321009

theorem tailTrace_4837983 : CollatzResearch.WordTrace tailWord_4837983 prefixEnd_4837983 828070225760350034321009 := by
  unfold tailWord_4837983
  simp only [CollatzResearch.WordTrace]
  refine ⟨176455736431821327559454603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117637157621214218372969735 176455736431821327559454603)
  ·
    refine ⟨264683604647731991339181905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176455736431821327559454603 264683604647731991339181905)
    ·
      refine ⟨198512703485798993504386429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264683604647731991339181905 198512703485798993504386429)
      ·
        refine ⟨74442263807174622564144911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198512703485798993504386429 74442263807174622564144911)
        ·
          refine ⟨111663395710761933846217367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74442263807174622564144911 111663395710761933846217367)
          ·
            refine ⟨167495093566142900769326051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111663395710761933846217367 167495093566142900769326051)
            ·
              refine ⟨251242640349214351153989077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167495093566142900769326051 251242640349214351153989077)
              ·
                refine ⟨5888499383184711355171619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 251242640349214351153989077 5888499383184711355171619)
                ·
                  refine ⟨8832749074777067032757429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5888499383184711355171619 8832749074777067032757429)
                  ·
                    refine ⟨828070225760350034321009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8832749074777067032757429 828070225760350034321009)
                    ·
                      rfl

theorem cell23_4837983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 5].length) (baseStart_4837983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4837983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4837983 prefixEnd_4837983 := by exact prefixLift 4837983
  have htrace : WordTrace (prefixWord ++ tailWord_4837983) baseStart_4837983 baseEnd_4837983 := by
    simpa [prefixWord, tailWord_4837983, baseEnd_4837983] using wordTrace_append hprefix tailTrace_4837983
  have hstable : (prefixWord ++ tailWord_4837983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4837983).length < 2 ^ (prefixWord ++ tailWord_4837983).sum := by decide
  have hdescent : baseEnd_4837983 < baseStart_4837983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4837983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838018 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4838018 : Nat := 118140960795 + 4838018 * 2 ^ 59
def prefixEnd_4838018 : Nat := 4983230072969 + 3 ^ 40 * 4838018 * 2
def baseEnd_4838018 : Nat := 2484228649103957466025367

theorem tailTrace_4838018 : CollatzResearch.WordTrace tailWord_4838018 prefixEnd_4838018 2484228649103957466025367 := by
  unfold tailWord_4838018
  simp only [CollatzResearch.WordTrace]
  refine ⟨44114253246673632134244677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117638008657796352357985805 44114253246673632134244677)
  ·
    refine ⟨8271422483751306025170877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44114253246673632134244677 8271422483751306025170877)
    ·
      refine ⟨3101783431406739759439079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8271422483751306025170877 3101783431406739759439079)
      ·
        refine ⟨4652675147110109639158619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101783431406739759439079 4652675147110109639158619)
        ·
          refine ⟨6979012720665164458737929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4652675147110109639158619 6979012720665164458737929)
          ·
            refine ⟨5234259540498873344053447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6979012720665164458737929 5234259540498873344053447)
            ·
              refine ⟨7851389310748310016080171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5234259540498873344053447 7851389310748310016080171)
              ·
                refine ⟨11777083966122465024120257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7851389310748310016080171 11777083966122465024120257)
                ·
                  refine ⟨8832812974591848768090193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11777083966122465024120257 8832812974591848768090193)
                  ·
                    refine ⟨6624609730943886576067645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8832812974591848768090193 6624609730943886576067645)
                    ·
                      refine ⟨2484228649103957466025367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6624609730943886576067645 2484228649103957466025367)
                      ·
                        rfl

theorem cell23_4838018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4838018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838018 prefixEnd_4838018 := by exact prefixLift 4838018
  have htrace : WordTrace (prefixWord ++ tailWord_4838018) baseStart_4838018 baseEnd_4838018 := by
    simpa [prefixWord, tailWord_4838018, baseEnd_4838018] using wordTrace_append hprefix tailTrace_4838018
  have hstable : (prefixWord ++ tailWord_4838018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838018).length < 2 ^ (prefixWord ++ tailWord_4838018).sum := by decide
  have hdescent : baseEnd_4838018 < baseStart_4838018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838020 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_4838020 : Nat := 118140960795 + 4838020 * 2 ^ 59
def prefixEnd_4838020 : Nat := 4983230072969 + 3 ^ 40 * 4838020 * 2
def baseEnd_4838020 : Nat := 2484229676065266458200357

theorem tailTrace_4838020 : CollatzResearch.WordTrace tailWord_4838020 prefixEnd_4838020 2484229676065266458200357 := by
  unfold tailWord_4838020
  simp only [CollatzResearch.WordTrace]
  refine ⟨88228542966343641439275757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117638057288458188585701009 88228542966343641439275757)
  ·
    refine ⟨33085703612378865539728409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88228542966343641439275757 33085703612378865539728409)
    ·
      refine ⟨24814277709284149154796307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33085703612378865539728409 24814277709284149154796307)
      ·
        refine ⟨37221416563926223732194461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24814277709284149154796307 37221416563926223732194461)
        ·
          refine ⟨13958031211472333899572923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37221416563926223732194461 13958031211472333899572923)
          ·
            refine ⟨20937046817208500849359385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13958031211472333899572923 20937046817208500849359385)
            ·
              refine ⟨15702785112906375637019539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20937046817208500849359385 15702785112906375637019539)
              ·
                refine ⟨23554177669359563455529309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15702785112906375637019539 23554177669359563455529309)
                ·
                  refine ⟨8832816626009836295823491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23554177669359563455529309 8832816626009836295823491)
                  ·
                    refine ⟨13249224939014754443735237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8832816626009836295823491 13249224939014754443735237)
                    ·
                      refine ⟨2484229676065266458200357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13249224939014754443735237 2484229676065266458200357)
                      ·
                        rfl

theorem cell23_4838020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_4838020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838020 prefixEnd_4838020 := by exact prefixLift 4838020
  have htrace : WordTrace (prefixWord ++ tailWord_4838020) baseStart_4838020 baseEnd_4838020 := by
    simpa [prefixWord, tailWord_4838020, baseEnd_4838020] using wordTrace_append hprefix tailTrace_4838020
  have hstable : (prefixWord ++ tailWord_4838020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838020).length < 2 ^ (prefixWord ++ tailWord_4838020).sum := by decide
  have hdescent : baseEnd_4838020 < baseStart_4838020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838030 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_4838030 : Nat := 118140960795 + 4838030 * 2 ^ 59
def prefixEnd_4838030 : Nat := 4983230072969 + 3 ^ 40 * 4838030 * 2
def baseEnd_4838030 : Nat := 828078270290603806358437

theorem tailTrace_4838030 : CollatzResearch.WordTrace tailWord_4838030 prefixEnd_4838030 828078270290603806358437 := by
  unfold tailWord_4838030
  simp only [CollatzResearch.WordTrace]
  refine ⟨22057181332831381823301943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117638300441767369724277029 22057181332831381823301943)
  ·
    refine ⟨33085771999247072734952915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22057181332831381823301943 33085771999247072734952915)
    ·
      refine ⟨49628657998870609102429373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33085771999247072734952915 49628657998870609102429373)
      ·
        refine ⟨18610746749576478413411015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49628657998870609102429373 18610746749576478413411015)
        ·
          refine ⟨27916120124364717620116523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18610746749576478413411015 27916120124364717620116523)
          ·
            refine ⟨41874180186547076430174785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27916120124364717620116523 41874180186547076430174785)
            ·
              refine ⟨31405635139910307322631089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41874180186547076430174785 31405635139910307322631089)
              ·
                refine ⟨23554226354932730491973317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31405635139910307322631089 23554226354932730491973317)
                ·
                  refine ⟨4416417441549886967244997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23554226354932730491973317 4416417441549886967244997)
                  ·
                    refine ⟨828078270290603806358437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4416417441549886967244997 828078270290603806358437)
                    ·
                      rfl

theorem cell23_4838030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_4838030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838030 prefixEnd_4838030 := by exact prefixLift 4838030
  have htrace : WordTrace (prefixWord ++ tailWord_4838030) baseStart_4838030 baseEnd_4838030 := by
    simpa [prefixWord, tailWord_4838030, baseEnd_4838030] using wordTrace_append hprefix tailTrace_4838030
  have hstable : (prefixWord ++ tailWord_4838030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838030).length < 2 ^ (prefixWord ++ tailWord_4838030).sum := by decide
  have hdescent : baseEnd_4838030 < baseStart_4838030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838034 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_4838034 : Nat := 118140960795 + 4838034 * 2 ^ 59
def prefixEnd_4838034 : Nat := 4983230072969 + 3 ^ 40 * 4838034 * 2
def baseEnd_4838034 : Nat := 828078954931476467808431

theorem tailTrace_4838034 : CollatzResearch.WordTrace tailWord_4838034 prefixEnd_4838034 828078954931476467808431 := by
  unfold tailWord_4838034
  simp only [CollatzResearch.WordTrace]
  refine ⟨44114399138659140817390289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117638397703091042179707437 44114399138659140817390289)
  ·
    refine ⟨33085799353994355613042717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44114399138659140817390289 33085799353994355613042717)
    ·
      refine ⟨12407174757747883354891019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33085799353994355613042717 12407174757747883354891019)
      ·
        refine ⟨18610762136621825032336529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12407174757747883354891019 18610762136621825032336529)
        ·
          refine ⟨13958071602466368774252397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18610762136621825032336529 13958071602466368774252397)
          ·
            refine ⟨5234276850924888290344649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13958071602466368774252397 5234276850924888290344649)
            ·
              refine ⟨3925707638193666217758487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5234276850924888290344649 3925707638193666217758487)
              ·
                refine ⟨5888561457290499326637731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925707638193666217758487 5888561457290499326637731)
                ·
                  refine ⟨8832842185935748989956597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5888561457290499326637731 8832842185935748989956597)
                  ·
                    refine ⟨828078954931476467808431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8832842185935748989956597 828078954931476467808431)
                    ·
                      rfl

theorem cell23_4838034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_4838034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838034 prefixEnd_4838034 := by exact prefixLift 4838034
  have htrace : WordTrace (prefixWord ++ tailWord_4838034) baseStart_4838034 baseEnd_4838034 := by
    simpa [prefixWord, tailWord_4838034, baseEnd_4838034] using wordTrace_append hprefix tailTrace_4838034
  have hstable : (prefixWord ++ tailWord_4838034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838034).length < 2 ^ (prefixWord ++ tailWord_4838034).sum := by decide
  have hdescent : baseEnd_4838034 < baseStart_4838034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838097 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 1, 3, 2]
def baseStart_4838097 : Nat := 118140960795 + 4838097 * 2 ^ 59
def prefixEnd_4838097 : Nat := 4983230072969 + 3 ^ 40 * 4838097 * 2
def baseEnd_4838097 : Nat := 2484269214075662656937503

theorem tailTrace_4838097 : CollatzResearch.WordTrace tailWord_4838097 prefixEnd_4838097 2484269214075662656937503 := by
  unfold tailWord_4838097
  simp only [CollatzResearch.WordTrace]
  refine ⟨176459894353408325029104545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117639929568938883352736363 176459894353408325029104545)
  ·
    refine ⟨132344920765056243771828409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176459894353408325029104545 132344920765056243771828409)
    ·
      refine ⟨99258690573792182828871307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132344920765056243771828409 99258690573792182828871307)
      ·
        refine ⟨148888035860688274243306961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99258690573792182828871307 148888035860688274243306961)
        ·
          refine ⟨111666026895516205682480221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148888035860688274243306961 111666026895516205682480221)
          ·
            refine ⟨41874760085818577130930083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111666026895516205682480221 41874760085818577130930083)
            ·
              refine ⟨62812140128727865696395125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41874760085818577130930083 62812140128727865696395125)
              ·
                refine ⟨5888638137068237409037043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62812140128727865696395125 5888638137068237409037043)
                ·
                  refine ⟨8832957205602356113555565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5888638137068237409037043 8832957205602356113555565)
                  ·
                    refine ⟨3312358952100883542583337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8832957205602356113555565 3312358952100883542583337)
                    ·
                      refine ⟨2484269214075662656937503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3312358952100883542583337 2484269214075662656937503)
                      ·
                        rfl

theorem cell23_4838097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 3, 2].length) (baseStart_4838097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838097 prefixEnd_4838097 := by exact prefixLift 4838097
  have htrace : WordTrace (prefixWord ++ tailWord_4838097) baseStart_4838097 baseEnd_4838097 := by
    simpa [prefixWord, tailWord_4838097, baseEnd_4838097] using wordTrace_append hprefix tailTrace_4838097
  have hstable : (prefixWord ++ tailWord_4838097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838097).length < 2 ^ (prefixWord ++ tailWord_4838097).sum := by decide
  have hdescent : baseEnd_4838097 < baseStart_4838097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838123 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 4]
def baseStart_4838123 : Nat := 118140960795 + 4838123 * 2 ^ 59
def prefixEnd_4838123 : Nat := 4983230072969 + 3 ^ 40 * 4838123 * 2
def baseEnd_4838123 : Nat := 2484282564572679555212383

theorem tailTrace_4838123 : CollatzResearch.WordTrace tailWord_4838123 prefixEnd_4838123 2484282564572679555212383 := by
  unfold tailWord_4838123
  simp only [CollatzResearch.WordTrace]
  refine ⟨176460842651314131469551023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117640561767542754313034015 176460842651314131469551023)
  ·
    refine ⟨264691263976971197204326535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176460842651314131469551023 264691263976971197204326535)
    ·
      refine ⟨397036895965456795806489803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264691263976971197204326535 397036895965456795806489803)
      ·
        refine ⟨595555343948185193709734705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397036895965456795806489803 595555343948185193709734705)
        ·
          refine ⟨446666507961138895282301029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595555343948185193709734705 446666507961138895282301029)
          ·
            refine ⟨83749970242713542865431443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 446666507961138895282301029 83749970242713542865431443)
            ·
              refine ⟨125624955364070314298147165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83749970242713542865431443 125624955364070314298147165)
              ·
                refine ⟨47109358261526367861805187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125624955364070314298147165 47109358261526367861805187)
                ·
                  refine ⟨70664037392289551792707781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47109358261526367861805187 70664037392289551792707781)
                  ·
                    refine ⟨13249507011054290961132709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70664037392289551792707781 13249507011054290961132709)
                    ·
                      refine ⟨2484282564572679555212383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13249507011054290961132709 2484282564572679555212383)
                      ·
                        rfl

theorem cell23_4838123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 4].length) (baseStart_4838123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838123 prefixEnd_4838123 := by exact prefixLift 4838123
  have htrace : WordTrace (prefixWord ++ tailWord_4838123) baseStart_4838123 baseEnd_4838123 := by
    simpa [prefixWord, tailWord_4838123, baseEnd_4838123] using wordTrace_append hprefix tailTrace_4838123
  have hstable : (prefixWord ++ tailWord_4838123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838123).length < 2 ^ (prefixWord ++ tailWord_4838123).sum := by decide
  have hdescent : baseEnd_4838123 < baseStart_4838123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838130 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_4838130 : Nat := 118140960795 + 4838130 * 2 ^ 59
def prefixEnd_4838130 : Nat := 4983230072969 + 3 ^ 40 * 4838130 * 2
def baseEnd_4838130 : Nat := 2484286158937261027824851

theorem tailTrace_4838130 : CollatzResearch.WordTrace tailWord_4838130 prefixEnd_4838130 2484286158937261027824851 := by
  unfold tailWord_4838130
  simp only [CollatzResearch.WordTrace]
  refine ⟨44115274490572192916263961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117640731974859181110037229 44115274490572192916263961)
  ·
    refine ⟨33086455867929144687197971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44115274490572192916263961 33086455867929144687197971)
    ·
      refine ⟨49629683801893717030796957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33086455867929144687197971 49629683801893717030796957)
      ·
        refine ⟨18611131425710143886548859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49629683801893717030796957 18611131425710143886548859)
        ·
          refine ⟨27916697138565215829823289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18611131425710143886548859 27916697138565215829823289)
          ·
            refine ⟨20937522853923911872367467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27916697138565215829823289 20937522853923911872367467)
            ·
              refine ⟨31406284280885867808551201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20937522853923911872367467 31406284280885867808551201)
              ·
                refine ⟨23554713210664400856413401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31406284280885867808551201 23554713210664400856413401)
                ·
                  refine ⟨17666034907998300642310051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23554713210664400856413401 17666034907998300642310051)
                  ·
                    refine ⟨26499052361997450963465077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17666034907998300642310051 26499052361997450963465077)
                    ·
                      refine ⟨2484286158937261027824851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26499052361997450963465077 2484286158937261027824851)
                      ·
                        rfl

theorem cell23_4838130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_4838130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838130 prefixEnd_4838130 := by exact prefixLift 4838130
  have htrace : WordTrace (prefixWord ++ tailWord_4838130) baseStart_4838130 baseEnd_4838130 := by
    simpa [prefixWord, tailWord_4838130, baseEnd_4838130] using wordTrace_append hprefix tailTrace_4838130
  have hstable : (prefixWord ++ tailWord_4838130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838130).length < 2 ^ (prefixWord ++ tailWord_4838130).sum := by decide
  have hdescent : baseEnd_4838130 < baseStart_4838130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838197 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 2, 5]
def baseStart_4838197 : Nat := 118140960795 + 4838197 * 2 ^ 59
def prefixEnd_4838197 : Nat := 4983230072969 + 3 ^ 40 * 4838197 * 2
def baseEnd_4838197 : Nat := 828106854047037421895681

theorem tailTrace_4838197 : CollatzResearch.WordTrace tailWord_4838197 prefixEnd_4838197 828106854047037421895681 := by
  unfold tailWord_4838197
  simp only [CollatzResearch.WordTrace]
  refine ⟨176463541653046042107744845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117642361102030694738496563 176463541653046042107744845)
  ·
    refine ⟨66173828119892265790404317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176463541653046042107744845 66173828119892265790404317)
    ·
      refine ⟨24815185544959599671401619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66173828119892265790404317 24815185544959599671401619)
      ·
        refine ⟨37222778317439399507102429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24815185544959599671401619 37222778317439399507102429)
        ·
          refine ⟨13958541869039774815163411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37222778317439399507102429 13958541869039774815163411)
          ·
            refine ⟨20937812803559662222745117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13958541869039774815163411 20937812803559662222745117)
            ·
              refine ⟨7851679801334873333529419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20937812803559662222745117 7851679801334873333529419)
              ·
                refine ⟨11777519702002310000294129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7851679801334873333529419 11777519702002310000294129)
                ·
                  refine ⟨8833139776501732500220597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11777519702002310000294129 8833139776501732500220597)
                  ·
                    refine ⟨828106854047037421895681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8833139776501732500220597 828106854047037421895681)
                    ·
                      rfl

theorem cell23_4838197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_4838197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838197 prefixEnd_4838197 := by exact prefixLift 4838197
  have htrace : WordTrace (prefixWord ++ tailWord_4838197) baseStart_4838197 baseEnd_4838197 := by
    simpa [prefixWord, tailWord_4838197, baseEnd_4838197] using wordTrace_append hprefix tailTrace_4838197
  have hstable : (prefixWord ++ tailWord_4838197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838197).length < 2 ^ (prefixWord ++ tailWord_4838197).sum := by decide
  have hdescent : baseEnd_4838197 < baseStart_4838197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838200 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_4838200 : Nat := 118140960795 + 4838200 * 2 ^ 59
def prefixEnd_4838200 : Nat := 4983230072969 + 3 ^ 40 * 4838200 * 2
def baseEnd_4838200 : Nat := 2484322102583075753949529

theorem tailTrace_4838200 : CollatzResearch.WordTrace tailWord_4838200 prefixEnd_4838200 2484322102583075753949529 := by
  unfold tailWord_4838200
  simp only [CollatzResearch.WordTrace]
  refine ⟨88231825536017586810052027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117642434048023449080069369 88231825536017586810052027)
  ·
    refine ⟨132347738304026380215078041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88231825536017586810052027 132347738304026380215078041)
    ·
      refine ⟨99260803728019785161308531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132347738304026380215078041 99260803728019785161308531)
      ·
        refine ⟨148891205592029677741962797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99260803728019785161308531 148891205592029677741962797)
        ·
          refine ⟨55834202097011129153236049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148891205592029677741962797 55834202097011129153236049)
          ·
            refine ⟨41875651572758346864927037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55834202097011129153236049 41875651572758346864927037)
            ·
              refine ⟨15703369339784380074347639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41875651572758346864927037 15703369339784380074347639)
              ·
                refine ⟨23555054009676570111521459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15703369339784380074347639 23555054009676570111521459)
                ·
                  refine ⟨35332581014514855167282189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23555054009676570111521459 35332581014514855167282189)
                  ·
                    refine ⟨13249717880443070687730821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35332581014514855167282189 13249717880443070687730821)
                    ·
                      refine ⟨2484322102583075753949529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13249717880443070687730821 2484322102583075753949529)
                      ·
                        rfl

theorem cell23_4838200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_4838200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838200 prefixEnd_4838200 := by exact prefixLift 4838200
  have htrace : WordTrace (prefixWord ++ tailWord_4838200) baseStart_4838200 baseEnd_4838200 := by
    simpa [prefixWord, tailWord_4838200, baseEnd_4838200] using wordTrace_append hprefix tailTrace_4838200
  have hstable : (prefixWord ++ tailWord_4838200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838200).length < 2 ^ (prefixWord ++ tailWord_4838200).sum := by decide
  have hdescent : baseEnd_4838200 < baseStart_4838200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838212 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4838212 : Nat := 118140960795 + 4838212 * 2 ^ 59
def prefixEnd_4838212 : Nat := 4983230072969 + 3 ^ 40 * 4838212 * 2
def baseEnd_4838212 : Nat := 2484328264350929706999475

theorem tailTrace_4838212 : CollatzResearch.WordTrace tailWord_4838212 prefixEnd_4838212 2484328264350929706999475 := by
  unfold tailWord_4838212
  simp only [CollatzResearch.WordTrace]
  refine ⟨88232044373995849834770445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117642725831994466446360593 88232044373995849834770445)
  ·
    refine ⟨33087016640248443688038917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88232044373995849834770445 33087016640248443688038917)
    ·
      refine ⟨6203815620046583191507297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33087016640248443688038917 6203815620046583191507297)
      ·
        refine ⟨4652861715034937393630473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6203815620046583191507297 4652861715034937393630473)
        ·
          refine ⟨3489646286276203045222855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4652861715034937393630473 3489646286276203045222855)
          ·
            refine ⟨5234469429414304567834283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489646286276203045222855 5234469429414304567834283)
            ·
              refine ⟨7851704144121456851751425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5234469429414304567834283 7851704144121456851751425)
              ·
                refine ⟨5888778108091092638813569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7851704144121456851751425 5888778108091092638813569)
                ·
                  refine ⟨4416583581068319479110177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5888778108091092638813569 4416583581068319479110177)
                  ·
                    refine ⟨3312437685801239609332633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4416583581068319479110177 3312437685801239609332633)
                    ·
                      refine ⟨2484328264350929706999475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3312437685801239609332633 2484328264350929706999475)
                      ·
                        rfl

theorem cell23_4838212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4838212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838212 prefixEnd_4838212 := by exact prefixLift 4838212
  have htrace : WordTrace (prefixWord ++ tailWord_4838212) baseStart_4838212 baseEnd_4838212 := by
    simpa [prefixWord, tailWord_4838212, baseEnd_4838212] using wordTrace_append hprefix tailTrace_4838212
  have hstable : (prefixWord ++ tailWord_4838212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838212).length < 2 ^ (prefixWord ++ tailWord_4838212).sum := by decide
  have hdescent : baseEnd_4838212 < baseStart_4838212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838217 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 2, 4, 2]
def baseStart_4838217 : Nat := 118140960795 + 4838217 * 2 ^ 59
def prefixEnd_4838217 : Nat := 4983230072969 + 3 ^ 40 * 4838217 * 2
def baseEnd_4838217 : Nat := 2484330831754202187436951

theorem tailTrace_4838217 : CollatzResearch.WordTrace tailWord_4838217 prefixEnd_4838217 2484330831754202187436951 := by
  unfold tailWord_4838217
  simp only [CollatzResearch.WordTrace]
  refine ⟨176464271112973585523472905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117642847408649057015648603 176464271112973585523472905)
  ·
    refine ⟨132348203334730189142604679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176464271112973585523472905 132348203334730189142604679)
    ·
      refine ⟨198522305002095283713907019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132348203334730189142604679 198522305002095283713907019)
      ·
        refine ⟨297783457503142925570860529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198522305002095283713907019 297783457503142925570860529)
        ·
          refine ⟨223337593127357194178145397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297783457503142925570860529 223337593127357194178145397)
          ·
            refine ⟨20937899355689736954201131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 223337593127357194178145397 20937899355689736954201131)
            ·
              refine ⟨31406849033534605431301697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20937899355689736954201131 31406849033534605431301697)
              ·
                refine ⟨23555136775150954073476273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31406849033534605431301697 23555136775150954073476273)
                ·
                  refine ⟨17666352581363215555107205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23555136775150954073476273 17666352581363215555107205)
                  ·
                    refine ⟨3312441109005602916582601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17666352581363215555107205 3312441109005602916582601)
                    ·
                      refine ⟨2484330831754202187436951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3312441109005602916582601 2484330831754202187436951)
                      ·
                        rfl

theorem cell23_4838217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 4, 2].length) (baseStart_4838217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838217 prefixEnd_4838217 := by exact prefixLift 4838217
  have htrace : WordTrace (prefixWord ++ tailWord_4838217) baseStart_4838217 baseEnd_4838217 := by
    simpa [prefixWord, tailWord_4838217, baseEnd_4838217] using wordTrace_append hprefix tailTrace_4838217
  have hstable : (prefixWord ++ tailWord_4838217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838217).length < 2 ^ (prefixWord ++ tailWord_4838217).sum := by decide
  have hdescent : baseEnd_4838217 < baseStart_4838217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838261 : List Nat := [1, 3, 4, 1, 1, 2, 3, 3, 1, 4]
def baseStart_4838261 : Nat := 118140960795 + 4838261 * 2 ^ 59
def prefixEnd_4838261 : Nat := 4983230072969 + 3 ^ 40 * 4838261 * 2
def baseEnd_4838261 : Nat := 828117808301000005095583

theorem tailTrace_4838261 : CollatzResearch.WordTrace tailWord_4838261 prefixEnd_4838261 828117808301000005095583 := by
  unfold tailWord_4838261
  simp only [CollatzResearch.WordTrace]
  refine ⟨176465875924814181038074637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117643917283209454025383091 176465875924814181038074637)
  ·
    refine ⟨66174703471805317889277989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176465875924814181038074637 66174703471805317889277989)
    ·
      refine ⟨12407756900963497104239623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66174703471805317889277989 12407756900963497104239623)
      ·
        refine ⟨18611635351445245656359435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12407756900963497104239623 18611635351445245656359435)
        ·
          refine ⟨27917453027167868484539153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18611635351445245656359435 27917453027167868484539153)
          ·
            refine ⟨20938089770375901363404365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27917453027167868484539153 20938089770375901363404365)
            ·
              refine ⟨7851783663890963011276637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20938089770375901363404365 7851783663890963011276637)
              ·
                refine ⟨2944418873959111129228739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7851783663890963011276637 2944418873959111129228739)
                ·
                  refine ⟨4416628310938666693843109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2944418873959111129228739 4416628310938666693843109)
                  ·
                    refine ⟨828117808301000005095583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4416628310938666693843109 828117808301000005095583)
                    ·
                      rfl

theorem cell23_4838261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_4838261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838261 prefixEnd_4838261 := by exact prefixLift 4838261
  have htrace : WordTrace (prefixWord ++ tailWord_4838261) baseStart_4838261 baseEnd_4838261 := by
    simpa [prefixWord, tailWord_4838261, baseEnd_4838261] using wordTrace_append hprefix tailTrace_4838261
  have hstable : (prefixWord ++ tailWord_4838261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838261).length < 2 ^ (prefixWord ++ tailWord_4838261).sum := by decide
  have hdescent : baseEnd_4838261 < baseStart_4838261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838267 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 5, 1, 3]
def baseStart_4838267 : Nat := 118140960795 + 4838267 * 2 ^ 59
def prefixEnd_4838267 : Nat := 4983230072969 + 3 ^ 40 * 4838267 * 2
def baseEnd_4838267 : Nat := 2484356505786926991811721

theorem tailTrace_4838267 : CollatzResearch.WordTrace tailWord_4838267 prefixEnd_4838267 2484356505786926991811721 := by
  unfold tailWord_4838267
  simp only [CollatzResearch.WordTrace]
  refine ⟨176466094762792444062793055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117644063175194962708528703 176466094762792444062793055)
  ·
    refine ⟨264699142144188666094189583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176466094762792444062793055 264699142144188666094189583)
    ·
      refine ⟨397048713216282999141284375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264699142144188666094189583 397048713216282999141284375)
      ·
        refine ⟨595573069824424498711926563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397048713216282999141284375 595573069824424498711926563)
        ·
          refine ⟨893359604736636748067889845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595573069824424498711926563 893359604736636748067889845)
          ·
            refine ⟨83752462944059695131364673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 893359604736636748067889845 83752462944059695131364673)
            ·
              refine ⟨62814347208044771348523505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83752462944059695131364673 62814347208044771348523505)
              ·
                refine ⟨47110760406033578511392629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62814347208044771348523505 47110760406033578511392629)
                ·
                  refine ⟨4416633788065647985443059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47110760406033578511392629 4416633788065647985443059)
                  ·
                    refine ⟨6624950682098471978164589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4416633788065647985443059 6624950682098471978164589)
                    ·
                      refine ⟨2484356505786926991811721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6624950682098471978164589 2484356505786926991811721)
                      ·
                        rfl

theorem cell23_4838267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 1, 3].length) (baseStart_4838267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838267 prefixEnd_4838267 := by exact prefixLift 4838267
  have htrace : WordTrace (prefixWord ++ tailWord_4838267) baseStart_4838267 baseEnd_4838267 := by
    simpa [prefixWord, tailWord_4838267, baseEnd_4838267] using wordTrace_append hprefix tailTrace_4838267
  have hstable : (prefixWord ++ tailWord_4838267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838267).length < 2 ^ (prefixWord ++ tailWord_4838267).sum := by decide
  have hdescent : baseEnd_4838267 < baseStart_4838267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838284 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 3, 1, 3]
def baseStart_4838284 : Nat := 118140960795 + 4838284 * 2 ^ 59
def prefixEnd_4838284 : Nat := 4983230072969 + 3 ^ 40 * 4838284 * 2
def baseEnd_4838284 : Nat := 2484365234958053425299143

theorem tailTrace_4838284 : CollatzResearch.WordTrace tailWord_4838284 prefixEnd_4838284 2484365234958053425299143 := by
  unfold tailWord_4838284
  simp only [CollatzResearch.WordTrace]
  refine ⟨88233357401865427983080953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117644476535820570644107937 88233357401865427983080953)
  ·
    refine ⟨66175018051399070987310715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88233357401865427983080953 66175018051399070987310715)
    ·
      refine ⟨99262527077098606480966073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66175018051399070987310715 99262527077098606480966073)
      ·
        refine ⟨74446895307823954860724555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99262527077098606480966073 74446895307823954860724555)
        ·
          refine ⟨111670342961735932291086833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74446895307823954860724555 111670342961735932291086833)
          ·
            refine ⟨83752757221301949218315125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111670342961735932291086833 83752757221301949218315125)
            ·
              refine ⟨7851820989497057739217043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83752757221301949218315125 7851820989497057739217043)
              ·
                refine ⟨11777731484245586608825565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7851820989497057739217043 11777731484245586608825565)
                ·
                  refine ⟨4416649306592094978309587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11777731484245586608825565 4416649306592094978309587)
                  ·
                    refine ⟨6624973959888142467464381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4416649306592094978309587 6624973959888142467464381)
                    ·
                      refine ⟨2484365234958053425299143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6624973959888142467464381 2484365234958053425299143)
                      ·
                        rfl

theorem cell23_4838284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_4838284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838284 prefixEnd_4838284 := by exact prefixLift 4838284
  have htrace : WordTrace (prefixWord ++ tailWord_4838284) baseStart_4838284 baseEnd_4838284 := by
    simpa [prefixWord, tailWord_4838284, baseEnd_4838284] using wordTrace_append hprefix tailTrace_4838284
  have hstable : (prefixWord ++ tailWord_4838284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838284).length < 2 ^ (prefixWord ++ tailWord_4838284).sum := by decide
  have hdescent : baseEnd_4838284 < baseStart_4838284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838307 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 2, 6, 2]
def baseStart_4838307 : Nat := 118140960795 + 4838307 * 2 ^ 59
def prefixEnd_4838307 : Nat := 4983230072969 + 3 ^ 40 * 4838307 * 2
def baseEnd_4838307 : Nat := 2484377045013106835311537

theorem tailTrace_4838307 : CollatzResearch.WordTrace tailWord_4838307 prefixEnd_4838307 2484377045013106835311537 := by
  unfold tailWord_4838307
  simp only [CollatzResearch.WordTrace]
  refine ⟨176467553682647530894249175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117645035788431687262832783 176467553682647530894249175)
  ·
    refine ⟨264701330523971296341373763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176467553682647530894249175 264701330523971296341373763)
    ·
      refine ⟨397051995785956944512060645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264701330523971296341373763 397051995785956944512060645)
      ·
        refine ⟨74447249209866927096011371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 397051995785956944512060645 74447249209866927096011371)
        ·
          refine ⟨111670873814800390644017057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74447249209866927096011371 111670873814800390644017057)
          ·
            refine ⟨83753155361100292983012793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111670873814800390644017057 83753155361100292983012793)
            ·
              refine ⟨62814866520825219737259595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83753155361100292983012793 62814866520825219737259595)
              ·
                refine ⟨94222299781237829605889393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62814866520825219737259595 94222299781237829605889393)
                ·
                  refine ⟨70666724835928372204417045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94222299781237829605889393 70666724835928372204417045)
                  ·
                    refine ⟨3312502726684142447082049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70666724835928372204417045 3312502726684142447082049)
                    ·
                      refine ⟨2484377045013106835311537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3312502726684142447082049 2484377045013106835311537)
                      ·
                        rfl

theorem cell23_4838307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_4838307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838307 prefixEnd_4838307 := by exact prefixLift 4838307
  have htrace : WordTrace (prefixWord ++ tailWord_4838307) baseStart_4838307 baseEnd_4838307 := by
    simpa [prefixWord, tailWord_4838307, baseEnd_4838307] using wordTrace_append hprefix tailTrace_4838307
  have hstable : (prefixWord ++ tailWord_4838307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838307).length < 2 ^ (prefixWord ++ tailWord_4838307).sum := by decide
  have hdescent : baseEnd_4838307 < baseStart_4838307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838321 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 1, 5]
def baseStart_4838321 : Nat := 118140960795 + 4838321 * 2 ^ 59
def prefixEnd_4838321 : Nat := 4983230072969 + 3 ^ 40 * 4838321 * 2
def baseEnd_4838321 : Nat := 828128077914089926845491

theorem tailTrace_4838321 : CollatzResearch.WordTrace tailWord_4838321 prefixEnd_4838321 828128077914089926845491 := by
  unfold tailWord_4838321
  simp only [CollatzResearch.WordTrace]
  refine ⟨176468064304596811285258817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117645376203064540856839211 176468064304596811285258817)
  ·
    refine ⟨132351048228447608463944113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176468064304596811285258817 132351048228447608463944113)
    ·
      refine ⟨99263286171335706347958085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132351048228447608463944113 99263286171335706347958085)
      ·
        refine ⟨18611866157125444940242141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99263286171335706347958085 18611866157125444940242141)
        ·
          refine ⟨6979449808922041852590803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18611866157125444940242141 6979449808922041852590803)
          ·
            refine ⟨10469174713383062778886205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6979449808922041852590803 10469174713383062778886205)
            ·
              refine ⟨3925940517518648542082327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10469174713383062778886205 3925940517518648542082327)
              ·
                refine ⟨5888910776277972813123491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925940517518648542082327 5888910776277972813123491)
                ·
                  refine ⟨8833366164416959219685237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5888910776277972813123491 8833366164416959219685237)
                  ·
                    refine ⟨828128077914089926845491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8833366164416959219685237 828128077914089926845491)
                    ·
                      rfl

theorem cell23_4838321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_4838321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838321 prefixEnd_4838321 := by exact prefixLift 4838321
  have htrace : WordTrace (prefixWord ++ tailWord_4838321) baseStart_4838321 baseEnd_4838321 := by
    simpa [prefixWord, tailWord_4838321, baseEnd_4838321] using wordTrace_append hprefix tailTrace_4838321
  have hstable : (prefixWord ++ tailWord_4838321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838321).length < 2 ^ (prefixWord ++ tailWord_4838321).sum := by decide
  have hdescent : baseEnd_4838321 < baseStart_4838321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838327 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 5]
def baseStart_4838327 : Nat := 118140960795 + 4838327 * 2 ^ 59
def prefixEnd_4838327 : Nat := 4983230072969 + 3 ^ 40 * 4838327 * 2
def baseEnd_4838327 : Nat := 2484387314626196757061445

theorem tailTrace_4838327 : CollatzResearch.WordTrace tailWord_4838327 prefixEnd_4838327 2484387314626196757061445 := by
  unfold tailWord_4838327
  simp only [CollatzResearch.WordTrace]
  refine ⟨176468283142575074309977235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117645522095050049539984823 176468283142575074309977235)
  ·
    refine ⟨264702424713862611464965853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176468283142575074309977235 264702424713862611464965853)
    ·
      refine ⟨99263409267698479299362195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264702424713862611464965853 99263409267698479299362195)
      ·
        refine ⟨148895113901547718949043293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99263409267698479299362195 148895113901547718949043293)
        ·
          refine ⟨55835667713080394605891235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148895113901547718949043293 55835667713080394605891235)
          ·
            refine ⟨83753501569620591908836853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55835667713080394605891235 83753501569620591908836853)
            ·
              refine ⟨7851890772151930491453455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83753501569620591908836853 7851890772151930491453455)
              ·
                refine ⟨11777836158227895737180183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7851890772151930491453455 11777836158227895737180183)
                ·
                  refine ⟨17666754237341843605770275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11777836158227895737180183 17666754237341843605770275)
                  ·
                    refine ⟨26500131356012765408655413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17666754237341843605770275 26500131356012765408655413)
                    ·
                      refine ⟨2484387314626196757061445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26500131356012765408655413 2484387314626196757061445)
                      ·
                        rfl

theorem cell23_4838327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_4838327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838327 prefixEnd_4838327 := by exact prefixLift 4838327
  have htrace : WordTrace (prefixWord ++ tailWord_4838327) baseStart_4838327 baseEnd_4838327 := by
    simpa [prefixWord, tailWord_4838327, baseEnd_4838327] using wordTrace_append hprefix tailTrace_4838327
  have hstable : (prefixWord ++ tailWord_4838327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838327).length < 2 ^ (prefixWord ++ tailWord_4838327).sum := by decide
  have hdescent : baseEnd_4838327 < baseStart_4838327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838347 : List Nat := [1, 1, 1, 1, 3, 7, 1, 8]
def baseStart_4838347 : Nat := 118140960795 + 4838347 * 2 ^ 59
def prefixEnd_4838347 : Nat := 4983230072969 + 3 ^ 40 * 4838347 * 2
def baseEnd_4838347 : Nat := 92014725342195802918939

theorem tailTrace_4838347 : CollatzResearch.WordTrace tailWord_4838347 prefixEnd_4838347 92014725342195802918939 := by
  unfold tailWord_4838347
  simp only [CollatzResearch.WordTrace]
  refine ⟨176469012602502617725705295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117646008401668411817136863 176469012602502617725705295)
  ·
    refine ⟨264703518903753926588557943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176469012602502617725705295 264703518903753926588557943)
    ·
      refine ⟨397055278355630889882836915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264703518903753926588557943 397055278355630889882836915)
      ·
        refine ⟨595582917533446334824255373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397055278355630889882836915 595582917533446334824255373)
        ·
          refine ⟨223343594075042375559095765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 595582917533446334824255373 223343594075042375559095765)
          ·
            refine ⟨5234615486133805677166307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 223343594075042375559095765 5234615486133805677166307)
            ·
              refine ⟨7851923229200708515749461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5234615486133805677166307 7851923229200708515749461)
              ·
                refine ⟨92014725342195802918939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7851923229200708515749461 92014725342195802918939)
                ·
                  rfl

theorem cell23_4838347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 8].length) (baseStart_4838347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838347 prefixEnd_4838347 := by exact prefixLift 4838347
  have htrace : WordTrace (prefixWord ++ tailWord_4838347) baseStart_4838347 baseEnd_4838347 := by
    simpa [prefixWord, tailWord_4838347, baseEnd_4838347] using wordTrace_append hprefix tailTrace_4838347
  have hstable : (prefixWord ++ tailWord_4838347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838347).length < 2 ^ (prefixWord ++ tailWord_4838347).sum := by decide
  have hdescent : baseEnd_4838347 < baseStart_4838347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838354 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_4838354 : Nat := 118140960795 + 4838354 * 2 ^ 59
def prefixEnd_4838354 : Nat := 4983230072969 + 3 ^ 40 * 4838354 * 2
def baseEnd_4838354 : Nat := 2484401178603868151423821

theorem tailTrace_4838354 : CollatzResearch.WordTrace tailWord_4838354 prefixEnd_4838354 2484401178603868151423821 := by
  unfold tailWord_4838354
  simp only [CollatzResearch.WordTrace]
  refine ⟨44117316978369314480302529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117646178608984838614140077 44117316978369314480302529)
  ·
    refine ⟨33087987733776985860226897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44117316978369314480302529 33087987733776985860226897)
    ·
      refine ⟨24815990800332739395170173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33087987733776985860226897 24815990800332739395170173)
      ·
        refine ⟨9305996550124777273188815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24815990800332739395170173 9305996550124777273188815)
        ·
          refine ⟨13958994825187165909783223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9305996550124777273188815 13958994825187165909783223)
          ·
            refine ⟨20938492237780748864674835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13958994825187165909783223 20938492237780748864674835)
            ·
              refine ⟨31407738356671123297012253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20938492237780748864674835 31407738356671123297012253)
              ·
                refine ⟨11777901883751671236379595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31407738356671123297012253 11777901883751671236379595)
                ·
                  refine ⟨17666852825627506854569393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11777901883751671236379595 17666852825627506854569393)
                  ·
                    refine ⟨13250139619220630140927045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17666852825627506854569393 13250139619220630140927045)
                    ·
                      refine ⟨2484401178603868151423821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13250139619220630140927045 2484401178603868151423821)
                      ·
                        rfl

theorem cell23_4838354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_4838354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838354 prefixEnd_4838354 := by exact prefixLift 4838354
  have htrace : WordTrace (prefixWord ++ tailWord_4838354) baseStart_4838354 baseEnd_4838354 := by
    simpa [prefixWord, tailWord_4838354, baseEnd_4838354] using wordTrace_append hprefix tailTrace_4838354
  have hstable : (prefixWord ++ tailWord_4838354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838354).length < 2 ^ (prefixWord ++ tailWord_4838354).sum := by decide
  have hdescent : baseEnd_4838354 < baseStart_4838354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838358 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_4838358 : Nat := 118140960795 + 4838358 * 2 ^ 59
def prefixEnd_4838358 : Nat := 4983230072969 + 3 ^ 40 * 4838358 * 2
def baseEnd_4838358 : Nat := 2484403232526486135773803

theorem tailTrace_4838358 : CollatzResearch.WordTrace tailWord_4838358 prefixEnd_4838358 2484403232526486135773803 := by
  unfold tailWord_4838358
  simp only [CollatzResearch.WordTrace]
  refine ⟨11029338362841422912772233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117646275870308511069570485 11029338362841422912772233)
  ·
    refine ⟨8272003772131067184579175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11029338362841422912772233 8272003772131067184579175)
    ·
      refine ⟨12408005658196600776868763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8272003772131067184579175 12408005658196600776868763)
      ·
        refine ⟨18612008487294901165303145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12408005658196600776868763 18612008487294901165303145)
        ·
          refine ⟨13959006365471175873977359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18612008487294901165303145 13959006365471175873977359)
          ·
            refine ⟨20938509548206763810966039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13959006365471175873977359 20938509548206763810966039)
            ·
              refine ⟨31407764322310145716449059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20938509548206763810966039 31407764322310145716449059)
              ·
                refine ⟨47111646483465218574673589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31407764322310145716449059 47111646483465218574673589)
                ·
                  refine ⟨4416716857824864241375649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47111646483465218574673589 4416716857824864241375649)
                  ·
                    refine ⟨3312537643368648181031737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4416716857824864241375649 3312537643368648181031737)
                    ·
                      refine ⟨2484403232526486135773803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3312537643368648181031737 2484403232526486135773803)
                      ·
                        rfl

theorem cell23_4838358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_4838358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838358 prefixEnd_4838358 := by exact prefixLift 4838358
  have htrace : WordTrace (prefixWord ++ tailWord_4838358) baseStart_4838358 baseEnd_4838358 := by
    simpa [prefixWord, tailWord_4838358, baseEnd_4838358] using wordTrace_append hprefix tailTrace_4838358
  have hstable : (prefixWord ++ tailWord_4838358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838358).length < 2 ^ (prefixWord ++ tailWord_4838358).sum := by decide
  have hdescent : baseEnd_4838358 < baseStart_4838358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838375 : List Nat := [1, 1, 5, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_4838375 : Nat := 118140960795 + 4838375 * 2 ^ 59
def prefixEnd_4838375 : Nat := 4983230072969 + 3 ^ 40 * 4838375 * 2
def baseEnd_4838375 : Nat := 2484411961697612569261225

theorem tailTrace_4838375 : CollatzResearch.WordTrace tailWord_4838375 prefixEnd_4838375 2484411961697612569261225 := by
  unfold tailWord_4838375
  simp only [CollatzResearch.WordTrace]
  refine ⟨176470033846401178507724579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117646689230934119005149719 176470033846401178507724579)
  ·
    refine ⟨264705050769601767761586869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176470033846401178507724579 264705050769601767761586869)
    ·
      refine ⟨24816098509650165727648769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 264705050769601767761586869 24816098509650165727648769)
      ·
        refine ⟨18612073882237624295736577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24816098509650165727648769 18612073882237624295736577)
        ·
          refine ⟨13959055411678218221802433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18612073882237624295736577 13959055411678218221802433)
          ·
            refine ⟨10469291558758663666351825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13959055411678218221802433 10469291558758663666351825)
            ·
              refine ⟨7851968669068997749763869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10469291558758663666351825 7851968669068997749763869)
              ·
                refine ⟨2944488250900874156161451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7851968669068997749763869 2944488250900874156161451)
                ·
                  refine ⟨4416732376351311234242177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2944488250900874156161451 4416732376351311234242177)
                  ·
                    refine ⟨3312549282263483425681633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4416732376351311234242177 3312549282263483425681633)
                    ·
                      refine ⟨2484411961697612569261225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3312549282263483425681633 2484411961697612569261225)
                      ·
                        rfl

theorem cell23_4838375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_4838375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838375 prefixEnd_4838375 := by exact prefixLift 4838375
  have htrace : WordTrace (prefixWord ++ tailWord_4838375) baseStart_4838375 baseEnd_4838375 := by
    simpa [prefixWord, tailWord_4838375, baseEnd_4838375] using wordTrace_append hprefix tailTrace_4838375
  have hstable : (prefixWord ++ tailWord_4838375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838375).length < 2 ^ (prefixWord ++ tailWord_4838375).sum := by decide
  have hdescent : baseEnd_4838375 < baseStart_4838375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838378 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_4838378 : Nat := 118140960795 + 4838378 * 2 ^ 59
def prefixEnd_4838378 : Nat := 4983230072969 + 3 ^ 40 * 4838378 * 2
def baseEnd_4838378 : Nat := 2484413502139576057523711

theorem tailTrace_4838378 : CollatzResearch.WordTrace tailWord_4838378 prefixEnd_4838378 2484413502139576057523711 := by
  unfold tailWord_4838378
  simp only [CollatzResearch.WordTrace]
  refine ⟨44117535816347577505020947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117646762176926873346722525 44117535816347577505020947)
  ·
    refine ⟨66176303724521366257531421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44117535816347577505020947 66176303724521366257531421)
    ·
      refine ⟨24816113896695512346574283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66176303724521366257531421 24816113896695512346574283)
      ·
        refine ⟨37224170845043268519861425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24816113896695512346574283 37224170845043268519861425)
        ·
          refine ⟨27918128133782451389896069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37224170845043268519861425 27918128133782451389896069)
          ·
            refine ⟨5234649025084209635605513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27918128133782451389896069 5234649025084209635605513)
            ·
              refine ⟨3925986768813157226704135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5234649025084209635605513 3925986768813157226704135)
              ·
                refine ⟨5888980153219735840056203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925986768813157226704135 5888980153219735840056203)
                ·
                  refine ⟨8833470229829603760084305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5888980153219735840056203 8833470229829603760084305)
                  ·
                    refine ⟨6625102672372202820063229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8833470229829603760084305 6625102672372202820063229)
                    ·
                      refine ⟨2484413502139576057523711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6625102672372202820063229 2484413502139576057523711)
                      ·
                        rfl

theorem cell23_4838378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_4838378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838378 prefixEnd_4838378 := by exact prefixLift 4838378
  have htrace : WordTrace (prefixWord ++ tailWord_4838378) baseStart_4838378 baseEnd_4838378 := by
    simpa [prefixWord, tailWord_4838378, baseEnd_4838378] using wordTrace_append hprefix tailTrace_4838378
  have hstable : (prefixWord ++ tailWord_4838378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838378).length < 2 ^ (prefixWord ++ tailWord_4838378).sum := by decide
  have hdescent : baseEnd_4838378 < baseStart_4838378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838407 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 2, 6]
def baseStart_4838407 : Nat := 118140960795 + 4838407 * 2 ^ 59
def prefixEnd_4838407 : Nat := 4983230072969 + 3 ^ 40 * 4838407 * 2
def baseEnd_4838407 : Nat := 828142797692852148020359

theorem tailTrace_4838407 : CollatzResearch.WordTrace tailWord_4838407 prefixEnd_4838407 828142797692852148020359 := by
  unfold tailWord_4838407
  simp only [CollatzResearch.WordTrace]
  refine ⟨176471200982285247972889475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117647467321523498648592983 176471200982285247972889475)
  ·
    refine ⟨264706801473427871959334213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176471200982285247972889475 264706801473427871959334213)
    ·
      refine ⟨49632525276267725992375165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 264706801473427871959334213 49632525276267725992375165)
      ·
        refine ⟨18612196978600397247140687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49632525276267725992375165 18612196978600397247140687)
        ·
          refine ⟨27918295467900595870711031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18612196978600397247140687 27918295467900595870711031)
          ·
            refine ⟨41877443201850893806066547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27918295467900595870711031 41877443201850893806066547)
            ·
              refine ⟨62816164802776340709099821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41877443201850893806066547 62816164802776340709099821)
              ·
                refine ⟨23556061801041127765912433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62816164802776340709099821 23556061801041127765912433)
                ·
                  refine ⟨17667046350780845824434325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23556061801041127765912433 17667046350780845824434325)
                  ·
                    refine ⟨828142797692852148020359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17667046350780845824434325 828142797692852148020359)
                    ·
                      rfl

theorem cell23_4838407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_4838407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838407 prefixEnd_4838407 := by exact prefixLift 4838407
  have htrace : WordTrace (prefixWord ++ tailWord_4838407) baseStart_4838407 baseEnd_4838407 := by
    simpa [prefixWord, tailWord_4838407, baseEnd_4838407] using wordTrace_append hprefix tailTrace_4838407
  have hstable : (prefixWord ++ tailWord_4838407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838407).length < 2 ^ (prefixWord ++ tailWord_4838407).sum := by decide
  have hdescent : baseEnd_4838407 < baseStart_4838407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838408 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 2, 1, 3]
def baseStart_4838408 : Nat := 118140960795 + 4838408 * 2 ^ 59
def prefixEnd_4838408 : Nat := 4983230072969 + 3 ^ 40 * 4838408 * 2
def baseEnd_4838408 : Nat := 2484428906559210940148573

theorem tailTrace_4838408 : CollatzResearch.WordTrace tailWord_4838408 prefixEnd_4838408 2484428906559210940148573 := by
  unfold tailWord_4838408
  simp only [CollatzResearch.WordTrace]
  refine ⟨88235618727640812571837939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117647491636854416762450585 88235618727640812571837939)
  ·
    refine ⟨132353428091461218857756909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88235618727640812571837939 132353428091461218857756909)
    ·
      refine ⟨49632535534297957071658841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132353428091461218857756909 49632535534297957071658841)
      ·
        refine ⟨37224401650723467803744131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49632535534297957071658841 37224401650723467803744131)
        ·
          refine ⟨55836602476085201705616197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37224401650723467803744131 55836602476085201705616197)
          ·
            refine ⟨10469362964265975319803037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55836602476085201705616197 10469362964265975319803037)
            ·
              refine ⟨3926011111599740744926139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10469362964265975319803037 3926011111599740744926139)
              ·
                refine ⟨5889016667399611117389209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3926011111599740744926139 5889016667399611117389209)
                ·
                  refine ⟨4416762500549708338041907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5889016667399611117389209 4416762500549708338041907)
                  ·
                    refine ⟨6625143750824562507062861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4416762500549708338041907 6625143750824562507062861)
                    ·
                      refine ⟨2484428906559210940148573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6625143750824562507062861 2484428906559210940148573)
                      ·
                        rfl

theorem cell23_4838408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_4838408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838408 prefixEnd_4838408 := by exact prefixLift 4838408
  have htrace : WordTrace (prefixWord ++ tailWord_4838408) baseStart_4838408 baseEnd_4838408 := by
    simpa [prefixWord, tailWord_4838408, baseEnd_4838408] using wordTrace_append hprefix tailTrace_4838408
  have hstable : (prefixWord ++ tailWord_4838408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838408).length < 2 ^ (prefixWord ++ tailWord_4838408).sum := by decide
  have hdescent : baseEnd_4838408 < baseStart_4838408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838417 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 3]
def baseStart_4838417 : Nat := 118140960795 + 4838417 * 2 ^ 59
def prefixEnd_4838417 : Nat := 4983230072969 + 3 ^ 40 * 4838417 * 2
def baseEnd_4838417 : Nat := 2484433527885101404936031

theorem tailTrace_4838417 : CollatzResearch.WordTrace tailWord_4838417 prefixEnd_4838417 2484433527885101404936031 := by
  unfold tailWord_4838417
  simp only [CollatzResearch.WordTrace]
  refine ⟨176471565712249019680753505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117647710474832679787169003 176471565712249019680753505)
  ·
    refine ⟨132353674284186764760565129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176471565712249019680753505 132353674284186764760565129)
    ·
      refine ⟨99265255713140073570423847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132353674284186764760565129 99265255713140073570423847)
      ·
        refine ⟨148897883569710110355635771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99265255713140073570423847 148897883569710110355635771)
        ·
          refine ⟨223346825354565165533453657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148897883569710110355635771 223346825354565165533453657)
          ·
            refine ⟨167510119015923874150090243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223346825354565165533453657 167510119015923874150090243)
            ·
              refine ⟨251265178523885811225135365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167510119015923874150090243 251265178523885811225135365)
              ·
                refine ⟨47112220973228589604712881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251265178523885811225135365 47112220973228589604712881)
                ·
                  refine ⟨35334165729921442203534661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47112220973228589604712881 35334165729921442203534661)
                  ·
                    refine ⟨6625156074360270413162749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35334165729921442203534661 6625156074360270413162749)
                    ·
                      refine ⟨2484433527885101404936031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6625156074360270413162749 2484433527885101404936031)
                      ·
                        rfl

theorem cell23_4838417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_4838417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838417 prefixEnd_4838417 := by exact prefixLift 4838417
  have htrace : WordTrace (prefixWord ++ tailWord_4838417) baseStart_4838417 baseEnd_4838417 := by
    simpa [prefixWord, tailWord_4838417, baseEnd_4838417] using wordTrace_append hprefix tailTrace_4838417
  have hstable : (prefixWord ++ tailWord_4838417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838417).length < 2 ^ (prefixWord ++ tailWord_4838417).sum := by decide
  have hdescent : baseEnd_4838417 < baseStart_4838417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838431 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 4, 2, 2]
def baseStart_4838431 : Nat := 118140960795 + 4838431 * 2 ^ 59
def prefixEnd_4838431 : Nat := 4983230072969 + 3 ^ 40 * 4838431 * 2
def baseEnd_4838431 : Nat := 2484440716614264350160967

theorem tailTrace_4838431 : CollatzResearch.WordTrace tailWord_4838431 prefixEnd_4838431 2484440716614264350160967 := by
  unfold tailWord_4838431
  simp only [CollatzResearch.WordTrace]
  refine ⟨176472076334198300071763147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117648050889465533381175431 176472076334198300071763147)
  ·
    refine ⟨264708114501297450107644721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176472076334198300071763147 264708114501297450107644721)
    ·
      refine ⟨198531085875973087580733541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264708114501297450107644721 198531085875973087580733541)
      ·
        refine ⟨37224578601744953921387539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198531085875973087580733541 37224578601744953921387539)
        ·
          refine ⟨55836867902617430882081309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37224578601744953921387539 55836867902617430882081309)
          ·
            refine ⟨20938825463481536580780491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55836867902617430882081309 20938825463481536580780491)
            ·
              refine ⟨31408238195222304871170737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20938825463481536580780491 31408238195222304871170737)
              ·
                refine ⟨23556178646416728653378053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31408238195222304871170737 23556178646416728653378053)
                ·
                  refine ⟨4416783496203136622508385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23556178646416728653378053 4416783496203136622508385)
                  ·
                    refine ⟨3312587622152352466881289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4416783496203136622508385 3312587622152352466881289)
                    ·
                      refine ⟨2484440716614264350160967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3312587622152352466881289 2484440716614264350160967)
                      ·
                        rfl

theorem cell23_4838431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_4838431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838431 prefixEnd_4838431 := by exact prefixLift 4838431
  have htrace : WordTrace (prefixWord ++ tailWord_4838431) baseStart_4838431 baseEnd_4838431 := by
    simpa [prefixWord, tailWord_4838431, baseEnd_4838431] using wordTrace_append hprefix tailTrace_4838431
  have hstable : (prefixWord ++ tailWord_4838431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838431).length < 2 ^ (prefixWord ++ tailWord_4838431).sum := by decide
  have hdescent : baseEnd_4838431 < baseStart_4838431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838434 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_4838434 : Nat := 118140960795 + 4838434 * 2 ^ 59
def prefixEnd_4838434 : Nat := 4983230072969 + 3 ^ 40 * 4838434 * 2
def baseEnd_4838434 : Nat := 2484442257056227838423453

theorem tailTrace_4838434 : CollatzResearch.WordTrace tailWord_4838434 prefixEnd_4838434 2484442257056227838423453 := by
  unfold tailWord_4838434
  simp only [CollatzResearch.WordTrace]
  refine ⟨44118046438296857896030589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117648123835458287722748237 44118046438296857896030589)
  ·
    refine ⟨16544267414361321711011471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44118046438296857896030589 16544267414361321711011471)
    ·
      refine ⟨24816401121541982566517207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16544267414361321711011471 24816401121541982566517207)
      ·
        refine ⟨37224601682312973849775811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24816401121541982566517207 37224601682312973849775811)
        ·
          refine ⟨55836902523469460774663717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37224601682312973849775811 55836902523469460774663717)
          ·
            refine ⟨10469419223150523895249447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55836902523469460774663717 10469419223150523895249447)
            ·
              refine ⟨15704128834725785842874171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10469419223150523895249447 15704128834725785842874171)
              ·
                refine ⟨23556193252088678764311257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15704128834725785842874171 23556193252088678764311257)
                ·
                  refine ⟨17667144939066509073233443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23556193252088678764311257 17667144939066509073233443)
                  ·
                    refine ⟨26500717408599763609850165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17667144939066509073233443 26500717408599763609850165)
                    ·
                      refine ⟨2484442257056227838423453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26500717408599763609850165 2484442257056227838423453)
                      ·
                        rfl

theorem cell23_4838434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_4838434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838434 prefixEnd_4838434 := by exact prefixLift 4838434
  have htrace : WordTrace (prefixWord ++ tailWord_4838434) baseStart_4838434 baseEnd_4838434 := by
    simpa [prefixWord, tailWord_4838434, baseEnd_4838434] using wordTrace_append hprefix tailTrace_4838434
  have hstable : (prefixWord ++ tailWord_4838434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838434).length < 2 ^ (prefixWord ++ tailWord_4838434).sum := by decide
  have hdescent : baseEnd_4838434 < baseStart_4838434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838465 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_4838465 : Nat := 118140960795 + 4838465 * 2 ^ 59
def prefixEnd_4838465 : Nat := 4983230072969 + 3 ^ 40 * 4838465 * 2
def baseEnd_4838465 : Nat := 2484458174956517217135811

theorem tailTrace_4838465 : CollatzResearch.WordTrace tailWord_4838465 prefixEnd_4838465 2484458174956517217135811 := by
  unfold tailWord_4838465
  simp only [CollatzResearch.WordTrace]
  refine ⟨176473316416075123878500849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117648877610716749252333899 176473316416075123878500849)
  ·
    refine ⟨132354987312056342908875637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176473316416075123878500849 132354987312056342908875637)
    ·
      refine ⟨12408280060505282147707091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132354987312056342908875637 12408280060505282147707091)
      ·
        refine ⟨18612420090757923221560637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12408280060505282147707091 18612420090757923221560637)
        ·
          refine ⟨6979657534034221208085239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18612420090757923221560637 6979657534034221208085239)
          ·
            refine ⟨10469486301051331812127859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6979657534034221208085239 10469486301051331812127859)
            ·
              refine ⟨15704229451576997718191789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10469486301051331812127859 15704229451576997718191789)
              ·
                refine ⟨5889086044341374144321921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15704229451576997718191789 5889086044341374144321921)
                ·
                  refine ⟨4416814533256030608241441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5889086044341374144321921 4416814533256030608241441)
                  ·
                    refine ⟨3312610899942022956181081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4416814533256030608241441 3312610899942022956181081)
                    ·
                      refine ⟨2484458174956517217135811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3312610899942022956181081 2484458174956517217135811)
                      ·
                        rfl

theorem cell23_4838465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_4838465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838465 prefixEnd_4838465 := by exact prefixLift 4838465
  have htrace : WordTrace (prefixWord ++ tailWord_4838465) baseStart_4838465 baseEnd_4838465 := by
    simpa [prefixWord, tailWord_4838465, baseEnd_4838465] using wordTrace_append hprefix tailTrace_4838465
  have hstable : (prefixWord ++ tailWord_4838465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838465).length < 2 ^ (prefixWord ++ tailWord_4838465).sum := by decide
  have hdescent : baseEnd_4838465 < baseStart_4838465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838467 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 4, 5]
def baseStart_4838467 : Nat := 118140960795 + 4838467 * 2 ^ 59
def prefixEnd_4838467 : Nat := 4983230072969 + 3 ^ 40 * 4838467 * 2
def baseEnd_4838467 : Nat := 828153067305942069770267

theorem tailTrace_4838467 : CollatzResearch.WordTrace tailWord_4838467 prefixEnd_4838467 828153067305942069770267 := by
  unfold tailWord_4838467
  simp only [CollatzResearch.WordTrace]
  refine ⟨176473389362067878220073655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117648926241378585480049103 176473389362067878220073655)
  ·
    refine ⟨264710084043101817330110483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176473389362067878220073655 264710084043101817330110483)
    ·
      refine ⟨397065126064652725995165725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264710084043101817330110483 397065126064652725995165725)
      ·
        refine ⟨148899422274244772248187147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397065126064652725995165725 148899422274244772248187147)
        ·
          refine ⟨223349133411367158372280721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148899422274244772248187147 223349133411367158372280721)
          ·
            refine ⟨167511850058525368779210541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223349133411367158372280721 167511850058525368779210541)
            ·
              refine ⟨62816943771947013292203953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167511850058525368779210541 62816943771947013292203953)
              ·
                refine ⟨47112707828960259969152965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62816943771947013292203953 47112707828960259969152965)
                ·
                  refine ⟨8833632717930048744216181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47112707828960259969152965 8833632717930048744216181)
                  ·
                    refine ⟨828153067305942069770267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8833632717930048744216181 828153067305942069770267)
                    ·
                      rfl

theorem cell23_4838467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 5].length) (baseStart_4838467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838467 prefixEnd_4838467 := by exact prefixLift 4838467
  have htrace : WordTrace (prefixWord ++ tailWord_4838467) baseStart_4838467 baseEnd_4838467 := by
    simpa [prefixWord, tailWord_4838467, baseEnd_4838467] using wordTrace_append hprefix tailTrace_4838467
  have hstable : (prefixWord ++ tailWord_4838467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838467).length < 2 ^ (prefixWord ++ tailWord_4838467).sum := by decide
  have hdescent : baseEnd_4838467 < baseStart_4838467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838484 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_4838484 : Nat := 118140960795 + 4838484 * 2 ^ 59
def prefixEnd_4838484 : Nat := 4983230072969 + 3 ^ 40 * 4838484 * 2
def baseEnd_4838484 : Nat := 828155977029650880932741

theorem tailTrace_4838484 : CollatzResearch.WordTrace tailWord_4838484 prefixEnd_4838484 828155977029650880932741 := by
  unfold tailWord_4838484
  simp only [CollatzResearch.WordTrace]
  refine ⟨88237004701503145061721253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117649339602004193415628337 88237004701503145061721253)
  ·
    refine ⟨16544438381531839699072735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88237004701503145061721253 16544438381531839699072735)
    ·
      refine ⟨24816657572297759548609103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16544438381531839699072735 24816657572297759548609103)
      ·
        refine ⟨37224986358446639322913655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24816657572297759548609103 37224986358446639322913655)
        ·
          refine ⟨55837479537669958984370483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37224986358446639322913655 55837479537669958984370483)
          ·
            refine ⟨83756219306504938476555725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55837479537669958984370483 83756219306504938476555725)
            ·
              refine ⟨31408582239939351928708397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83756219306504938476555725 31408582239939351928708397)
              ·
                refine ⟨11778218339977256973265649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31408582239939351928708397 11778218339977256973265649)
                ·
                  refine ⟨8833663754982942729949237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11778218339977256973265649 8833663754982942729949237)
                  ·
                    refine ⟨828155977029650880932741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8833663754982942729949237 828155977029650880932741)
                    ·
                      rfl

theorem cell23_4838484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_4838484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838484 prefixEnd_4838484 := by exact prefixLift 4838484
  have htrace : WordTrace (prefixWord ++ tailWord_4838484) baseStart_4838484 baseEnd_4838484 := by
    simpa [prefixWord, tailWord_4838484, baseEnd_4838484] using wordTrace_append hprefix tailTrace_4838484
  have hstable : (prefixWord ++ tailWord_4838484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838484).length < 2 ^ (prefixWord ++ tailWord_4838484).sum := by decide
  have hdescent : baseEnd_4838484 < baseStart_4838484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838524 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_4838524 : Nat := 118140960795 + 4838524 * 2 ^ 59
def prefixEnd_4838524 : Nat := 4983230072969 + 3 ^ 40 * 4838524 * 2
def baseEnd_4838524 : Nat := 2484488470315132486298039

theorem tailTrace_4838524 : CollatzResearch.WordTrace tailWord_4838524 prefixEnd_4838524 2484488470315132486298039 := by
  unfold tailWord_4838524
  simp only [CollatzResearch.WordTrace]
  refine ⟨88237734161430688477449313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117650312215240917969932417 88237734161430688477449313)
  ·
    refine ⟨66178300621073016358086985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88237734161430688477449313 66178300621073016358086985)
    ·
      refine ⟨49633725465804762268565239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66178300621073016358086985 49633725465804762268565239)
      ·
        refine ⟨74450588198707143402847859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49633725465804762268565239 74450588198707143402847859)
        ·
          refine ⟨111675882298060715104271789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74450588198707143402847859 111675882298060715104271789)
          ·
            refine ⟨41878455861772768164101921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111675882298060715104271789 41878455861772768164101921)
            ·
              refine ⟨31408841896329576123076441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41878455861772768164101921 31408841896329576123076441)
              ·
                refine ⟨23556631422247182092307331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31408841896329576123076441 23556631422247182092307331)
                ·
                  refine ⟨35334947133370773138460997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23556631422247182092307331 35334947133370773138460997)
                  ·
                    refine ⟨6625302587507019963461437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35334947133370773138460997 6625302587507019963461437)
                    ·
                      refine ⟨2484488470315132486298039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6625302587507019963461437 2484488470315132486298039)
                      ·
                        rfl

theorem cell23_4838524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_4838524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838524 prefixEnd_4838524 := by exact prefixLift 4838524
  have htrace : WordTrace (prefixWord ++ tailWord_4838524) baseStart_4838524 baseEnd_4838524 := by
    simpa [prefixWord, tailWord_4838524, baseEnd_4838524] using wordTrace_append hprefix tailTrace_4838524
  have hstable : (prefixWord ++ tailWord_4838524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838524).length < 2 ^ (prefixWord ++ tailWord_4838524).sum := by decide
  have hdescent : baseEnd_4838524 < baseStart_4838524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838564 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_4838564 : Nat := 118140960795 + 4838564 * 2 ^ 59
def prefixEnd_4838564 : Nat := 4983230072969 + 3 ^ 40 * 4838564 * 2
def baseEnd_4838564 : Nat := 2484509009541312329797855

theorem tailTrace_4838564 : CollatzResearch.WordTrace tailWord_4838564 prefixEnd_4838564 2484509009541312329797855 := by
  unfold tailWord_4838564
  simp only [CollatzResearch.WordTrace]
  refine ⟨88238463621358231893177373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117651284828477642524236497 88238463621358231893177373)
  ·
    refine ⟨33089423858009336959941515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88238463621358231893177373 33089423858009336959941515)
    ·
      refine ⟨49634135787014005439912273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33089423858009336959941515 49634135787014005439912273)
      ·
        refine ⟨37225601840260504079934205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49634135787014005439912273 37225601840260504079934205)
        ·
          refine ⟨13959600690097689029975327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37225601840260504079934205 13959600690097689029975327)
          ·
            refine ⟨20939401035146533544962991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13959600690097689029975327 20939401035146533544962991)
            ·
              refine ⟨31409101552719800317444487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20939401035146533544962991 31409101552719800317444487)
              ·
                refine ⟨47113652329079700476166731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31409101552719800317444487 47113652329079700476166731)
                ·
                  refine ⟨70670478493619550714250097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47113652329079700476166731 70670478493619550714250097)
                  ·
                    refine ⟨53002858870214663035687573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70670478493619550714250097 53002858870214663035687573)
                    ·
                      refine ⟨2484509009541312329797855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53002858870214663035687573 2484509009541312329797855)
                      ·
                        rfl

theorem cell23_4838564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_4838564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838564 prefixEnd_4838564 := by exact prefixLift 4838564
  have htrace : WordTrace (prefixWord ++ tailWord_4838564) baseStart_4838564 baseEnd_4838564 := by
    simpa [prefixWord, tailWord_4838564, baseEnd_4838564] using wordTrace_append hprefix tailTrace_4838564
  have hstable : (prefixWord ++ tailWord_4838564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838564).length < 2 ^ (prefixWord ++ tailWord_4838564).sum := by decide
  have hdescent : baseEnd_4838564 < baseStart_4838564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838588 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_4838588 : Nat := 118140960795 + 4838588 * 2 ^ 59
def prefixEnd_4838588 : Nat := 4983230072969 + 3 ^ 40 * 4838588 * 2
def baseEnd_4838588 : Nat := 2484521333077020235897745

theorem tailTrace_4838588 : CollatzResearch.WordTrace tailWord_4838588 prefixEnd_4838588 2484521333077020235897745 := by
  unfold tailWord_4838588
  simp only [CollatzResearch.WordTrace]
  refine ⟨88238901297314757942614209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117651868396419677256818945 88238901297314757942614209)
  ·
    refine ⟨66179175972986068456960657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88238901297314757942614209 66179175972986068456960657)
    ·
      refine ⟨49634381979739551342720493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66179175972986068456960657 49634381979739551342720493)
      ·
        refine ⟨18612893242402331753520185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49634381979739551342720493 18612893242402331753520185)
        ·
          refine ⟨13959669931801748815140139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18612893242402331753520185 13959669931801748815140139)
          ·
            refine ⟨20939504897702623222710209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13959669931801748815140139 20939504897702623222710209)
            ·
              refine ⟨15704628673276967417032657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20939504897702623222710209 15704628673276967417032657)
              ·
                refine ⟨11778471504957725562774493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15704628673276967417032657 11778471504957725562774493)
                ·
                  refine ⟨4416926814359147086040435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11778471504957725562774493 4416926814359147086040435)
                  ·
                    refine ⟨6625390221538720629060653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4416926814359147086040435 6625390221538720629060653)
                    ·
                      refine ⟨2484521333077020235897745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6625390221538720629060653 2484521333077020235897745)
                      ·
                        rfl

theorem cell23_4838588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_4838588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838588 prefixEnd_4838588 := by exact prefixLift 4838588
  have htrace : WordTrace (prefixWord ++ tailWord_4838588) baseStart_4838588 baseEnd_4838588 := by
    simpa [prefixWord, tailWord_4838588, baseEnd_4838588] using wordTrace_append hprefix tailTrace_4838588
  have hstable : (prefixWord ++ tailWord_4838588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838588).length < 2 ^ (prefixWord ++ tailWord_4838588).sum := by decide
  have hdescent : baseEnd_4838588 < baseStart_4838588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838624 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 6]
def baseStart_4838624 : Nat := 118140960795 + 4838624 * 2 ^ 59
def prefixEnd_4838624 : Nat := 4983230072969 + 3 ^ 40 * 4838624 * 2
def baseEnd_4838624 : Nat := 2484539818380582095047579

theorem tailTrace_4838624 : CollatzResearch.WordTrace tailWord_4838624 prefixEnd_4838624 2484539818380582095047579 := by
  unfold tailWord_4838624
  simp only [CollatzResearch.WordTrace]
  refine ⟨88239557811249547016769463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117652743748332729355692617 88239557811249547016769463)
  ·
    refine ⟨132359336716874320525154195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88239557811249547016769463 132359336716874320525154195)
    ·
      refine ⟨198539005075311480787731293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132359336716874320525154195 198539005075311480787731293)
      ·
        refine ⟨74452126903241805295399235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198539005075311480787731293 74452126903241805295399235)
        ·
          refine ⟨111678190354862707943098853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74452126903241805295399235 111678190354862707943098853)
          ·
            refine ⟨20939660691536757739331035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111678190354862707943098853 20939660691536757739331035)
            ·
              refine ⟨31409491037305136608996553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20939660691536757739331035 31409491037305136608996553)
              ·
                refine ⟨23557118277978852456747415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31409491037305136608996553 23557118277978852456747415)
                ·
                  refine ⟨35335677416968278685121123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23557118277978852456747415 35335677416968278685121123)
                  ·
                    refine ⟨53003516125452418027681685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35335677416968278685121123 53003516125452418027681685)
                    ·
                      refine ⟨2484539818380582095047579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53003516125452418027681685 2484539818380582095047579)
                      ·
                        rfl

theorem cell23_4838624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_4838624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838624 prefixEnd_4838624 := by exact prefixLift 4838624
  have htrace : WordTrace (prefixWord ++ tailWord_4838624) baseStart_4838624 baseEnd_4838624 := by
    simpa [prefixWord, tailWord_4838624, baseEnd_4838624] using wordTrace_append hprefix tailTrace_4838624
  have hstable : (prefixWord ++ tailWord_4838624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838624).length < 2 ^ (prefixWord ++ tailWord_4838624).sum := by decide
  have hdescent : baseEnd_4838624 < baseStart_4838624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838634 : List Nat := [3, 1, 3, 1, 1, 3, 1, 10]
def baseStart_4838634 : Nat := 118140960795 + 4838634 * 2 ^ 59
def prefixEnd_4838634 : Nat := 4983230072969 + 3 ^ 40 * 4838634 * 2
def baseEnd_4838634 : Nat := 92020183451375076145279

theorem tailTrace_4838634 : CollatzResearch.WordTrace tailWord_4838634 prefixEnd_4838634 92020183451375076145279 := by
  unfold tailWord_4838634
  simp only [CollatzResearch.WordTrace]
  refine ⟨44119870088115716435350739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117652986901641910494268637 44119870088115716435350739)
  ·
    refine ⟨66179805132173574653026109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44119870088115716435350739 66179805132173574653026109)
    ·
      refine ⟨24817426924565090494884791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66179805132173574653026109 24817426924565090494884791)
      ·
        refine ⟨37226140386847635742327187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24817426924565090494884791 37226140386847635742327187)
        ·
          refine ⟨55839210580271453613490781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37226140386847635742327187 55839210580271453613490781)
          ·
            refine ⟨20939703967601795105059043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55839210580271453613490781 20939703967601795105059043)
            ·
              refine ⟨31409555951402692657588565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20939703967601795105059043 31409555951402692657588565)
              ·
                refine ⟨92020183451375076145279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31409555951402692657588565 92020183451375076145279)
                ·
                  rfl

theorem cell23_4838634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 10].length) (baseStart_4838634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838634 prefixEnd_4838634 := by exact prefixLift 4838634
  have htrace : WordTrace (prefixWord ++ tailWord_4838634) baseStart_4838634 baseEnd_4838634 := by
    simpa [prefixWord, tailWord_4838634, baseEnd_4838634] using wordTrace_append hprefix tailTrace_4838634
  have hstable : (prefixWord ++ tailWord_4838634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838634).length < 2 ^ (prefixWord ++ tailWord_4838634).sum := by decide
  have hdescent : baseEnd_4838634 < baseStart_4838634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838661 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 1, 3, 3]
def baseStart_4838661 : Nat := 118140960795 + 4838661 * 2 ^ 59
def prefixEnd_4838661 : Nat := 4983230072969 + 3 ^ 40 * 4838661 * 2
def baseEnd_4838661 : Nat := 2484558817164798450284909

theorem tailTrace_4838661 : CollatzResearch.WordTrace tailWord_4838661 prefixEnd_4838661 2484558817164798450284909 := by
  unfold tailWord_4838661
  simp only [CollatzResearch.WordTrace]
  refine ⟨176480465123365049352635837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117653643415576699568423891 176480465123365049352635837)
  ·
    refine ⟨66180174421261893507238439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176480465123365049352635837 66180174421261893507238439)
    ·
      refine ⟨99270261631892840260857659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66180174421261893507238439 99270261631892840260857659)
      ·
        refine ⟨148905392447839260391286489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99270261631892840260857659 148905392447839260391286489)
        ·
          refine ⟨111679044335879445293464867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148905392447839260391286489 111679044335879445293464867)
          ·
            refine ⟨167518566503819167940197301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111679044335879445293464867 167518566503819167940197301)
            ·
              refine ⟨15704865609733046994393497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167518566503819167940197301 15704865609733046994393497)
              ·
                refine ⟨11778649207299785245795123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15704865609733046994393497 11778649207299785245795123)
                ·
                  refine ⟨17667973810949677868692685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11778649207299785245795123 17667973810949677868692685)
                  ·
                    refine ⟨6625490179106129200759757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17667973810949677868692685 6625490179106129200759757)
                    ·
                      refine ⟨2484558817164798450284909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6625490179106129200759757 2484558817164798450284909)
                      ·
                        rfl

theorem cell23_4838661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_4838661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838661 prefixEnd_4838661 := by exact prefixLift 4838661
  have htrace : WordTrace (prefixWord ++ tailWord_4838661) baseStart_4838661 baseEnd_4838661 := by
    simpa [prefixWord, tailWord_4838661, baseEnd_4838661] using wordTrace_append hprefix tailTrace_4838661
  have hstable : (prefixWord ++ tailWord_4838661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838661).length < 2 ^ (prefixWord ++ tailWord_4838661).sum := by decide
  have hdescent : baseEnd_4838661 < baseStart_4838661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838741 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 7]
def baseStart_4838741 : Nat := 118140960795 + 4838741 * 2 ^ 59
def prefixEnd_4838741 : Nat := 4983230072969 + 3 ^ 40 * 4838741 * 2
def baseEnd_4838741 : Nat := 276066655068573126364949

theorem tailTrace_4838741 : CollatzResearch.WordTrace tailWord_4838741 prefixEnd_4838741 276066655068573126364949 := by
  unfold tailWord_4838741
  simp only [CollatzResearch.WordTrace]
  refine ⟨176483382963075223015548077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117655588642050148677032051 176483382963075223015548077)
  ·
    refine ⟨66181268611153208630830529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176483382963075223015548077 66181268611153208630830529)
    ·
      refine ⟨49635951458364906473122897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66181268611153208630830529 49635951458364906473122897)
      ·
        refine ⟨37226963593773679854842173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49635951458364906473122897 37226963593773679854842173)
        ·
          refine ⟨13960111347665129945565815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37226963593773679854842173 13960111347665129945565815)
          ·
            refine ⟨20940167021497694918348723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13960111347665129945565815 20940167021497694918348723)
            ·
              refine ⟨31410250532246542377523085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20940167021497694918348723 31410250532246542377523085)
              ·
                refine ⟨11778843949592453391571157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31410250532246542377523085 11778843949592453391571157)
                ·
                  refine ⟨276066655068573126364949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11778843949592453391571157 276066655068573126364949)
                  ·
                    rfl

theorem cell23_4838741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_4838741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838741 prefixEnd_4838741 := by exact prefixLift 4838741
  have htrace : WordTrace (prefixWord ++ tailWord_4838741) baseStart_4838741 baseEnd_4838741 := by
    simpa [prefixWord, tailWord_4838741, baseEnd_4838741] using wordTrace_append hprefix tailTrace_4838741
  have hstable : (prefixWord ++ tailWord_4838741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838741).length < 2 ^ (prefixWord ++ tailWord_4838741).sum := by decide
  have hdescent : baseEnd_4838741 < baseStart_4838741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838781 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_4838781 : Nat := 118140960795 + 4838781 * 2 ^ 59
def prefixEnd_4838781 : Nat := 4983230072969 + 3 ^ 40 * 4838781 * 2
def baseEnd_4838781 : Nat := 2484620434843337980784357

theorem tailTrace_4838781 : CollatzResearch.WordTrace tailWord_4838781 prefixEnd_4838781 2484620434843337980784357 := by
  unfold tailWord_4838781
  simp only [CollatzResearch.WordTrace]
  refine ⟨176484841882930309847004197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117656561255286873231336131 176484841882930309847004197)
  ·
    refine ⟨33090907853049433096313287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176484841882930309847004197 33090907853049433096313287)
    ·
      refine ⟨49636361779574149644469931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33090907853049433096313287 49636361779574149644469931)
      ·
        refine ⟨74454542669361224466704897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49636361779574149644469931 74454542669361224466704897)
        ·
          refine ⟨55840907002020918350028673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74454542669361224466704897 55840907002020918350028673)
          ·
            refine ⟨41880680251515688762521505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55840907002020918350028673 41880680251515688762521505)
            ·
              refine ⟨31410510188636766571891129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41880680251515688762521505 31410510188636766571891129)
              ·
                refine ⟨23557882641477574928918347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31410510188636766571891129 23557882641477574928918347)
                ·
                  refine ⟨35336823962216362393377521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23557882641477574928918347 35336823962216362393377521)
                  ·
                    refine ⟨26502617971662271795033141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35336823962216362393377521 26502617971662271795033141)
                    ·
                      refine ⟨2484620434843337980784357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26502617971662271795033141 2484620434843337980784357)
                      ·
                        rfl

theorem cell23_4838781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_4838781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838781 prefixEnd_4838781 := by exact prefixLift 4838781
  have htrace : WordTrace (prefixWord ++ tailWord_4838781) baseStart_4838781 baseEnd_4838781 := by
    simpa [prefixWord, tailWord_4838781, baseEnd_4838781] using wordTrace_append hprefix tailTrace_4838781
  have hstable : (prefixWord ++ tailWord_4838781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838781).length < 2 ^ (prefixWord ++ tailWord_4838781).sum := by decide
  have hdescent : baseEnd_4838781 < baseStart_4838781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838788 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_4838788 : Nat := 118140960795 + 4838788 * 2 ^ 59
def prefixEnd_4838788 : Nat := 4983230072969 + 3 ^ 40 * 4838788 * 2
def baseEnd_4838788 : Nat := 828208009735973151132275

theorem tailTrace_4838788 : CollatzResearch.WordTrace tailWord_4838788 prefixEnd_4838788 828208009735973151132275 := by
  unfold tailWord_4838788
  simp only [CollatzResearch.WordTrace]
  refine ⟨88242548596952475021254509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117656731462603300028339345 88242548596952475021254509)
  ·
    refine ⟨33090955723857178132970441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88242548596952475021254509 33090955723857178132970441)
    ·
      refine ⟨24818216792892883599727831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33090955723857178132970441 24818216792892883599727831)
      ·
        refine ⟨37227325189339325399591747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24818216792892883599727831 37227325189339325399591747)
        ·
          refine ⟨55840987784008988099387621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37227325189339325399591747 55840987784008988099387621)
          ·
            refine ⟨10470185209501685268635179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55840987784008988099387621 10470185209501685268635179)
            ·
              refine ⟨15705277814252527902952769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10470185209501685268635179 15705277814252527902952769)
              ·
                refine ⟨11778958360689395927214577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15705277814252527902952769 11778958360689395927214577)
                ·
                  refine ⟨8834218770517046945410933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11778958360689395927214577 8834218770517046945410933)
                  ·
                    refine ⟨828208009735973151132275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8834218770517046945410933 828208009735973151132275)
                    ·
                      rfl

theorem cell23_4838788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_4838788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838788 prefixEnd_4838788 := by exact prefixLift 4838788
  have htrace : WordTrace (prefixWord ++ tailWord_4838788) baseStart_4838788 baseEnd_4838788 := by
    simpa [prefixWord, tailWord_4838788, baseEnd_4838788] using wordTrace_append hprefix tailTrace_4838788
  have hstable : (prefixWord ++ tailWord_4838788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838788).length < 2 ^ (prefixWord ++ tailWord_4838788).sum := by decide
  have hdescent : baseEnd_4838788 < baseStart_4838788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838828 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 3]
def baseStart_4838828 : Nat := 118140960795 + 4838828 * 2 ^ 59
def prefixEnd_4838828 : Nat := 4983230072969 + 3 ^ 40 * 4838828 * 2
def baseEnd_4838828 : Nat := 2484644568434099296896641

theorem tailTrace_4838828 : CollatzResearch.WordTrace tailWord_4838828 prefixEnd_4838828 2484644568434099296896641 := by
  unfold tailWord_4838828
  simp only [CollatzResearch.WordTrace]
  refine ⟨88243278056880018436982569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117657704075840024582643425 88243278056880018436982569)
  ·
    refine ⟨66182458542660013827736927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88243278056880018436982569 66182458542660013827736927)
    ·
      refine ⟨99273687813990020741605391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66182458542660013827736927 99273687813990020741605391)
      ·
        refine ⟨148910531720985031112408087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99273687813990020741605391 148910531720985031112408087)
        ·
          refine ⟨223365797581477546668612131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148910531720985031112408087 223365797581477546668612131)
          ·
            refine ⟨335048696372216320002918197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223365797581477546668612131 335048696372216320002918197)
            ·
              refine ⟨31410815284895280000273581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 335048696372216320002918197 31410815284895280000273581)
              ·
                refine ⟨11779055731835730000102593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31410815284895280000273581 11779055731835730000102593)
                ·
                  refine ⟨8834291798876797500076945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11779055731835730000102593 8834291798876797500076945)
                  ·
                    refine ⟨6625718849157598125057709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8834291798876797500076945 6625718849157598125057709)
                    ·
                      refine ⟨2484644568434099296896641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6625718849157598125057709 2484644568434099296896641)
                      ·
                        rfl

theorem cell23_4838828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_4838828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838828 prefixEnd_4838828 := by exact prefixLift 4838828
  have htrace : WordTrace (prefixWord ++ tailWord_4838828) baseStart_4838828 baseEnd_4838828 := by
    simpa [prefixWord, tailWord_4838828, baseEnd_4838828] using wordTrace_append hprefix tailTrace_4838828
  have hstable : (prefixWord ++ tailWord_4838828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838828).length < 2 ^ (prefixWord ++ tailWord_4838828).sum := by decide
  have hdescent : baseEnd_4838828 < baseStart_4838828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838891 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 3, 6]
def baseStart_4838891 : Nat := 118140960795 + 4838891 * 2 ^ 59
def prefixEnd_4838891 : Nat := 4983230072969 + 3 ^ 40 * 4838891 * 2
def baseEnd_4838891 : Nat := 828225639238444183469617

theorem tailTrace_4838891 : CollatzResearch.WordTrace tailWord_4838891 prefixEnd_4838891 828225639238444183469617 := by
  unfold tailWord_4838891
  simp only [CollatzResearch.WordTrace]
  refine ⟨176488853912531798633508527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117659235941687865755672351 176488853912531798633508527)
  ·
    refine ⟨264733280868797697950262791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176488853912531798633508527 264733280868797697950262791)
    ·
      refine ⟨397099921303196546925394187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264733280868797697950262791 397099921303196546925394187)
      ·
        refine ⟨595649881954794820388091281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397099921303196546925394187 595649881954794820388091281)
        ·
          refine ⟨446737411466096115291068461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595649881954794820388091281 446737411466096115291068461)
          ·
            refine ⟨167526529299786043234150673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 446737411466096115291068461 167526529299786043234150673)
            ·
              refine ⟨125644896974839532425613005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167526529299786043234150673 125644896974839532425613005)
              ·
                refine ⟨47116836365564824659604877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125644896974839532425613005 47116836365564824659604877)
                ·
                  refine ⟨17668813637086809247351829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47116836365564824659604877 17668813637086809247351829)
                  ·
                    refine ⟨828225639238444183469617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17668813637086809247351829 828225639238444183469617)
                    ·
                      rfl

theorem cell23_4838891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 6].length) (baseStart_4838891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838891 prefixEnd_4838891 := by exact prefixLift 4838891
  have htrace : WordTrace (prefixWord ++ tailWord_4838891) baseStart_4838891 baseEnd_4838891 := by
    simpa [prefixWord, tailWord_4838891, baseEnd_4838891] using wordTrace_append hprefix tailTrace_4838891
  have hstable : (prefixWord ++ tailWord_4838891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838891).length < 2 ^ (prefixWord ++ tailWord_4838891).sum := by decide
  have hdescent : baseEnd_4838891 < baseStart_4838891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838895 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 1, 5]
def baseStart_4838895 : Nat := 118140960795 + 4838895 * 2 ^ 59
def prefixEnd_4838895 : Nat := 4983230072969 + 3 ^ 40 * 4838895 * 2
def baseEnd_4838895 : Nat := 828226323879316844919611

theorem tailTrace_4838895 : CollatzResearch.WordTrace tailWord_4838895 prefixEnd_4838895 828226323879316844919611 := by
  unfold tailWord_4838895
  simp only [CollatzResearch.WordTrace]
  refine ⟨176488999804517307316654139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117659333203011538211102759 176488999804517307316654139)
  ·
    refine ⟨264733499706775960974981209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176488999804517307316654139 264733499706775960974981209)
    ·
      refine ⟨198550124780081970731235907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264733499706775960974981209 198550124780081970731235907)
      ·
        refine ⟨297825187170122956096853861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198550124780081970731235907 297825187170122956096853861)
        ·
          refine ⟨55842222594398054268160099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 297825187170122956096853861 55842222594398054268160099)
          ·
            refine ⟨83763333891597081402240149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55842222594398054268160099 83763333891597081402240149)
            ·
              refine ⟨3926406276168613190730007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83763333891597081402240149 3926406276168613190730007)
              ·
                refine ⟨5889609414252919786095011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3926406276168613190730007 5889609414252919786095011)
                ·
                  refine ⟨8834414121379379679142517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5889609414252919786095011 8834414121379379679142517)
                  ·
                    refine ⟨828226323879316844919611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8834414121379379679142517 828226323879316844919611)
                    ·
                      rfl

theorem cell23_4838895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 5].length) (baseStart_4838895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838895 prefixEnd_4838895 := by exact prefixLift 4838895
  have htrace : WordTrace (prefixWord ++ tailWord_4838895) baseStart_4838895 baseEnd_4838895 := by
    simpa [prefixWord, tailWord_4838895, baseEnd_4838895] using wordTrace_append hprefix tailTrace_4838895
  have hstable : (prefixWord ++ tailWord_4838895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838895).length < 2 ^ (prefixWord ++ tailWord_4838895).sum := by decide
  have hdescent : baseEnd_4838895 < baseStart_4838895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838921 : List Nat := [1, 2, 1, 1, 3, 1, 4, 10]
def baseStart_4838921 : Nat := 118140960795 + 4838921 * 2 ^ 59
def prefixEnd_4838921 : Nat := 4983230072969 + 3 ^ 40 * 4838921 * 2
def baseEnd_4838921 : Nat := 92025641560554349371619

theorem tailTrace_4838921 : CollatzResearch.WordTrace tailWord_4838921 prefixEnd_4838921 92025641560554349371619 := by
  unfold tailWord_4838921
  simp only [CollatzResearch.WordTrace]
  refine ⟨176489948102423113757100617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117659965401615409171400411 176489948102423113757100617)
  ·
    refine ⟨132367461076817335317825463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176489948102423113757100617 132367461076817335317825463)
    ·
      refine ⟨198551191615226002976738195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132367461076817335317825463 198551191615226002976738195)
      ·
        refine ⟨297826787422839004465107293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198551191615226002976738195 297826787422839004465107293)
        ·
          refine ⟨111685045283564626674415235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297826787422839004465107293 111685045283564626674415235)
          ·
            refine ⟨167527567925346940011622853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111685045283564626674415235 167527567925346940011622853)
            ·
              refine ⟨31411418986002551252179285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167527567925346940011622853 31411418986002551252179285)
              ·
                refine ⟨92025641560554349371619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31411418986002551252179285 92025641560554349371619)
                ·
                  rfl

theorem cell23_4838921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 10].length) (baseStart_4838921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838921 prefixEnd_4838921 := by exact prefixLift 4838921
  have htrace : WordTrace (prefixWord ++ tailWord_4838921) baseStart_4838921 baseEnd_4838921 := by
    simpa [prefixWord, tailWord_4838921, baseEnd_4838921] using wordTrace_append hprefix tailTrace_4838921
  have hstable : (prefixWord ++ tailWord_4838921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838921).length < 2 ^ (prefixWord ++ tailWord_4838921).sum := by decide
  have hdescent : baseEnd_4838921 < baseStart_4838921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4838952 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_4838952 : Nat := 118140960795 + 4838952 * 2 ^ 59
def prefixEnd_4838952 : Nat := 4983230072969 + 3 ^ 40 * 4838952 * 2
def baseEnd_4838952 : Nat := 2484708240035256811746071

theorem tailTrace_4838952 : CollatzResearch.WordTrace tailWord_4838952 prefixEnd_4838952 2484708240035256811746071 := by
  unfold tailWord_4838952
  simp only [CollatzResearch.WordTrace]
  refine ⟨88245539382655403025739555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117660719176873870700986073 88245539382655403025739555)
  ·
    refine ⟨132368309073983104538609333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88245539382655403025739555 132368309073983104538609333)
    ·
      refine ⟨12409528975685916050494625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132368309073983104538609333 12409528975685916050494625)
      ·
        refine ⟨9307146731764437037870969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12409528975685916050494625 9307146731764437037870969)
        ·
          refine ⟨6980360048823327778403227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9307146731764437037870969 6980360048823327778403227)
          ·
            refine ⟨10470540073234991667604841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6980360048823327778403227 10470540073234991667604841)
            ·
              refine ⟨7852905054926243750703631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10470540073234991667604841 7852905054926243750703631)
              ·
                refine ⟨11779357582389365626055447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7852905054926243750703631 11779357582389365626055447)
                ·
                  refine ⟨17669036373584048439083171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11779357582389365626055447 17669036373584048439083171)
                  ·
                    refine ⟨26503554560376072658624757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17669036373584048439083171 26503554560376072658624757)
                    ·
                      refine ⟨2484708240035256811746071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26503554560376072658624757 2484708240035256811746071)
                      ·
                        rfl

theorem cell23_4838952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_4838952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4838952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4838952 prefixEnd_4838952 := by exact prefixLift 4838952
  have htrace : WordTrace (prefixWord ++ tailWord_4838952) baseStart_4838952 baseEnd_4838952 := by
    simpa [prefixWord, tailWord_4838952, baseEnd_4838952] using wordTrace_append hprefix tailTrace_4838952
  have hstable : (prefixWord ++ tailWord_4838952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4838952).length < 2 ^ (prefixWord ++ tailWord_4838952).sum := by decide
  have hdescent : baseEnd_4838952 < baseStart_4838952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4838952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839009 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 1, 3, 2]
def baseStart_4839009 : Nat := 118140960795 + 4839009 * 2 ^ 59
def prefixEnd_4839009 : Nat := 4983230072969 + 3 ^ 40 * 4839009 * 2
def baseEnd_4839009 : Nat := 2484737508432563088733309

theorem tailTrace_4839009 : CollatzResearch.WordTrace tailWord_4839009 prefixEnd_4839009 2484737508432563088733309 := by
  unfold tailWord_4839009
  simp only [CollatzResearch.WordTrace]
  refine ⟨176493157726104304786304081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117662105150736203190869387 176493157726104304786304081)
  ·
    refine ⟨132369868294578228589728061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176493157726104304786304081 132369868294578228589728061)
    ·
      refine ⟨49638700610466835721148023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132369868294578228589728061 49638700610466835721148023)
      ·
        refine ⟨74458050915700253581722035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49638700610466835721148023 74458050915700253581722035)
        ·
          refine ⟨111687076373550380372583053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74458050915700253581722035 111687076373550380372583053)
          ·
            refine ⟨41882653640081392639718645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111687076373550380372583053 41882653640081392639718645)
            ·
              refine ⟨3926498778757630559973623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41882653640081392639718645 3926498778757630559973623)
              ·
                refine ⟨5889748168136445839960435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3926498778757630559973623 5889748168136445839960435)
                ·
                  refine ⟨8834622252204668759940653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5889748168136445839960435 8834622252204668759940653)
                  ·
                    refine ⟨3312983344576750784977745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8834622252204668759940653 3312983344576750784977745)
                    ·
                      refine ⟨2484737508432563088733309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3312983344576750784977745 2484737508432563088733309)
                      ·
                        rfl

theorem cell23_4839009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_4839009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839009 prefixEnd_4839009 := by exact prefixLift 4839009
  have htrace : WordTrace (prefixWord ++ tailWord_4839009) baseStart_4839009 baseEnd_4839009 := by
    simpa [prefixWord, tailWord_4839009, baseEnd_4839009] using wordTrace_append hprefix tailTrace_4839009
  have hstable : (prefixWord ++ tailWord_4839009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839009).length < 2 ^ (prefixWord ++ tailWord_4839009).sum := by decide
  have hdescent : baseEnd_4839009 < baseStart_4839009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839060 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_4839060 : Nat := 118140960795 + 4839060 * 2 ^ 59
def prefixEnd_4839060 : Nat := 4983230072969 + 3 ^ 40 * 4839060 * 2
def baseEnd_4839060 : Nat := 2484763695945942389195575

theorem tailTrace_4839060 : CollatzResearch.WordTrace tailWord_4839060 prefixEnd_4839060 2484763695945942389195575 := by
  unfold tailWord_4839060
  simp only [CollatzResearch.WordTrace]
  refine ⟨88247508924459770248205317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117663345232613026997607089 88247508924459770248205317)
  ·
    refine ⟨16546407923336206921538497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88247508924459770248205317 16546407923336206921538497)
    ·
      refine ⟨12409805942502155191153873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16546407923336206921538497 12409805942502155191153873)
      ·
        refine ⟨9307354456876616393365405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12409805942502155191153873 9307354456876616393365405)
        ·
          refine ⟨3490257921328731147512027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9307354456876616393365405 3490257921328731147512027)
          ·
            refine ⟨5235386881993096721268041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3490257921328731147512027 5235386881993096721268041)
            ·
              refine ⟨3926540161494822540951031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5235386881993096721268041 3926540161494822540951031)
              ·
                refine ⟨5889810242242233811426547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3926540161494822540951031 5889810242242233811426547)
                ·
                  refine ⟨8834715363363350717139821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5889810242242233811426547 8834715363363350717139821)
                  ·
                    refine ⟨3313018261261256518927433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8834715363363350717139821 3313018261261256518927433)
                    ·
                      refine ⟨2484763695945942389195575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3313018261261256518927433 2484763695945942389195575)
                      ·
                        rfl

theorem cell23_4839060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_4839060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839060 prefixEnd_4839060 := by exact prefixLift 4839060
  have htrace : WordTrace (prefixWord ++ tailWord_4839060) baseStart_4839060 baseEnd_4839060 := by
    simpa [prefixWord, tailWord_4839060, baseEnd_4839060] using wordTrace_append hprefix tailTrace_4839060
  have hstable : (prefixWord ++ tailWord_4839060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839060).length < 2 ^ (prefixWord ++ tailWord_4839060).sum := by decide
  have hdescent : baseEnd_4839060 < baseStart_4839060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839065 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 1, 7, 2]
def baseStart_4839065 : Nat := 118140960795 + 4839065 * 2 ^ 59
def prefixEnd_4839065 : Nat := 4983230072969 + 3 ^ 40 * 4839065 * 2
def baseEnd_4839065 : Nat := 2484766263349214869633051

theorem tailTrace_4839065 : CollatzResearch.WordTrace tailWord_4839065 prefixEnd_4839065 2484766263349214869633051 := by
  unfold tailWord_4839065
  simp only [CollatzResearch.WordTrace]
  refine ⟨176495200213901426350342649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117663466809267617566895099 176495200213901426350342649)
  ·
    refine ⟨132371400160426069762756987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176495200213901426350342649 132371400160426069762756987)
    ·
      refine ⟨198557100240639104644135481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132371400160426069762756987 198557100240639104644135481)
      ·
        refine ⟨148917825180479328483101611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198557100240639104644135481 148917825180479328483101611)
        ·
          refine ⟨223376737770718992724652417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148917825180479328483101611 223376737770718992724652417)
          ·
            refine ⟨167532553328039244543489313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223376737770718992724652417 167532553328039244543489313)
            ·
              refine ⟨125649414996029433407616985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167532553328039244543489313 125649414996029433407616985)
              ·
                refine ⟨94237061247022075055712739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125649414996029433407616985 94237061247022075055712739)
                ·
                  refine ⟨141355591870533112583569109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94237061247022075055712739 141355591870533112583569109)
                  ·
                    refine ⟨3313021684465619826177401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 141355591870533112583569109 3313021684465619826177401)
                    ·
                      refine ⟨2484766263349214869633051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3313021684465619826177401 2484766263349214869633051)
                      ·
                        rfl

theorem cell23_4839065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 7, 2].length) (baseStart_4839065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839065 prefixEnd_4839065 := by exact prefixLift 4839065
  have htrace : WordTrace (prefixWord ++ tailWord_4839065) baseStart_4839065 baseEnd_4839065 := by
    simpa [prefixWord, tailWord_4839065, baseEnd_4839065] using wordTrace_append hprefix tailTrace_4839065
  have hstable : (prefixWord ++ tailWord_4839065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839065).length < 2 ^ (prefixWord ++ tailWord_4839065).sum := by decide
  have hdescent : baseEnd_4839065 < baseStart_4839065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839085 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_4839085 : Nat := 118140960795 + 4839085 * 2 ^ 59
def prefixEnd_4839085 : Nat := 4983230072969 + 3 ^ 40 * 4839085 * 2
def baseEnd_4839085 : Nat := 2484776532962304791382959

theorem tailTrace_4839085 : CollatzResearch.WordTrace tailWord_4839085 prefixEnd_4839085 2484776532962304791382959 := by
  unfold tailWord_4839085
  simp only [CollatzResearch.WordTrace]
  refine ⟨176495929673828969766070709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117663953115885979844047139 176495929673828969766070709)
  ·
    refine ⟨16546493406921465915569129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176495929673828969766070709 16546493406921465915569129)
    ·
      refine ⟨12409870055191099436676847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16546493406921465915569129 12409870055191099436676847)
      ·
        refine ⟨18614805082786649155015271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12409870055191099436676847 18614805082786649155015271)
        ·
          refine ⟨27922207624179973732522907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18614805082786649155015271 27922207624179973732522907)
          ·
            refine ⟨41883311436269960598784361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27922207624179973732522907 41883311436269960598784361)
            ·
              refine ⟨31412483577202470449088271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41883311436269960598784361 31412483577202470449088271)
              ·
                refine ⟨47118725365803705673632407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31412483577202470449088271 47118725365803705673632407)
                ·
                  refine ⟨70678088048705558510448611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47118725365803705673632407 70678088048705558510448611)
                  ·
                    refine ⟨106017132073058337765672917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70678088048705558510448611 106017132073058337765672917)
                    ·
                      refine ⟨2484776532962304791382959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106017132073058337765672917 2484776532962304791382959)
                      ·
                        rfl

theorem cell23_4839085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_4839085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839085 prefixEnd_4839085 := by exact prefixLift 4839085
  have htrace : WordTrace (prefixWord ++ tailWord_4839085) baseStart_4839085 baseEnd_4839085 := by
    simpa [prefixWord, tailWord_4839085, baseEnd_4839085] using wordTrace_append hprefix tailTrace_4839085
  have hstable : (prefixWord ++ tailWord_4839085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839085).length < 2 ^ (prefixWord ++ tailWord_4839085).sum := by decide
  have hdescent : baseEnd_4839085 < baseStart_4839085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839095 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_4839095 : Nat := 118140960795 + 4839095 * 2 ^ 59
def prefixEnd_4839095 : Nat := 4983230072969 + 3 ^ 40 * 4839095 * 2
def baseEnd_4839095 : Nat := 2484781667768849752257913

theorem tailTrace_4839095 : CollatzResearch.WordTrace tailWord_4839095 prefixEnd_4839095 2484781667768849752257913 := by
  unfold tailWord_4839095
  simp only [CollatzResearch.WordTrace]
  refine ⟨176496294403792741473934739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117664196269195160982623159 176496294403792741473934739)
  ·
    refine ⟨264744441605689112210902109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176496294403792741473934739 264744441605689112210902109)
    ·
      refine ⟨99279165602133417079088291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264744441605689112210902109 99279165602133417079088291)
      ·
        refine ⟨148918748403200125618632437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99279165602133417079088291 148918748403200125618632437)
        ·
          refine ⟨13961132662800011776746791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148918748403200125618632437 13961132662800011776746791)
          ·
            refine ⟨20941698994200017665120187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13961132662800011776746791 20941698994200017665120187)
            ·
              refine ⟨31412548491300026497680281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20941698994200017665120187 31412548491300026497680281)
              ·
                refine ⟨23559411368475019873260211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31412548491300026497680281 23559411368475019873260211)
                ·
                  refine ⟨35339117052712529809890317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23559411368475019873260211 35339117052712529809890317)
                  ·
                    refine ⟨13252168894767198678708869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35339117052712529809890317 13252168894767198678708869)
                    ·
                      refine ⟨2484781667768849752257913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13252168894767198678708869 2484781667768849752257913)
                      ·
                        rfl

theorem cell23_4839095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_4839095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839095 prefixEnd_4839095 := by exact prefixLift 4839095
  have htrace : WordTrace (prefixWord ++ tailWord_4839095) baseStart_4839095 baseEnd_4839095 := by
    simpa [prefixWord, tailWord_4839095, baseEnd_4839095] using wordTrace_append hprefix tailTrace_4839095
  have hstable : (prefixWord ++ tailWord_4839095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839095).length < 2 ^ (prefixWord ++ tailWord_4839095).sum := by decide
  have hdescent : baseEnd_4839095 < baseStart_4839095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839115 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 3]
def baseStart_4839115 : Nat := 118140960795 + 4839115 * 2 ^ 59
def prefixEnd_4839115 : Nat := 4983230072969 + 3 ^ 40 * 4839115 * 2
def baseEnd_4839115 : Nat := 2484791937381939674007821

theorem tailTrace_4839115 : CollatzResearch.WordTrace tailWord_4839115 prefixEnd_4839115 2484791937381939674007821 := by
  unfold tailWord_4839115
  simp only [CollatzResearch.WordTrace]
  refine ⟨176497023863720284889662799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117664682575813523259775199 176497023863720284889662799)
  ·
    refine ⟨264745535795580427334494199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176497023863720284889662799 264745535795580427334494199)
    ·
      refine ⟨397118303693370641001741299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264745535795580427334494199 397118303693370641001741299)
      ·
        refine ⟨595677455540055961502611949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397118303693370641001741299 595677455540055961502611949)
        ·
          refine ⟨223379045827520985563479481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 595677455540055961502611949 223379045827520985563479481)
          ·
            refine ⟨167534284370640739172609611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223379045827520985563479481 167534284370640739172609611)
            ·
              refine ⟨251301426555961108758914417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167534284370640739172609611 251301426555961108758914417)
              ·
                refine ⟨188476069916970831569185813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251301426555961108758914417 188476069916970831569185813)
                ·
                  refine ⟨8834815777358007729805585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 188476069916970831569185813 8834815777358007729805585)
                  ·
                    refine ⟨6626111833018505797354189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8834815777358007729805585 6626111833018505797354189)
                    ·
                      refine ⟨2484791937381939674007821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6626111833018505797354189 2484791937381939674007821)
                      ·
                        rfl

theorem cell23_4839115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 3].length) (baseStart_4839115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839115 prefixEnd_4839115 := by exact prefixLift 4839115
  have htrace : WordTrace (prefixWord ++ tailWord_4839115) baseStart_4839115 baseEnd_4839115 := by
    simpa [prefixWord, tailWord_4839115, baseEnd_4839115] using wordTrace_append hprefix tailTrace_4839115
  have hstable : (prefixWord ++ tailWord_4839115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839115).length < 2 ^ (prefixWord ++ tailWord_4839115).sum := by decide
  have hdescent : baseEnd_4839115 < baseStart_4839115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839126 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_4839126 : Nat := 118140960795 + 4839126 * 2 ^ 59
def prefixEnd_4839126 : Nat := 4983230072969 + 3 ^ 40 * 4839126 * 2
def baseEnd_4839126 : Nat := 828265861889713043656757

theorem tailTrace_4839126 : CollatzResearch.WordTrace tailWord_4839126 prefixEnd_4839126 828265861889713043656757 := by
  unfold tailWord_4839126
  simp only [CollatzResearch.WordTrace]
  refine ⟨11031089066667527110519577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117664950044453622512208821 11031089066667527110519577)
  ·
    refine ⟨8273316800000645332889683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11031089066667527110519577 8273316800000645332889683)
    ·
      refine ⟨12409975200000967999334525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8273316800000645332889683 12409975200000967999334525)
      ·
        refine ⟨4653740700000362999750447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12409975200000967999334525 4653740700000362999750447)
        ·
          refine ⟨6980611050000544499625671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4653740700000362999750447 6980611050000544499625671)
          ·
            refine ⟨10470916575000816749438507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6980611050000544499625671 10470916575000816749438507)
            ·
              refine ⟨15706374862501225124157761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10470916575000816749438507 15706374862501225124157761)
              ·
                refine ⟨11779781146875918843118321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15706374862501225124157761 11779781146875918843118321)
                ·
                  refine ⟨8834835860156939132338741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11779781146875918843118321 8834835860156939132338741)
                  ·
                    refine ⟨828265861889713043656757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8834835860156939132338741 828265861889713043656757)
                    ·
                      rfl

theorem cell23_4839126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_4839126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839126 prefixEnd_4839126 := by exact prefixLift 4839126
  have htrace : WordTrace (prefixWord ++ tailWord_4839126) baseStart_4839126 baseEnd_4839126 := by
    simpa [prefixWord, tailWord_4839126, baseEnd_4839126] using wordTrace_append hprefix tailTrace_4839126
  have hstable : (prefixWord ++ tailWord_4839126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839126).length < 2 ^ (prefixWord ++ tailWord_4839126).sum := by decide
  have hdescent : baseEnd_4839126 < baseStart_4839126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839135 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 6]
def baseStart_4839135 : Nat := 118140960795 + 4839135 * 2 ^ 59
def prefixEnd_4839135 : Nat := 4983230072969 + 3 ^ 40 * 4839135 * 2
def baseEnd_4839135 : Nat := 276089134110558843973081

theorem tailTrace_4839135 : CollatzResearch.WordTrace tailWord_4839135 prefixEnd_4839135 276089134110558843973081 := by
  unfold tailWord_4839135
  simp only [CollatzResearch.WordTrace]
  refine ⟨176497753323647828305390859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117665168882431885536927239 176497753323647828305390859)
  ·
    refine ⟨264746629985471742458086289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176497753323647828305390859 264746629985471742458086289)
    ·
      refine ⟨198559972489103806843564717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264746629985471742458086289 198559972489103806843564717)
      ·
        refine ⟨74459989683413927566336769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198559972489103806843564717 74459989683413927566336769)
        ·
          refine ⟨55844992262560445674752577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74459989683413927566336769 55844992262560445674752577)
          ·
            refine ⟨41883744196920334256064433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55844992262560445674752577 41883744196920334256064433)
            ·
              refine ⟨31412808147690250692048325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41883744196920334256064433 31412808147690250692048325)
              ·
                refine ⟨5889901527691922004759061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31412808147690250692048325 5889901527691922004759061)
                ·
                  refine ⟨276089134110558843973081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5889901527691922004759061 276089134110558843973081)
                  ·
                    rfl

theorem cell23_4839135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 6].length) (baseStart_4839135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839135 prefixEnd_4839135 := by exact prefixLift 4839135
  have htrace : WordTrace (prefixWord ++ tailWord_4839135) baseStart_4839135 baseEnd_4839135 := by
    simpa [prefixWord, tailWord_4839135, baseEnd_4839135] using wordTrace_append hprefix tailTrace_4839135
  have hstable : (prefixWord ++ tailWord_4839135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839135).length < 2 ^ (prefixWord ++ tailWord_4839135).sum := by decide
  have hdescent : baseEnd_4839135 < baseStart_4839135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839162 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3]
def baseStart_4839162 : Nat := 118140960795 + 4839162 * 2 ^ 59
def prefixEnd_4839162 : Nat := 4983230072969 + 3 ^ 40 * 4839162 * 2
def baseEnd_4839162 : Nat := 2484816070972700990120105

theorem tailTrace_4839162 : CollatzResearch.WordTrace tailWord_4839162 prefixEnd_4839162 2484816070972700990120105 := by
  unfold tailWord_4839162
  simp only [CollatzResearch.WordTrace]
  refine ⟨44124684523637502979155935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117665825396366674611082493 44124684523637502979155935)
  ·
    refine ⟨66187026785456254468733903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44124684523637502979155935 66187026785456254468733903)
    ·
      refine ⟨99280540178184381703100855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66187026785456254468733903 99280540178184381703100855)
      ·
        refine ⟨148920810267276572554651283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99280540178184381703100855 148920810267276572554651283)
        ·
          refine ⟨223381215400914858831976925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148920810267276572554651283 223381215400914858831976925)
          ·
            refine ⟨83767955775343072061991347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223381215400914858831976925 83767955775343072061991347)
            ·
              refine ⟨125651933663014608092987021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83767955775343072061991347 125651933663014608092987021)
              ·
                refine ⟨47119475123630478034870133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125651933663014608092987021 47119475123630478034870133)
                ·
                  refine ⟨4417450792840357315769075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47119475123630478034870133 4417450792840357315769075)
                  ·
                    refine ⟨6626176189260535973653613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4417450792840357315769075 6626176189260535973653613)
                    ·
                      refine ⟨2484816070972700990120105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6626176189260535973653613 2484816070972700990120105)
                      ·
                        rfl

theorem cell23_4839162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_4839162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839162 prefixEnd_4839162 := by exact prefixLift 4839162
  have htrace : WordTrace (prefixWord ++ tailWord_4839162) baseStart_4839162 baseEnd_4839162 := by
    simpa [prefixWord, tailWord_4839162, baseEnd_4839162] using wordTrace_append hprefix tailTrace_4839162
  have hstable : (prefixWord ++ tailWord_4839162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839162).length < 2 ^ (prefixWord ++ tailWord_4839162).sum := by decide
  have hdescent : baseEnd_4839162 < baseStart_4839162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839166 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_4839166 : Nat := 118140960795 + 4839166 * 2 ^ 59
def prefixEnd_4839166 : Nat := 4983230072969 + 3 ^ 40 * 4839166 * 2
def baseEnd_4839166 : Nat := 2484818124895318974470087

theorem tailTrace_4839166 : CollatzResearch.WordTrace tailWord_4839166 prefixEnd_4839166 2484818124895318974470087 := by
  unfold tailWord_4839166
  simp only [CollatzResearch.WordTrace]
  refine ⟨22062360498316940074971169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117665922657690347066512901 22062360498316940074971169)
  ·
    refine ⟨16546770373737705056228377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22062360498316940074971169 16546770373737705056228377)
    ·
      refine ⟨12410077780303278792171283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16546770373737705056228377 12410077780303278792171283)
      ·
        refine ⟨18615116670454918188256925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12410077780303278792171283 18615116670454918188256925)
        ·
          refine ⟨6980668751420594320596347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18615116670454918188256925 6980668751420594320596347)
          ·
            refine ⟨10471003127130891480894521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6980668751420594320596347 10471003127130891480894521)
            ·
              refine ⟨7853252345348168610670891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10471003127130891480894521 7853252345348168610670891)
              ·
                refine ⟨11779878518022252916006337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7853252345348168610670891 11779878518022252916006337)
                ·
                  refine ⟨8834908888516689687004753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11779878518022252916006337 8834908888516689687004753)
                  ·
                    refine ⟨6626181666387517265253565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8834908888516689687004753 6626181666387517265253565)
                    ·
                      refine ⟨2484818124895318974470087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6626181666387517265253565 2484818124895318974470087)
                      ·
                        rfl

theorem cell23_4839166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_4839166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839166 prefixEnd_4839166 := by exact prefixLift 4839166
  have htrace : WordTrace (prefixWord ++ tailWord_4839166) baseStart_4839166 baseEnd_4839166 := by
    simpa [prefixWord, tailWord_4839166, baseEnd_4839166] using wordTrace_append hprefix tailTrace_4839166
  have hstable : (prefixWord ++ tailWord_4839166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839166).length < 2 ^ (prefixWord ++ tailWord_4839166).sum := by decide
  have hdescent : baseEnd_4839166 < baseStart_4839166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839182 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_4839182 : Nat := 118140960795 + 4839182 * 2 ^ 59
def prefixEnd_4839182 : Nat := 4983230072969 + 3 ^ 40 * 4839182 * 2
def baseEnd_4839182 : Nat := 828275446861930303956671

theorem tailTrace_4839182 : CollatzResearch.WordTrace tailWord_4839182 prefixEnd_4839182 828275446861930303956671 := by
  unfold tailWord_4839182
  simp only [CollatzResearch.WordTrace]
  refine ⟨22062433444309694416543975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117666311702985036888234533 22062433444309694416543975)
  ·
    refine ⟨33093650166464541624815963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22062433444309694416543975 33093650166464541624815963)
    ·
      refine ⟨49640475249696812437223945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33093650166464541624815963 49640475249696812437223945)
      ·
        refine ⟨37230356437272609327917959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49640475249696812437223945 37230356437272609327917959)
        ·
          refine ⟨55845534655908913991876939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37230356437272609327917959 55845534655908913991876939)
          ·
            refine ⟨83768301983863370987815409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55845534655908913991876939 83768301983863370987815409)
            ·
              refine ⟨62826226487897528240861557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83768301983863370987815409 62826226487897528240861557)
              ·
                refine ⟨5889958733240393272580771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62826226487897528240861557 5889958733240393272580771)
                ·
                  refine ⟨8834938099860589908871157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5889958733240393272580771 8834938099860589908871157)
                  ·
                    refine ⟨828275446861930303956671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8834938099860589908871157 828275446861930303956671)
                    ·
                      rfl

theorem cell23_4839182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_4839182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839182 prefixEnd_4839182 := by exact prefixLift 4839182
  have htrace : WordTrace (prefixWord ++ tailWord_4839182) baseStart_4839182 baseEnd_4839182 := by
    simpa [prefixWord, tailWord_4839182, baseEnd_4839182] using wordTrace_append hprefix tailTrace_4839182
  have hstable : (prefixWord ++ tailWord_4839182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839182).length < 2 ^ (prefixWord ++ tailWord_4839182).sum := by decide
  have hdescent : baseEnd_4839182 < baseStart_4839182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839189 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 2, 3, 2]
def baseStart_4839189 : Nat := 118140960795 + 4839189 * 2 ^ 59
def prefixEnd_4839189 : Nat := 4983230072969 + 3 ^ 40 * 4839189 * 2
def baseEnd_4839189 : Nat := 2484829934950372384482481

theorem tailTrace_4839189 : CollatzResearch.WordTrace tailWord_4839189 prefixEnd_4839189 2484829934950372384482481 := by
  unfold tailWord_4839189
  simp only [CollatzResearch.WordTrace]
  refine ⟨176499722865452195527856621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117666481910301463685237747 176499722865452195527856621)
  ·
    refine ⟨66187396074544573322946233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176499722865452195527856621 66187396074544573322946233)
    ·
      refine ⟨49640547055908429992209675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66187396074544573322946233 49640547055908429992209675)
      ·
        refine ⟨74460820583862644988314513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49640547055908429992209675 74460820583862644988314513)
        ·
          refine ⟨55845615437896983741235885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74460820583862644988314513 55845615437896983741235885)
          ·
            refine ⟨20942105789211368902963457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55845615437896983741235885 20942105789211368902963457)
            ·
              refine ⟨15706579341908526677222593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20942105789211368902963457 15706579341908526677222593)
              ·
                refine ⟨11779934506431395007916945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15706579341908526677222593 11779934506431395007916945)
                ·
                  refine ⟨8834950879823546255937709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11779934506431395007916945 8834950879823546255937709)
                  ·
                    refine ⟨3313106579933829845976641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8834950879823546255937709 3313106579933829845976641)
                    ·
                      refine ⟨2484829934950372384482481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3313106579933829845976641 2484829934950372384482481)
                      ·
                        rfl

theorem cell23_4839189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_4839189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839189 prefixEnd_4839189 := by exact prefixLift 4839189
  have htrace : WordTrace (prefixWord ++ tailWord_4839189) baseStart_4839189 baseEnd_4839189 := by
    simpa [prefixWord, tailWord_4839189, baseEnd_4839189] using wordTrace_append hprefix tailTrace_4839189
  have hstable : (prefixWord ++ tailWord_4839189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839189).length < 2 ^ (prefixWord ++ tailWord_4839189).sum := by decide
  have hdescent : baseEnd_4839189 < baseStart_4839189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839196 : List Nat := [2, 2, 3, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_4839196 : Nat := 118140960795 + 4839196 * 2 ^ 59
def prefixEnd_4839196 : Nat := 4983230072969 + 3 ^ 40 * 4839196 * 2
def baseEnd_4839196 : Nat := 2484833529314953857094949

theorem tailTrace_4839196 : CollatzResearch.WordTrace tailWord_4839196 prefixEnd_4839196 2484833529314953857094949 := by
  unfold tailWord_4839196
  simp only [CollatzResearch.WordTrace]
  refine ⟨88249989088213417861680721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117666652117617890482240961 88249989088213417861680721)
  ·
    refine ⟨66187491816160063396260541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88249989088213417861680721 66187491816160063396260541)
    ·
      refine ⟨24820309431060023773597703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66187491816160063396260541 24820309431060023773597703)
      ·
        refine ⟨37230464146590035660396555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24820309431060023773597703 37230464146590035660396555)
        ·
          refine ⟨55845696219885053490594833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37230464146590035660396555 55845696219885053490594833)
          ·
            refine ⟨41884272164913790117946125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55845696219885053490594833 41884272164913790117946125)
            ·
              refine ⟨15706602061842671294229797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41884272164913790117946125 15706602061842671294229797)
              ·
                refine ⟨2944987886595500867668087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15706602061842671294229797 2944987886595500867668087)
                ·
                  refine ⟨4417481829893251301502131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2944987886595500867668087 4417481829893251301502131)
                  ·
                    refine ⟨6626222744839876952253197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4417481829893251301502131 6626222744839876952253197)
                    ·
                      refine ⟨2484833529314953857094949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6626222744839876952253197 2484833529314953857094949)
                      ·
                        rfl

theorem cell23_4839196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_4839196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839196 prefixEnd_4839196 := by exact prefixLift 4839196
  have htrace : WordTrace (prefixWord ++ tailWord_4839196) baseStart_4839196 baseEnd_4839196 := by
    simpa [prefixWord, tailWord_4839196, baseEnd_4839196] using wordTrace_append hprefix tailTrace_4839196
  have hstable : (prefixWord ++ tailWord_4839196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839196).length < 2 ^ (prefixWord ++ tailWord_4839196).sum := by decide
  have hdescent : baseEnd_4839196 < baseStart_4839196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839202 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_4839202 : Nat := 118140960795 + 4839202 * 2 ^ 59
def prefixEnd_4839202 : Nat := 4983230072969 + 3 ^ 40 * 4839202 * 2
def baseEnd_4839202 : Nat := 2484836610198880833619921

theorem tailTrace_4839202 : CollatzResearch.WordTrace tailWord_4839202 prefixEnd_4839202 2484836610198880833619921 := by
  unfold tailWord_4839202
  simp only [CollatzResearch.WordTrace]
  refine ⟨44125049253601274687019965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117666798009603399165386573 44125049253601274687019965)
  ·
    refine ⟨16546893470100478007632487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44125049253601274687019965 16546893470100478007632487)
    ·
      refine ⟨24820340205150717011448731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16546893470100478007632487 24820340205150717011448731)
      ·
        refine ⟨37230510307726075517173097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24820340205150717011448731 37230510307726075517173097)
        ·
          refine ⟨27922882730794556637879823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37230510307726075517173097 27922882730794556637879823)
          ·
            refine ⟨41884324096191834956819735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27922882730794556637879823 41884324096191834956819735)
            ·
              refine ⟨62826486144287752435229603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41884324096191834956819735 62826486144287752435229603)
              ·
                refine ⟨94239729216431628652844405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62826486144287752435229603 94239729216431628652844405)
                ·
                  refine ⟨8834974614040465186204163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94239729216431628652844405 8834974614040465186204163)
                  ·
                    refine ⟨13252461921060697779306245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8834974614040465186204163 13252461921060697779306245)
                    ·
                      refine ⟨2484836610198880833619921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13252461921060697779306245 2484836610198880833619921)
                      ·
                        rfl

theorem cell23_4839202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_4839202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839202 prefixEnd_4839202 := by exact prefixLift 4839202
  have htrace : WordTrace (prefixWord ++ tailWord_4839202) baseStart_4839202 baseEnd_4839202 := by
    simpa [prefixWord, tailWord_4839202, baseEnd_4839202] using wordTrace_append hprefix tailTrace_4839202
  have hstable : (prefixWord ++ tailWord_4839202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839202).length < 2 ^ (prefixWord ++ tailWord_4839202).sum := by decide
  have hdescent : baseEnd_4839202 < baseStart_4839202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839212 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 1, 6]
def baseStart_4839212 : Nat := 118140960795 + 4839212 * 2 ^ 59
def prefixEnd_4839212 : Nat := 4983230072969 + 3 ^ 40 * 4839212 * 2
def baseEnd_4839212 : Nat := 828280581668475264831625

theorem tailTrace_4839212 : CollatzResearch.WordTrace tailWord_4839212 prefixEnd_4839212 828280581668475264831625 := by
  unfold tailWord_4839212
  simp only [CollatzResearch.WordTrace]
  refine ⟨88250280872184435227971945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117667041162912580303962593 88250280872184435227971945)
  ·
    refine ⟨66187710654138326420978959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88250280872184435227971945 66187710654138326420978959)
    ·
      refine ⟨99281565981207489631468439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66187710654138326420978959 99281565981207489631468439)
      ·
        refine ⟨148922348971811234447202659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99281565981207489631468439 148922348971811234447202659)
        ·
          refine ⟨223383523457716851670803989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148922348971811234447202659 223383523457716851670803989)
          ·
            refine ⟨10471102662080477422068937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 223383523457716851670803989 10471102662080477422068937)
            ·
              refine ⟨7853326996560358066551703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10471102662080477422068937 7853326996560358066551703)
              ·
                refine ⟨11779990494840537099827555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7853326996560358066551703 11779990494840537099827555)
                ·
                  refine ⟨17669985742260805649741333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11779990494840537099827555 17669985742260805649741333)
                  ·
                    refine ⟨828280581668475264831625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17669985742260805649741333 828280581668475264831625)
                    ·
                      rfl

theorem cell23_4839212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_4839212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839212 prefixEnd_4839212 := by exact prefixLift 4839212
  have htrace : WordTrace (prefixWord ++ tailWord_4839212) baseStart_4839212 baseEnd_4839212 := by
    simpa [prefixWord, tailWord_4839212, baseEnd_4839212] using wordTrace_append hprefix tailTrace_4839212
  have hstable : (prefixWord ++ tailWord_4839212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839212).length < 2 ^ (prefixWord ++ tailWord_4839212).sum := by decide
  have hdescent : baseEnd_4839212 < baseStart_4839212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839215 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 4]
def baseStart_4839215 : Nat := 118140960795 + 4839215 * 2 ^ 59
def prefixEnd_4839215 : Nat := 4983230072969 + 3 ^ 40 * 4839215 * 2
def baseEnd_4839215 : Nat := 2484843285447389282757361

theorem tailTrace_4839215 : CollatzResearch.WordTrace tailWord_4839215 prefixEnd_4839215 2484843285447389282757361 := by
  unfold tailWord_4839215
  simp only [CollatzResearch.WordTrace]
  refine ⟨176500671163358001968303099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117667114108905334645535399 176500671163358001968303099)
  ·
    refine ⟨264751006745037002952454649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176500671163358001968303099 264751006745037002952454649)
    ·
      refine ⟨198563255058777752214340987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264751006745037002952454649 198563255058777752214340987)
      ·
        refine ⟨297844882588166628321511481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198563255058777752214340987 297844882588166628321511481)
        ·
          refine ⟨223383661941124971241133611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297844882588166628321511481 223383661941124971241133611)
          ·
            refine ⟨335075492911687456861700417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223383661941124971241133611 335075492911687456861700417)
            ·
              refine ⟨251306619683765592646275313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335075492911687456861700417 251306619683765592646275313)
              ·
                refine ⟨188479964762824194484706485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251306619683765592646275313 188479964762824194484706485)
                ·
                  refine ⟨17669996696514768232941233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188479964762824194484706485 17669996696514768232941233)
                  ·
                    refine ⟨13252497522386076174705925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17669996696514768232941233 13252497522386076174705925)
                    ·
                      refine ⟨2484843285447389282757361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13252497522386076174705925 2484843285447389282757361)
                      ·
                        rfl

theorem cell23_4839215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_4839215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839215 prefixEnd_4839215 := by exact prefixLift 4839215
  have htrace : WordTrace (prefixWord ++ tailWord_4839215) baseStart_4839215 baseEnd_4839215 := by
    simpa [prefixWord, tailWord_4839215, baseEnd_4839215] using wordTrace_append hprefix tailTrace_4839215
  have hstable : (prefixWord ++ tailWord_4839215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839215).length < 2 ^ (prefixWord ++ tailWord_4839215).sum := by decide
  have hdescent : baseEnd_4839215 < baseStart_4839215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839253 : List Nat := [1, 3, 2, 2, 2, 2, 2, 4, 1, 2, 2]
def baseStart_4839253 : Nat := 118140960795 + 4839253 * 2 ^ 59
def prefixEnd_4839253 : Nat := 4983230072969 + 3 ^ 40 * 4839253 * 2
def baseEnd_4839253 : Nat := 2484862797712260134082187

theorem tailTrace_4839253 : CollatzResearch.WordTrace tailWord_4839253 prefixEnd_4839253 2484862797712260134082187 := by
  unfold tailWord_4839253
  simp only [CollatzResearch.WordTrace]
  refine ⟨176502057137220334458186413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117668038091480222972124275 176502057137220334458186413)
  ·
    refine ⟨66188271426457625421819905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176502057137220334458186413 66188271426457625421819905)
    ·
      refine ⟨49641203569843219066364929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66188271426457625421819905 49641203569843219066364929)
      ·
        refine ⟨37230902677382414299773697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49641203569843219066364929 37230902677382414299773697)
        ·
          refine ⟨27923177008036810724830273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37230902677382414299773697 27923177008036810724830273)
          ·
            refine ⟨20942382756027608043622705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27923177008036810724830273 20942382756027608043622705)
            ·
              refine ⟨15706787067020706032717029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20942382756027608043622705 15706787067020706032717029)
              ·
                refine ⟨2945022575066382381134443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15706787067020706032717029 2945022575066382381134443)
                ·
                  refine ⟨4417533862599573571701665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945022575066382381134443 4417533862599573571701665)
                  ·
                    refine ⟨3313150396949680178776249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4417533862599573571701665 3313150396949680178776249)
                    ·
                      refine ⟨2484862797712260134082187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3313150396949680178776249 2484862797712260134082187)
                      ·
                        rfl

theorem cell23_4839253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_4839253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839253 prefixEnd_4839253 := by exact prefixLift 4839253
  have htrace : WordTrace (prefixWord ++ tailWord_4839253) baseStart_4839253 baseEnd_4839253 := by
    simpa [prefixWord, tailWord_4839253, baseEnd_4839253] using wordTrace_append hprefix tailTrace_4839253
  have hstable : (prefixWord ++ tailWord_4839253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839253).length < 2 ^ (prefixWord ++ tailWord_4839253).sum := by decide
  have hdescent : baseEnd_4839253 < baseStart_4839253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839266 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_4839266 : Nat := 118140960795 + 4839266 * 2 ^ 59
def prefixEnd_4839266 : Nat := 4983230072969 + 3 ^ 40 * 4839266 * 2
def baseEnd_4839266 : Nat := 2484869472960768583219627

theorem tailTrace_4839266 : CollatzResearch.WordTrace tailWord_4839266 prefixEnd_4839266 2484869472960768583219627 := by
  unfold tailWord_4839266
  simp only [CollatzResearch.WordTrace]
  refine ⟨44125632821543309419602413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117668354190782158452273101 44125632821543309419602413)
  ·
    refine ⟨16547112308078741032350905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44125632821543309419602413 16547112308078741032350905)
    ·
      refine ⟨12410334231059055774263179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16547112308078741032350905 12410334231059055774263179)
      ·
        refine ⟨18615501346588583661394769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12410334231059055774263179 18615501346588583661394769)
        ·
          refine ⟨13961626009941437746046077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18615501346588583661394769 13961626009941437746046077)
          ·
            refine ⟨5235609753728039154767279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13961626009941437746046077 5235609753728039154767279)
            ·
              refine ⟨7853414630592058732150919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5235609753728039154767279 7853414630592058732150919)
              ·
                refine ⟨11780121945888088098226379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7853414630592058732150919 11780121945888088098226379)
                ·
                  refine ⟨17670182918832132147339569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11780121945888088098226379 17670182918832132147339569)
                  ·
                    refine ⟨13252637189124099110504677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17670182918832132147339569 13252637189124099110504677)
                    ·
                      refine ⟨2484869472960768583219627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13252637189124099110504677 2484869472960768583219627)
                      ·
                        rfl

theorem cell23_4839266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_4839266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839266 prefixEnd_4839266 := by exact prefixLift 4839266
  have htrace : WordTrace (prefixWord ++ tailWord_4839266) baseStart_4839266 baseEnd_4839266 := by
    simpa [prefixWord, tailWord_4839266, baseEnd_4839266] using wordTrace_append hprefix tailTrace_4839266
  have hstable : (prefixWord ++ tailWord_4839266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839266).length < 2 ^ (prefixWord ++ tailWord_4839266).sum := by decide
  have hdescent : baseEnd_4839266 < baseStart_4839266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839330 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_4839330 : Nat := 118140960795 + 4839330 * 2 ^ 59
def prefixEnd_4839330 : Nat := 4983230072969 + 3 ^ 40 * 4839330 * 2
def baseEnd_4839330 : Nat := 2484902335722656332819333

theorem tailTrace_4839330 : CollatzResearch.WordTrace tailWord_4839330 prefixEnd_4839330 2484902335722656332819333 := by
  unfold tailWord_4839330
  simp only [CollatzResearch.WordTrace]
  refine ⟨44126216389485344152184861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117669910371960917739159629 44126216389485344152184861)
  ·
    refine ⟨16547331146057004057069323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44126216389485344152184861 16547331146057004057069323)
    ·
      refine ⟨24820996719085506085603985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16547331146057004057069323 24820996719085506085603985)
      ·
        refine ⟨18615747539314129564202989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24820996719085506085603985 18615747539314129564202989)
        ·
          refine ⟨6980905327242798586576121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18615747539314129564202989 6980905327242798586576121)
          ·
            refine ⟨5235678995432098939932091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6980905327242798586576121 5235678995432098939932091)
            ·
              refine ⟨7853518493148148409898137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5235678995432098939932091 7853518493148148409898137)
              ·
                refine ⟨5890138869861111307423603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7853518493148148409898137 5890138869861111307423603)
                ·
                  refine ⟨8835208304791666961135405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5890138869861111307423603 8835208304791666961135405)
                  ·
                    refine ⟨3313203114296875110425777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8835208304791666961135405 3313203114296875110425777)
                    ·
                      refine ⟨2484902335722656332819333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3313203114296875110425777 2484902335722656332819333)
                      ·
                        rfl

theorem cell23_4839330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_4839330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839330 prefixEnd_4839330 := by exact prefixLift 4839330
  have htrace : WordTrace (prefixWord ++ tailWord_4839330) baseStart_4839330 baseEnd_4839330 := by
    simpa [prefixWord, tailWord_4839330, baseEnd_4839330] using wordTrace_append hprefix tailTrace_4839330
  have hstable : (prefixWord ++ tailWord_4839330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839330).length < 2 ^ (prefixWord ++ tailWord_4839330).sum := by decide
  have hdescent : baseEnd_4839330 < baseStart_4839330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839419 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 3]
def baseStart_4839419 : Nat := 118140960795 + 4839419 * 2 ^ 59
def prefixEnd_4839419 : Nat := 4983230072969 + 3 ^ 40 * 4839419 * 2
def baseEnd_4839419 : Nat := 2484948035500906484606423

theorem tailTrace_4839419 : CollatzResearch.WordTrace tailWord_4839419 prefixEnd_4839419 2484948035500906484606423 := by
  unfold tailWord_4839419
  simp only [CollatzResearch.WordTrace]
  refine ⟨176508111654618944808729311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117672074436412629872486207 176508111654618944808729311)
  ·
    refine ⟨264762167481928417213093967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176508111654618944808729311 264762167481928417213093967)
    ·
      refine ⟨397143251222892625819640951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264762167481928417213093967 397143251222892625819640951)
      ·
        refine ⟨595714876834338938729461427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397143251222892625819640951 595714876834338938729461427)
        ·
          refine ⟨893572315251508408094192141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595714876834338938729461427 893572315251508408094192141)
          ·
            refine ⟨335089618219315653035322053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 893572315251508408094192141 335089618219315653035322053)
            ·
              refine ⟨62829303416121684944122885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 335089618219315653035322053 62829303416121684944122885)
              ·
                refine ⟨11780494390522815927023041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62829303416121684944122885 11780494390522815927023041)
                ·
                  refine ⟨8835370792892111945267281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11780494390522815927023041 8835370792892111945267281)
                  ·
                    refine ⟨6626528094669083958950461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8835370792892111945267281 6626528094669083958950461)
                    ·
                      refine ⟨2484948035500906484606423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6626528094669083958950461 2484948035500906484606423)
                      ·
                        rfl

theorem cell23_4839419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 3].length) (baseStart_4839419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839419 prefixEnd_4839419 := by exact prefixLift 4839419
  have htrace : WordTrace (prefixWord ++ tailWord_4839419) baseStart_4839419 baseEnd_4839419 := by
    simpa [prefixWord, tailWord_4839419, baseEnd_4839419] using wordTrace_append hprefix tailTrace_4839419
  have hstable : (prefixWord ++ tailWord_4839419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839419).length < 2 ^ (prefixWord ++ tailWord_4839419).sum := by decide
  have hdescent : baseEnd_4839419 < baseStart_4839419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839516 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_4839516 : Nat := 118140960795 + 4839516 * 2 ^ 59
def prefixEnd_4839516 : Nat := 4983230072969 + 3 ^ 40 * 4839516 * 2
def baseEnd_4839516 : Nat := 828332614374797535031159

theorem tailTrace_4839516 : CollatzResearch.WordTrace tailWord_4839516 prefixEnd_4839516 828332614374797535031159 := by
  unfold tailWord_4839516
  simp only [CollatzResearch.WordTrace]
  refine ⟨88255824767633765187505201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117674433023511686916673601 88255824767633765187505201)
  ·
    refine ⟨66191868575725323890628901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88255824767633765187505201 66191868575725323890628901)
    ·
      refine ⟨12410975357948498229492919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66191868575725323890628901 12410975357948498229492919)
      ·
        refine ⟨18616463036922747344239379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12410975357948498229492919 18616463036922747344239379)
        ·
          refine ⟨27924694555384121016359069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18616463036922747344239379 27924694555384121016359069)
          ·
            refine ⟨10471760458269045381134651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27924694555384121016359069 10471760458269045381134651)
            ·
              refine ⟨15707640687403568071701977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10471760458269045381134651 15707640687403568071701977)
              ·
                refine ⟨11780730515552676053776483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15707640687403568071701977 11780730515552676053776483)
                ·
                  refine ⟨17671095773329014080664725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11780730515552676053776483 17671095773329014080664725)
                  ·
                    refine ⟨828332614374797535031159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17671095773329014080664725 828332614374797535031159)
                    ·
                      rfl

theorem cell23_4839516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_4839516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839516 prefixEnd_4839516 := by exact prefixLift 4839516
  have htrace : WordTrace (prefixWord ++ tailWord_4839516) baseStart_4839516 baseEnd_4839516 := by
    simpa [prefixWord, tailWord_4839516, baseEnd_4839516] using wordTrace_append hprefix tailTrace_4839516
  have hstable : (prefixWord ++ tailWord_4839516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839516).length < 2 ^ (prefixWord ++ tailWord_4839516).sum := by decide
  have hdescent : baseEnd_4839516 < baseStart_4839516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839533 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_4839533 : Nat := 118140960795 + 4839533 * 2 ^ 59
def prefixEnd_4839533 : Nat := 4983230072969 + 3 ^ 40 * 4839533 * 2
def baseEnd_4839533 : Nat := 828335524098506346193633

theorem tailTrace_4839533 : CollatzResearch.WordTrace tailWord_4839533 prefixEnd_4839533 828335524098506346193633 := by
  unfold tailWord_4839533
  simp only [CollatzResearch.WordTrace]
  refine ⟨176512269576205942278379253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117674846384137294852252835 176512269576205942278379253)
  ·
    refine ⟨16548025272769307088598055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176512269576205942278379253 16548025272769307088598055)
    ·
      refine ⟨24822037909153960632897083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16548025272769307088598055 24822037909153960632897083)
      ·
        refine ⟨37233056863730940949345625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24822037909153960632897083 37233056863730940949345625)
        ·
          refine ⟨27924792647798205712009219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37233056863730940949345625 27924792647798205712009219)
          ·
            refine ⟨41887188971697308568013829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27924792647798205712009219 41887188971697308568013829)
            ·
              refine ⟨7853847932193245356502593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41887188971697308568013829 7853847932193245356502593)
              ·
                refine ⟨5890385949144934017376945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7853847932193245356502593 5890385949144934017376945)
                ·
                  refine ⟨4417789461858700513032709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5890385949144934017376945 4417789461858700513032709)
                  ·
                    refine ⟨828335524098506346193633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4417789461858700513032709 828335524098506346193633)
                    ·
                      rfl

theorem cell23_4839533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_4839533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839533 prefixEnd_4839533 := by exact prefixLift 4839533
  have htrace : WordTrace (prefixWord ++ tailWord_4839533) baseStart_4839533 baseEnd_4839533 := by
    simpa [prefixWord, tailWord_4839533, baseEnd_4839533] using wordTrace_append hprefix tailTrace_4839533
  have hstable : (prefixWord ++ tailWord_4839533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839533).length < 2 ^ (prefixWord ++ tailWord_4839533).sum := by decide
  have hdescent : baseEnd_4839533 < baseStart_4839533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839553 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_4839553 : Nat := 118140960795 + 4839553 * 2 ^ 59
def prefixEnd_4839553 : Nat := 4983230072969 + 3 ^ 40 * 4839553 * 2
def baseEnd_4839553 : Nat := 2485016841908608960330807

theorem tailTrace_4839553 : CollatzResearch.WordTrace tailWord_4839553 prefixEnd_4839553 2485016841908608960330807 := by
  unfold tailWord_4839553
  simp only [CollatzResearch.WordTrace]
  refine ⟨176512999036133485694107313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117675332690755657129404875 176512999036133485694107313)
  ·
    refine ⟨132384749277100114270580485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176512999036133485694107313 132384749277100114270580485)
    ·
      refine ⟨24822140489456271425733841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132384749277100114270580485 24822140489456271425733841)
      ·
        refine ⟨18616605367092203569300381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24822140489456271425733841 18616605367092203569300381)
        ·
          refine ⟨6981227012659576338487643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18616605367092203569300381 6981227012659576338487643)
          ·
            refine ⟨10471840518989364507731465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6981227012659576338487643 10471840518989364507731465)
            ·
              refine ⟨7853880389242023380798599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10471840518989364507731465 7853880389242023380798599)
              ·
                refine ⟨11780820583863035071197899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7853880389242023380798599 11780820583863035071197899)
                ·
                  refine ⟨17671230875794552606796849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11780820583863035071197899 17671230875794552606796849)
                  ·
                    refine ⟨13253423156845914455097637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17671230875794552606796849 13253423156845914455097637)
                    ·
                      refine ⟨2485016841908608960330807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13253423156845914455097637 2485016841908608960330807)
                      ·
                        rfl

theorem cell23_4839553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_4839553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839553 prefixEnd_4839553 := by exact prefixLift 4839553
  have htrace : WordTrace (prefixWord ++ tailWord_4839553) baseStart_4839553 baseEnd_4839553 := by
    simpa [prefixWord, tailWord_4839553, baseEnd_4839553] using wordTrace_append hprefix tailTrace_4839553
  have hstable : (prefixWord ++ tailWord_4839553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839553).length < 2 ^ (prefixWord ++ tailWord_4839553).sum := by decide
  have hdescent : baseEnd_4839553 < baseStart_4839553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839589 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_4839589 : Nat := 118140960795 + 4839589 * 2 ^ 59
def prefixEnd_4839589 : Nat := 4983230072969 + 3 ^ 40 * 4839589 * 2
def baseEnd_4839589 : Nat := 828345109070723606493547

theorem tailTrace_4839589 : CollatzResearch.WordTrace tailWord_4839589 prefixEnd_4839589 828345109070723606493547 := by
  unfold tailWord_4839589
  simp only [CollatzResearch.WordTrace]
  refine ⟨176514312064003063842417821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117676208042668709228278547 176514312064003063842417821)
  ·
    refine ⟨66192867024001148940906683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176514312064003063842417821 66192867024001148940906683)
    ·
      refine ⟨99289300536001723411360025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66192867024001148940906683 99289300536001723411360025)
      ·
        refine ⟨74466975402001292558520019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99289300536001723411360025 74466975402001292558520019)
        ·
          refine ⟨111700463103001938837780029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74466975402001292558520019 111700463103001938837780029)
          ·
            refine ⟨41887673663625727064167511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111700463103001938837780029 41887673663625727064167511)
            ·
              refine ⟨62831510495438590596251267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41887673663625727064167511 62831510495438590596251267)
              ·
                refine ⟨94247265743157885894376901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62831510495438590596251267 94247265743157885894376901)
                ·
                  refine ⟨17671362326842103605195669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94247265743157885894376901 17671362326842103605195669)
                  ·
                    refine ⟨828345109070723606493547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17671362326842103605195669 828345109070723606493547)
                    ·
                      rfl

theorem cell23_4839589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_4839589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839589 prefixEnd_4839589 := by exact prefixLift 4839589
  have htrace : WordTrace (prefixWord ++ tailWord_4839589) baseStart_4839589 baseEnd_4839589 := by
    simpa [prefixWord, tailWord_4839589, baseEnd_4839589] using wordTrace_append hprefix tailTrace_4839589
  have hstable : (prefixWord ++ tailWord_4839589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839589).length < 2 ^ (prefixWord ++ tailWord_4839589).sum := by decide
  have hdescent : baseEnd_4839589 < baseStart_4839589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839599 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 5]
def baseStart_4839599 : Nat := 118140960795 + 4839599 * 2 ^ 59
def prefixEnd_4839599 : Nat := 4983230072969 + 3 ^ 40 * 4839599 * 2
def baseEnd_4839599 : Nat := 2485040462018715780355595

theorem tailTrace_4839599 : CollatzResearch.WordTrace tailWord_4839599 prefixEnd_4839599 2485040462018715780355595 := by
  unfold tailWord_4839599
  simp only [CollatzResearch.WordTrace]
  refine ⟨176514676793966835550281851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117676451195977890366854567 176514676793966835550281851)
  ·
    refine ⟨264772015190950253325422777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176514676793966835550281851 264772015190950253325422777)
    ·
      refine ⟨198579011393212689994067083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264772015190950253325422777 198579011393212689994067083)
      ·
        refine ⟨297868517089819034991100625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198579011393212689994067083 297868517089819034991100625)
        ·
          refine ⟨223401387817364276243325469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297868517089819034991100625 223401387817364276243325469)
          ·
            refine ⟨83775520431511603591247051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223401387817364276243325469 83775520431511603591247051)
            ·
              refine ⟨125663280647267405386870577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83775520431511603591247051 125663280647267405386870577)
              ·
                refine ⟨94247460485450554040152933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125663280647267405386870577 94247460485450554040152933)
                ·
                  refine ⟨17671398841021978882528675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94247460485450554040152933 17671398841021978882528675)
                  ·
                    refine ⟨26507098261532968323793013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17671398841021978882528675 26507098261532968323793013)
                    ·
                      refine ⟨2485040462018715780355595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26507098261532968323793013 2485040462018715780355595)
                      ·
                        rfl

theorem cell23_4839599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_4839599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839599 prefixEnd_4839599 := by exact prefixLift 4839599
  have htrace : WordTrace (prefixWord ++ tailWord_4839599) baseStart_4839599 baseEnd_4839599 := by
    simpa [prefixWord, tailWord_4839599, baseEnd_4839599] using wordTrace_append hprefix tailTrace_4839599
  have hstable : (prefixWord ++ tailWord_4839599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839599).length < 2 ^ (prefixWord ++ tailWord_4839599).sum := by decide
  have hdescent : baseEnd_4839599 < baseStart_4839599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839604 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4839604 : Nat := 118140960795 + 4839604 * 2 ^ 59
def prefixEnd_4839604 : Nat := 4983230072969 + 3 ^ 40 * 4839604 * 2
def baseEnd_4839604 : Nat := 2485043029421988260793073

theorem tailTrace_4839604 : CollatzResearch.WordTrace tailWord_4839604 prefixEnd_4839604 2485043029421988260793073 := by
  unfold tailWord_4839604
  simp only [CollatzResearch.WordTrace]
  refine ⟨88257429579474360702106933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117676572772632480936142577 88257429579474360702106933)
  ·
    refine ⟨8274134023075721315822525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88257429579474360702106933 8274134023075721315822525)
    ·
      refine ⟨3102800258653395493433447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8274134023075721315822525 3102800258653395493433447)
      ·
        refine ⟨4654200387980093240150171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3102800258653395493433447 4654200387980093240150171)
        ·
          refine ⟨6981300581970139860225257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4654200387980093240150171 6981300581970139860225257)
          ·
            refine ⟨5235975436477604895168943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6981300581970139860225257 5235975436477604895168943)
            ·
              refine ⟨7853963154716407342753415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5235975436477604895168943 7853963154716407342753415)
              ·
                refine ⟨11780944732074611014130123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7853963154716407342753415 11780944732074611014130123)
                ·
                  refine ⟨17671417098111916521195185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11780944732074611014130123 17671417098111916521195185)
                  ·
                    refine ⟨13253562823583937390896389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17671417098111916521195185 13253562823583937390896389)
                    ·
                      refine ⟨2485043029421988260793073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13253562823583937390896389 2485043029421988260793073)
                      ·
                        rfl

theorem cell23_4839604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4839604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839604 prefixEnd_4839604 := by exact prefixLift 4839604
  have htrace : WordTrace (prefixWord ++ tailWord_4839604) baseStart_4839604 baseEnd_4839604 := by
    simpa [prefixWord, tailWord_4839604, baseEnd_4839604] using wordTrace_append hprefix tailTrace_4839604
  have hstable : (prefixWord ++ tailWord_4839604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839604).length < 2 ^ (prefixWord ++ tailWord_4839604).sum := by decide
  have hdescent : baseEnd_4839604 < baseStart_4839604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839630 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2]
def baseStart_4839630 : Nat := 118140960795 + 4839630 * 2 ^ 59
def prefixEnd_4839630 : Nat := 4983230072969 + 3 ^ 40 * 4839630 * 2
def baseEnd_4839630 : Nat := 2485056379919005159067953

theorem tailTrace_4839630 : CollatzResearch.WordTrace tailWord_4839630 prefixEnd_4839630 2485056379919005159067953 := by
  unfold tailWord_4839630
  simp only [CollatzResearch.WordTrace]
  refine ⟨22064475932106815980582543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117677204971236351896440229 22064475932106815980582543)
  ·
    refine ⟨33096713898160223970873815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22064475932106815980582543 33096713898160223970873815)
    ·
      refine ⟨49645070847240335956310723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33096713898160223970873815 49645070847240335956310723)
      ·
        refine ⟨74467606270860503934466085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49645070847240335956310723 74467606270860503934466085)
        ·
          refine ⟨13962676175786344487712391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74467606270860503934466085 13962676175786344487712391)
          ·
            refine ⟨20944014263679516731568587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13962676175786344487712391 20944014263679516731568587)
            ·
              refine ⟨31416021395519275097352881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20944014263679516731568587 31416021395519275097352881)
              ·
                refine ⟨23562016046639456323014661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31416021395519275097352881 23562016046639456323014661)
                ·
                  refine ⟨4417878008744898060565249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23562016046639456323014661 4417878008744898060565249)
                  ·
                    refine ⟨3313408506558673545423937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4417878008744898060565249 3313408506558673545423937)
                    ·
                      refine ⟨2485056379919005159067953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3313408506558673545423937 2485056379919005159067953)
                      ·
                        rfl

theorem cell23_4839630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_4839630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839630 prefixEnd_4839630 := by exact prefixLift 4839630
  have htrace : WordTrace (prefixWord ++ tailWord_4839630) baseStart_4839630 baseEnd_4839630 := by
    simpa [prefixWord, tailWord_4839630, baseEnd_4839630] using wordTrace_append hprefix tailTrace_4839630
  have hstable : (prefixWord ++ tailWord_4839630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839630).length < 2 ^ (prefixWord ++ tailWord_4839630).sum := by decide
  have hdescent : baseEnd_4839630 < baseStart_4839630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839653 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 7]
def baseStart_4839653 : Nat := 118140960795 + 4839653 * 2 ^ 59
def prefixEnd_4839653 : Nat := 4983230072969 + 3 ^ 40 * 4839653 * 2
def baseEnd_4839653 : Nat := 276118687774895396564483

theorem tailTrace_4839653 : CollatzResearch.WordTrace tailWord_4839653 prefixEnd_4839653 276118687774895396564483 := by
  unfold tailWord_4839653
  simp only [CollatzResearch.WordTrace]
  refine ⟨176516646335771202772747613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117677764223847468515165075 176516646335771202772747613)
  ·
    refine ⟨66193742375914201039780355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176516646335771202772747613 66193742375914201039780355)
    ·
      refine ⟨99290613563871301559670533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66193742375914201039780355 99290613563871301559670533)
      ·
        refine ⟨18616990043225869042438225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99290613563871301559670533 18616990043225869042438225)
        ·
          refine ⟨13962742532419401781828669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18616990043225869042438225 13962742532419401781828669)
          ·
            refine ⟨5236028449657275668185751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13962742532419401781828669 5236028449657275668185751)
            ·
              refine ⟨7854042674485913502278627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5236028449657275668185751 7854042674485913502278627)
              ·
                refine ⟨11781064011728870253417941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7854042674485913502278627 11781064011728870253417941)
                ·
                  refine ⟨276118687774895396564483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11781064011728870253417941 276118687774895396564483)
                  ·
                    rfl

theorem cell23_4839653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_4839653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839653 prefixEnd_4839653 := by exact prefixLift 4839653
  have htrace : WordTrace (prefixWord ++ tailWord_4839653) baseStart_4839653 baseEnd_4839653 := by
    simpa [prefixWord, tailWord_4839653, baseEnd_4839653] using wordTrace_append hprefix tailTrace_4839653
  have hstable : (prefixWord ++ tailWord_4839653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839653).length < 2 ^ (prefixWord ++ tailWord_4839653).sum := by decide
  have hdescent : baseEnd_4839653 < baseStart_4839653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839703 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4839703 : Nat := 118140960795 + 4839703 * 2 ^ 59
def prefixEnd_4839703 : Nat := 4983230072969 + 3 ^ 40 * 4839703 * 2
def baseEnd_4839703 : Nat := 2485093864006783373455117

theorem tailTrace_4839703 : CollatzResearch.WordTrace tailWord_4839703 prefixEnd_4839703 2485093864006783373455117 := by
  unfold tailWord_4839703
  simp only [CollatzResearch.WordTrace]
  refine ⟨176518469985590061312067763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117678979990393374208045175 176518469985590061312067763)
  ·
    refine ⟨264777704978385091968101645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176518469985590061312067763 264777704978385091968101645)
    ·
      refine ⟨99291639366894409488038117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264777704978385091968101645 99291639366894409488038117)
      ·
        refine ⟨18617182381292701779007147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99291639366894409488038117 18617182381292701779007147)
        ·
          refine ⟨27925773571939052668510721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18617182381292701779007147 27925773571939052668510721)
          ·
            refine ⟨20944330178954289501383041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27925773571939052668510721 20944330178954289501383041)
            ·
              refine ⟨15708247634215717126037281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20944330178954289501383041 15708247634215717126037281)
              ·
                refine ⟨11781185725661787844527961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15708247634215717126037281 11781185725661787844527961)
                ·
                  refine ⟨8835889294246340883395971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11781185725661787844527961 8835889294246340883395971)
                  ·
                    refine ⟨13253833941369511325093957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8835889294246340883395971 13253833941369511325093957)
                    ·
                      refine ⟨2485093864006783373455117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13253833941369511325093957 2485093864006783373455117)
                      ·
                        rfl

theorem cell23_4839703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4839703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839703 prefixEnd_4839703 := by exact prefixLift 4839703
  have htrace : WordTrace (prefixWord ++ tailWord_4839703) baseStart_4839703 baseEnd_4839703 := by
    simpa [prefixWord, tailWord_4839703, baseEnd_4839703] using wordTrace_append hprefix tailTrace_4839703
  have hstable : (prefixWord ++ tailWord_4839703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839703).length < 2 ^ (prefixWord ++ tailWord_4839703).sum := by decide
  have hdescent : baseEnd_4839703 < baseStart_4839703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839710 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4839710 : Nat := 118140960795 + 4839710 * 2 ^ 59
def prefixEnd_4839710 : Nat := 4983230072969 + 3 ^ 40 * 4839710 * 2
def baseEnd_4839710 : Nat := 2485097458371364846067585

theorem tailTrace_4839710 : CollatzResearch.WordTrace tailWord_4839710 prefixEnd_4839710 2485097458371364846067585 := by
  unfold tailWord_4839710
  simp only [CollatzResearch.WordTrace]
  refine ⟨22064840662070587688446573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117679150197709801005048389 22064840662070587688446573)
  ·
    refine ⟨8274315248276470383167465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22064840662070587688446573 8274315248276470383167465)
    ·
      refine ⟨6205736436207352787375599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8274315248276470383167465 6205736436207352787375599)
      ·
        refine ⟨9308604654311029181063399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6205736436207352787375599 9308604654311029181063399)
        ·
          refine ⟨13962906981466543771595099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9308604654311029181063399 13962906981466543771595099)
          ·
            refine ⟨20944360472199815657392649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13962906981466543771595099 20944360472199815657392649)
            ·
              refine ⟨15708270354149861743044487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20944360472199815657392649 15708270354149861743044487)
              ·
                refine ⟨23562405531224792614566731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15708270354149861743044487 23562405531224792614566731)
                ·
                  refine ⟨35343608296837188921850097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23562405531224792614566731 35343608296837188921850097)
                  ·
                    refine ⟨26507706222627891691387573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35343608296837188921850097 26507706222627891691387573)
                    ·
                      refine ⟨2485097458371364846067585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26507706222627891691387573 2485097458371364846067585)
                      ·
                        rfl

theorem cell23_4839710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4839710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839710 prefixEnd_4839710 := by exact prefixLift 4839710
  have htrace : WordTrace (prefixWord ++ tailWord_4839710) baseStart_4839710 baseEnd_4839710 := by
    simpa [prefixWord, tailWord_4839710, baseEnd_4839710] using wordTrace_append hprefix tailTrace_4839710
  have hstable : (prefixWord ++ tailWord_4839710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839710).length < 2 ^ (prefixWord ++ tailWord_4839710).sum := by decide
  have hdescent : baseEnd_4839710 < baseStart_4839710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839730 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_4839730 : Nat := 118140960795 + 4839730 * 2 ^ 59
def prefixEnd_4839730 : Nat := 4983230072969 + 3 ^ 40 * 4839730 * 2
def baseEnd_4839730 : Nat := 828369242661484922605831

theorem tailTrace_4839730 : CollatzResearch.WordTrace tailWord_4839730 prefixEnd_4839730 828369242661484922605831 := by
  unfold tailWord_4839730
  simp only [CollatzResearch.WordTrace]
  refine ⟨44129863689123061230825161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117679636504328163282200429 44129863689123061230825161)
  ·
    refine ⟨33097397766842295923118871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44129863689123061230825161 33097397766842295923118871)
    ·
      refine ⟨49646096650263443884678307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33097397766842295923118871 49646096650263443884678307)
      ·
        refine ⟨74469144975395165827017461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49646096650263443884678307 74469144975395165827017461)
        ·
          refine ⟨6981482341443296796282887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74469144975395165827017461 6981482341443296796282887)
          ·
            refine ⟨10472223512164945194424331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6981482341443296796282887 10472223512164945194424331)
            ·
              refine ⟨15708335268247417791636497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10472223512164945194424331 15708335268247417791636497)
              ·
                refine ⟨11781251451185563343727373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15708335268247417791636497 11781251451185563343727373)
                ·
                  refine ⟨4417969294194586253897765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11781251451185563343727373 4417969294194586253897765)
                  ·
                    refine ⟨828369242661484922605831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4417969294194586253897765 828369242661484922605831)
                    ·
                      rfl

theorem cell23_4839730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_4839730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839730 prefixEnd_4839730 := by exact prefixLift 4839730
  have htrace : WordTrace (prefixWord ++ tailWord_4839730) baseStart_4839730 baseEnd_4839730 := by
    simpa [prefixWord, tailWord_4839730, baseEnd_4839730] using wordTrace_append hprefix tailTrace_4839730
  have hstable : (prefixWord ++ tailWord_4839730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839730).length < 2 ^ (prefixWord ++ tailWord_4839730).sum := by decide
  have hdescent : baseEnd_4839730 < baseStart_4839730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839753 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 7, 1, 3]
def baseStart_4839753 : Nat := 118140960795 + 4839753 * 2 ^ 59
def prefixEnd_4839753 : Nat := 4983230072969 + 3 ^ 40 * 4839753 * 2
def baseEnd_4839753 : Nat := 2485119538039508177829887

theorem tailTrace_4839753 : CollatzResearch.WordTrace tailWord_4839753 prefixEnd_4839753 2485119538039508177829887 := by
  unfold tailWord_4839753
  simp only [CollatzResearch.WordTrace]
  refine ⟨176520293635408919851387913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117680195756939279900925275 176520293635408919851387913)
  ·
    refine ⟨132390220226556689888540935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176520293635408919851387913 132390220226556689888540935)
    ·
      refine ⟨198585330339835034832811403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132390220226556689888540935 198585330339835034832811403)
      ·
        refine ⟨297877995509752552249217105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198585330339835034832811403 297877995509752552249217105)
        ·
          refine ⟨223408496632314414186912829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297877995509752552249217105 223408496632314414186912829)
          ·
            refine ⟨83778186237117905320092311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223408496632314414186912829 83778186237117905320092311)
            ·
              refine ⟨125667279355676857980138467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83778186237117905320092311 125667279355676857980138467)
              ·
                refine ⟨188500919033515286970207701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125667279355676857980138467 188500919033515286970207701)
                ·
                  refine ⟨4417990289848014538364243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 188500919033515286970207701 4417990289848014538364243)
                  ·
                    refine ⟨6626985434772021807546365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4417990289848014538364243 6626985434772021807546365)
                    ·
                      refine ⟨2485119538039508177829887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6626985434772021807546365 2485119538039508177829887)
                      ·
                        rfl

theorem cell23_4839753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 1, 3].length) (baseStart_4839753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839753 prefixEnd_4839753 := by exact prefixLift 4839753
  have htrace : WordTrace (prefixWord ++ tailWord_4839753) baseStart_4839753 baseEnd_4839753 := by
    simpa [prefixWord, tailWord_4839753, baseEnd_4839753] using wordTrace_append hprefix tailTrace_4839753
  have hstable : (prefixWord ++ tailWord_4839753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839753).length < 2 ^ (prefixWord ++ tailWord_4839753).sum := by decide
  have hdescent : baseEnd_4839753 < baseStart_4839753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839793 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 1, 8, 2]
def baseStart_4839793 : Nat := 118140960795 + 4839793 * 2 ^ 59
def prefixEnd_4839793 : Nat := 4983230072969 + 3 ^ 40 * 4839793 * 2
def baseEnd_4839793 : Nat := 2485140077265688021329703

theorem tailTrace_4839793 : CollatzResearch.WordTrace tailWord_4839793 prefixEnd_4839793 2485140077265688021329703 := by
  unfold tailWord_4839793
  simp only [CollatzResearch.WordTrace]
  refine ⟨176521752555264006682844033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117681168370176004455229355 176521752555264006682844033)
  ·
    refine ⟨132391314416448005012133025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176521752555264006682844033 132391314416448005012133025)
    ·
      refine ⟨99293485812336003759099769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132391314416448005012133025 99293485812336003759099769)
      ·
        refine ⟨74470114359252002819324827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99293485812336003759099769 74470114359252002819324827)
        ·
          refine ⟨111705171538878004228987241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74470114359252002819324827 111705171538878004228987241)
          ·
            refine ⟨83778878654158503171740431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111705171538878004228987241 83778878654158503171740431)
            ·
              refine ⟨125668317981237754757610647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83778878654158503171740431 125668317981237754757610647)
              ·
                refine ⟨188502476971856632136415971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125668317981237754757610647 188502476971856632136415971)
                ·
                  refine ⟨282753715457784948204623957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188502476971856632136415971 282753715457784948204623957)
                  ·
                    refine ⟨3313520103020917361772937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 282753715457784948204623957 3313520103020917361772937)
                    ·
                      refine ⟨2485140077265688021329703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3313520103020917361772937 2485140077265688021329703)
                      ·
                        rfl

theorem cell23_4839793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_4839793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839793 prefixEnd_4839793 := by exact prefixLift 4839793
  have htrace : WordTrace (prefixWord ++ tailWord_4839793) baseStart_4839793 baseEnd_4839793 := by
    simpa [prefixWord, tailWord_4839793, baseEnd_4839793] using wordTrace_append hprefix tailTrace_4839793
  have hstable : (prefixWord ++ tailWord_4839793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839793).length < 2 ^ (prefixWord ++ tailWord_4839793).sum := by decide
  have hdescent : baseEnd_4839793 < baseStart_4839793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839798 : List Nat := [5, 1, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_4839798 : Nat := 118140960795 + 4839798 * 2 ^ 59
def prefixEnd_4839798 : Nat := 4983230072969 + 3 ^ 40 * 4839798 * 2
def baseEnd_4839798 : Nat := 828380881556320167255727

theorem tailTrace_4839798 : CollatzResearch.WordTrace tailWord_4839798 prefixEnd_4839798 828380881556320167255727 := by
  unfold tailWord_4839798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11032620932515368283548503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117681289946830595024517365 11032620932515368283548503)
  ·
    refine ⟨16548931398773052425322755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11032620932515368283548503 16548931398773052425322755)
    ·
      refine ⟨24823397098159578637984133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16548931398773052425322755 24823397098159578637984133)
      ·
        refine ⟨4654386955904920994622025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24823397098159578637984133 4654386955904920994622025)
        ·
          refine ⟨3490790216928690745966519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4654386955904920994622025 3490790216928690745966519)
          ·
            refine ⟨5236185325393036118949779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3490790216928690745966519 5236185325393036118949779)
            ·
              refine ⟨7854277988089554178424669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5236185325393036118949779 7854277988089554178424669)
              ·
                refine ⟨2945354245533582816909251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7854277988089554178424669 2945354245533582816909251)
                ·
                  refine ⟨4418031368300374225363877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945354245533582816909251 4418031368300374225363877)
                  ·
                    refine ⟨828380881556320167255727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4418031368300374225363877 828380881556320167255727)
                    ·
                      rfl

theorem cell23_4839798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_4839798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839798 prefixEnd_4839798 := by exact prefixLift 4839798
  have htrace : WordTrace (prefixWord ++ tailWord_4839798) baseStart_4839798 baseEnd_4839798 := by
    simpa [prefixWord, tailWord_4839798, baseEnd_4839798] using wordTrace_append hprefix tailTrace_4839798
  have hstable : (prefixWord ++ tailWord_4839798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839798).length < 2 ^ (prefixWord ++ tailWord_4839798).sum := by decide
  have hdescent : baseEnd_4839798 < baseStart_4839798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839803 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 4, 4]
def baseStart_4839803 : Nat := 118140960795 + 4839803 * 2 ^ 59
def prefixEnd_4839803 : Nat := 4983230072969 + 3 ^ 40 * 4839803 * 2
def baseEnd_4839803 : Nat := 828381737357410994068219

theorem tailTrace_4839803 : CollatzResearch.WordTrace tailWord_4839803 prefixEnd_4839803 828381737357410994068219 := by
  unfold tailWord_4839803
  simp only [CollatzResearch.WordTrace]
  refine ⟨176522117285227778390708063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117681411523485185593805375 176522117285227778390708063)
  ·
    refine ⟨264783175927841667586062095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176522117285227778390708063 264783175927841667586062095)
    ·
      refine ⟨397174763891762501379093143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264783175927841667586062095 397174763891762501379093143)
      ·
        refine ⟨595762145837643752068639715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397174763891762501379093143 595762145837643752068639715)
        ·
          refine ⟨893643218756465628102959573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595762145837643752068639715 893643218756465628102959573)
          ·
            refine ⟨20944762939604663158663115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 893643218756465628102959573 20944762939604663158663115)
            ·
              refine ⟨31417144409406994737994673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20944762939604663158663115 31417144409406994737994673)
              ·
                refine ⟨23562858307055246053496005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31417144409406994737994673 23562858307055246053496005)
                ·
                  refine ⟨4418035932572858635030501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23562858307055246053496005 4418035932572858635030501)
                  ·
                    refine ⟨828381737357410994068219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4418035932572858635030501 828381737357410994068219)
                    ·
                      rfl

theorem cell23_4839803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 4].length) (baseStart_4839803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839803 prefixEnd_4839803 := by exact prefixLift 4839803
  have htrace : WordTrace (prefixWord ++ tailWord_4839803) baseStart_4839803 baseEnd_4839803 := by
    simpa [prefixWord, tailWord_4839803, baseEnd_4839803] using wordTrace_append hprefix tailTrace_4839803
  have hstable : (prefixWord ++ tailWord_4839803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839803).length < 2 ^ (prefixWord ++ tailWord_4839803).sum := by decide
  have hdescent : baseEnd_4839803 < baseStart_4839803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
