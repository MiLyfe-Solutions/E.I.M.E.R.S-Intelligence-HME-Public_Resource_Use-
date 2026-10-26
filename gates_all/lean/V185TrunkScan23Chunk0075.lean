import V185TrunkScan23Chunk0074

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_445153 : List Nat := [1, 2, 3, 1, 4, 1, 4, 2, 1, 4]
def baseStart_445153 : Nat := 118140960795 + 445153 * 2 ^ 59
def prefixEnd_445153 : Nat := 4983230072969 + 3 ^ 40 * 445153 * 2
def baseEnd_445153 : Nat := 76192484597000690180095

theorem tailTrace_445153 : CollatzResearch.WordTrace tailWord_445153 prefixEnd_445153 76192484597000690180095 := by
  unfold tailWord_445153
  simp only [CollatzResearch.WordTrace]
  refine ⟨16236063756294181924764113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10824042504196121283176075 16236063756294181924764113)
  ·
    refine ⟨12177047817220636443573085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16236063756294181924764113 12177047817220636443573085)
    ·
      refine ⟨4566392931457738666339907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12177047817220636443573085 4566392931457738666339907)
      ·
        refine ⟨6849589397186607999509861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4566392931457738666339907 6849589397186607999509861)
        ·
          refine ⟨1284298011972488999908099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6849589397186607999509861 1284298011972488999908099)
          ·
            refine ⟨1926447017958733499862149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284298011972488999908099 1926447017958733499862149)
            ·
              refine ⟨361208815867262531224153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1926447017958733499862149 361208815867262531224153)
              ·
                refine ⟨270906611900446898418115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361208815867262531224153 270906611900446898418115)
                ·
                  refine ⟨406359917850670347627173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270906611900446898418115 406359917850670347627173)
                  ·
                    refine ⟨76192484597000690180095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 406359917850670347627173 76192484597000690180095)
                    ·
                      rfl

theorem cell23_445153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_445153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445153 prefixEnd_445153 := by exact prefixLift 445153
  have htrace : WordTrace (prefixWord ++ tailWord_445153) baseStart_445153 baseEnd_445153 := by
    simpa [prefixWord, tailWord_445153, baseEnd_445153] using wordTrace_append hprefix tailTrace_445153
  have hstable : (prefixWord ++ tailWord_445153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445153).length < 2 ^ (prefixWord ++ tailWord_445153).sum := by decide
  have hdescent : baseEnd_445153 < baseStart_445153 := by decide
  rcases family_descends (prefixWord ++ tailWord_445153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445169 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 1, 5, 2]
def baseStart_445169 : Nat := 118140960795 + 445169 * 2 ^ 59
def prefixEnd_445169 : Nat := 4983230072969 + 3 ^ 40 * 445169 * 2
def baseEnd_445169 : Nat := 228585669481474007940211

theorem tailTrace_445169 : CollatzResearch.WordTrace tailWord_445169 prefixEnd_445169 228585669481474007940211 := by
  unfold tailWord_445169
  simp only [CollatzResearch.WordTrace]
  refine ⟨16236647324236216657346561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10824431549490811104897707 16236647324236216657346561)
  ·
    refine ⟨12177485493177162493009921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16236647324236216657346561 12177485493177162493009921)
    ·
      refine ⟨9133114119882871869757441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12177485493177162493009921 9133114119882871869757441)
      ·
        refine ⟨6849835589912153902318081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9133114119882871869757441 6849835589912153902318081)
        ·
          refine ⟨5137376692434115426738561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6849835589912153902318081 5137376692434115426738561)
          ·
            refine ⟨3853032519325586570053921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5137376692434115426738561 3853032519325586570053921)
            ·
              refine ⟨2889774389494189927540441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3853032519325586570053921 2889774389494189927540441)
              ·
                refine ⟨2167330792120642445655331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2889774389494189927540441 2167330792120642445655331)
                ·
                  refine ⟨3250996188180963668482997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167330792120642445655331 3250996188180963668482997)
                  ·
                    refine ⟨304780892641965343920281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3250996188180963668482997 304780892641965343920281)
                    ·
                      refine ⟨228585669481474007940211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304780892641965343920281 228585669481474007940211)
                      ·
                        rfl

theorem cell23_445169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_445169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445169 prefixEnd_445169 := by exact prefixLift 445169
  have htrace : WordTrace (prefixWord ++ tailWord_445169) baseStart_445169 baseEnd_445169 := by
    simpa [prefixWord, tailWord_445169, baseEnd_445169] using wordTrace_append hprefix tailTrace_445169
  have hstable : (prefixWord ++ tailWord_445169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445169).length < 2 ^ (prefixWord ++ tailWord_445169).sum := by decide
  have hdescent : baseEnd_445169 < baseStart_445169 := by decide
  rcases family_descends (prefixWord ++ tailWord_445169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445199 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 4]
def baseStart_445199 : Nat := 118140960795 + 445199 * 2 ^ 59
def prefixEnd_445199 : Nat := 4983230072969 + 3 ^ 40 * 445199 * 2
def baseEnd_445199 : Nat := 228601073901108890565073

theorem tailTrace_445199 : CollatzResearch.WordTrace tailWord_445199 prefixEnd_445199 228601073901108890565073 := by
  unfold tailWord_445199
  simp only [CollatzResearch.WordTrace]
  refine ⟨16237741514127531780938651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10825161009418354520625767 16237741514127531780938651)
  ·
    refine ⟨24356612271191297671407977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16237741514127531780938651 24356612271191297671407977)
    ·
      refine ⟨18267459203393473253555983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24356612271191297671407977 18267459203393473253555983)
      ·
        refine ⟨27401188805090209880333975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18267459203393473253555983 27401188805090209880333975)
        ·
          refine ⟨41101783207635314820500963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27401188805090209880333975 41101783207635314820500963)
          ·
            refine ⟨61652674811452972230751445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41101783207635314820500963 61652674811452972230751445)
            ·
              refine ⟨1444984565893429036658237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 61652674811452972230751445 1444984565893429036658237)
              ·
                refine ⟨541869212210035888746839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1444984565893429036658237 541869212210035888746839)
                ·
                  refine ⟨812803818315053833120259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541869212210035888746839 812803818315053833120259)
                  ·
                    refine ⟨1219205727472580749680389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 812803818315053833120259 1219205727472580749680389)
                    ·
                      refine ⟨228601073901108890565073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1219205727472580749680389 228601073901108890565073)
                      ·
                        rfl

theorem cell23_445199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 4].length) (baseStart_445199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445199 prefixEnd_445199 := by exact prefixLift 445199
  have htrace : WordTrace (prefixWord ++ tailWord_445199) baseStart_445199 baseEnd_445199 := by
    simpa [prefixWord, tailWord_445199, baseEnd_445199] using wordTrace_append hprefix tailTrace_445199
  have hstable : (prefixWord ++ tailWord_445199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445199).length < 2 ^ (prefixWord ++ tailWord_445199).sum := by decide
  have hdescent : baseEnd_445199 < baseStart_445199 := by decide
  rcases family_descends (prefixWord ++ tailWord_445199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445209 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 2, 4]
def baseStart_445209 : Nat := 118140960795 + 445209 * 2 ^ 59
def prefixEnd_445209 : Nat := 4983230072969 + 3 ^ 40 * 445209 * 2
def baseEnd_445209 : Nat := 76202069569217950480009

theorem tailTrace_445209 : CollatzResearch.WordTrace tailWord_445209 prefixEnd_445209 76202069569217950480009 := by
  unfold tailWord_445209
  simp only [CollatzResearch.WordTrace]
  refine ⟨16238106244091303488802681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10825404162727535659201787 16238106244091303488802681)
  ·
    refine ⟨12178579683068477616602011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16238106244091303488802681 12178579683068477616602011)
    ·
      refine ⟨18267869524602716424903017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12178579683068477616602011 18267869524602716424903017)
      ·
        refine ⟨13700902143452037318677263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18267869524602716424903017 13700902143452037318677263)
        ·
          refine ⟨20551353215178055978015895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13700902143452037318677263 20551353215178055978015895)
          ·
            refine ⟨30827029822767083967023843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20551353215178055978015895 30827029822767083967023843)
            ·
              refine ⟨46240544734150625950535765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30827029822767083967023843 46240544734150625950535765)
              ·
                refine ⟨541881383603327647857841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 46240544734150625950535765 541881383603327647857841)
                ·
                  refine ⟨406411037702495735893381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541881383603327647857841 406411037702495735893381)
                  ·
                    refine ⟨76202069569217950480009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 406411037702495735893381 76202069569217950480009)
                    ·
                      rfl

theorem cell23_445209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 4].length) (baseStart_445209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445209 prefixEnd_445209 := by exact prefixLift 445209
  have htrace : WordTrace (prefixWord ++ tailWord_445209) baseStart_445209 baseEnd_445209 := by
    simpa [prefixWord, tailWord_445209, baseEnd_445209] using wordTrace_append hprefix tailTrace_445209
  have hstable : (prefixWord ++ tailWord_445209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445209).length < 2 ^ (prefixWord ++ tailWord_445209).sum := by decide
  have hdescent : baseEnd_445209 < baseStart_445209 := by decide
  rcases family_descends (prefixWord ++ tailWord_445209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445266 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_445266 : Nat := 118140960795 + 445266 * 2 ^ 59
def prefixEnd_445266 : Nat := 4983230072969 + 3 ^ 40 * 445266 * 2
def baseEnd_445266 : Nat := 228635477104960128427265

theorem tailTrace_445266 : CollatzResearch.WordTrace tailWord_445266 prefixEnd_445266 228635477104960128427265 := by
  unfold tailWord_445266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4060046301221200555906913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10826790136589868149085101 4060046301221200555906913)
  ·
    refine ⟨3045034725915900416930185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4060046301221200555906913 3045034725915900416930185)
    ·
      refine ⟨2283776044436925312697639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3045034725915900416930185 2283776044436925312697639)
      ·
        refine ⟨3425664066655387969046459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2283776044436925312697639 3425664066655387969046459)
        ·
          refine ⟨5138496099983081953569689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3425664066655387969046459 5138496099983081953569689)
          ·
            refine ⟨3853872074987311465177267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5138496099983081953569689 3853872074987311465177267)
            ·
              refine ⟨5780808112480967197765901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3853872074987311465177267 5780808112480967197765901)
              ·
                refine ⟨2167803042180362699162213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5780808112480967197765901 2167803042180362699162213)
                ·
                  refine ⟨406463070408818006092915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2167803042180362699162213 406463070408818006092915)
                  ·
                    refine ⟨609694605613227009139373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 406463070408818006092915 609694605613227009139373)
                    ·
                      refine ⟨228635477104960128427265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 609694605613227009139373 228635477104960128427265)
                      ·
                        rfl

theorem cell23_445266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_445266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445266 prefixEnd_445266 := by exact prefixLift 445266
  have htrace : WordTrace (prefixWord ++ tailWord_445266) baseStart_445266 baseEnd_445266 := by
    simpa [prefixWord, tailWord_445266, baseEnd_445266] using wordTrace_append hprefix tailTrace_445266
  have hstable : (prefixWord ++ tailWord_445266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445266).length < 2 ^ (prefixWord ++ tailWord_445266).sum := by decide
  have hdescent : baseEnd_445266 < baseStart_445266 := by decide
  rcases family_descends (prefixWord ++ tailWord_445266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445283 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 2, 1, 3]
def baseStart_445283 : Nat := 118140960795 + 445283 * 2 ^ 59
def prefixEnd_445283 : Nat := 4983230072969 + 3 ^ 40 * 445283 * 2
def baseEnd_445283 : Nat := 228644206276086561914687

theorem tailTrace_445283 : CollatzResearch.WordTrace tailWord_445283 prefixEnd_445283 228644206276086561914687 := by
  unfold tailWord_445283
  simp only [CollatzResearch.WordTrace]
  refine ⟨16240805245823214126996503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10827203497215476084664335 16240805245823214126996503)
  ·
    refine ⟨24361207868734821190494755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16240805245823214126996503 24361207868734821190494755)
    ·
      refine ⟨36541811803102231785742133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24361207868734821190494755 36541811803102231785742133)
      ·
        refine ⟨3425794856540834229913325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36541811803102231785742133 3425794856540834229913325)
        ·
          refine ⟨1284673071202812836217497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3425794856540834229913325 1284673071202812836217497)
          ·
            refine ⟨963504803402109627163123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1284673071202812836217497 963504803402109627163123)
            ·
              refine ⟨1445257205103164440744685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963504803402109627163123 1445257205103164440744685)
              ·
                refine ⟨541971451913686665279257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1445257205103164440744685 541971451913686665279257)
                ·
                  refine ⟨406478588935264998959443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541971451913686665279257 406478588935264998959443)
                  ·
                    refine ⟨609717883402897498439165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 406478588935264998959443 609717883402897498439165)
                    ·
                      refine ⟨228644206276086561914687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 609717883402897498439165 228644206276086561914687)
                      ·
                        rfl

theorem cell23_445283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_445283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445283 prefixEnd_445283 := by exact prefixLift 445283
  have htrace : WordTrace (prefixWord ++ tailWord_445283) baseStart_445283 baseEnd_445283 := by
    simpa [prefixWord, tailWord_445283, baseEnd_445283] using wordTrace_append hprefix tailTrace_445283
  have hstable : (prefixWord ++ tailWord_445283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445283).length < 2 ^ (prefixWord ++ tailWord_445283).sum := by decide
  have hdescent : baseEnd_445283 < baseStart_445283 := by decide
  rcases family_descends (prefixWord ++ tailWord_445283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445309 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_445309 : Nat := 118140960795 + 445309 * 2 ^ 59
def prefixEnd_445309 : Nat := 4983230072969 + 3 ^ 40 * 445309 * 2
def baseEnd_445309 : Nat := 228657556773103460189567

theorem tailTrace_445309 : CollatzResearch.WordTrace tailWord_445309 prefixEnd_445309 228657556773103460189567 := by
  unfold tailWord_445309
  simp only [CollatzResearch.WordTrace]
  refine ⟨16241753543729020567442981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10827835695819347044961987 16241753543729020567442981)
  ·
    refine ⟨3045328789449191356395559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16241753543729020567442981 3045328789449191356395559)
    ·
      refine ⟨4567993184173787034593339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3045328789449191356395559 4567993184173787034593339)
      ·
        refine ⟨6851989776260680551890009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4567993184173787034593339 6851989776260680551890009)
        ·
          refine ⟨5138992332195510413917507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6851989776260680551890009 5138992332195510413917507)
          ·
            refine ⟨7708488498293265620876261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138992332195510413917507 7708488498293265620876261)
            ·
              refine ⟨1445341593429987303914299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7708488498293265620876261 1445341593429987303914299)
              ·
                refine ⟨2168012390144980955871449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445341593429987303914299 2168012390144980955871449)
                ·
                  refine ⟨1626009292608735716903587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2168012390144980955871449 1626009292608735716903587)
                  ·
                    refine ⟨2439013938913103575355381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1626009292608735716903587 2439013938913103575355381)
                    ·
                      refine ⟨228657556773103460189567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2439013938913103575355381 228657556773103460189567)
                      ·
                        rfl

theorem cell23_445309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_445309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445309 prefixEnd_445309 := by exact prefixLift 445309
  have htrace : WordTrace (prefixWord ++ tailWord_445309) baseStart_445309 baseEnd_445309 := by
    simpa [prefixWord, tailWord_445309, baseEnd_445309] using wordTrace_append hprefix tailTrace_445309
  have hstable : (prefixWord ++ tailWord_445309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445309).length < 2 ^ (prefixWord ++ tailWord_445309).sum := by decide
  have hdescent : baseEnd_445309 < baseStart_445309 := by decide
  rcases family_descends (prefixWord ++ tailWord_445309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445312 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 11]
def baseStart_445312 : Nat := 118140960795 + 445312 * 2 ^ 59
def prefixEnd_445312 : Nat := 4983230072969 + 3 ^ 40 * 445312 * 2
def baseEnd_445312 : Nat := 25406566357229660939117

theorem tailTrace_445312 : CollatzResearch.WordTrace tailWord_445312 prefixEnd_445312 25406566357229660939117 := by
  unfold tailWord_445312
  simp only [CollatzResearch.WordTrace]
  refine ⟨8120931481359076039901095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10827908641812101386534793 8120931481359076039901095)
  ·
    refine ⟨12181397222038614059851643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8120931481359076039901095 12181397222038614059851643)
    ·
      refine ⟨18272095833057921089777465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12181397222038614059851643 18272095833057921089777465)
      ·
        refine ⟨13704071874793440817333099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18272095833057921089777465 13704071874793440817333099)
        ·
          refine ⟨20556107812190161225999649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13704071874793440817333099 20556107812190161225999649)
          ·
            refine ⟨15417080859142620919499737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20556107812190161225999649 15417080859142620919499737)
            ·
              refine ⟨11562810644356965689624803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15417080859142620919499737 11562810644356965689624803)
              ·
                refine ⟨17344215966535448534437205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11562810644356965689624803 17344215966535448534437205)
                ·
                  refine ⟨25406566357229660939117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 17344215966535448534437205 25406566357229660939117)
                  ·
                    rfl

theorem cell23_445312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 11].length) (baseStart_445312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445312 prefixEnd_445312 := by exact prefixLift 445312
  have htrace : WordTrace (prefixWord ++ tailWord_445312) baseStart_445312 baseEnd_445312 := by
    simpa [prefixWord, tailWord_445312, baseEnd_445312] using wordTrace_append hprefix tailTrace_445312
  have hstable : (prefixWord ++ tailWord_445312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445312).length < 2 ^ (prefixWord ++ tailWord_445312).sum := by decide
  have hdescent : baseEnd_445312 < baseStart_445312 := by decide
  rcases family_descends (prefixWord ++ tailWord_445312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445323 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 2, 2, 2]
def baseStart_445323 : Nat := 118140960795 + 445323 * 2 ^ 59
def prefixEnd_445323 : Nat := 4983230072969 + 3 ^ 40 * 445323 * 2
def baseEnd_445323 : Nat := 228664745502266405414503

theorem tailTrace_445323 : CollatzResearch.WordTrace tailWord_445323 prefixEnd_445323 228664745502266405414503 := by
  unfold tailWord_445323
  simp only [CollatzResearch.WordTrace]
  refine ⟨16242264165678300958452623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10828176110452200638968415 16242264165678300958452623)
  ·
    refine ⟨24363396248517451437678935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16242264165678300958452623 24363396248517451437678935)
    ·
      refine ⟨36545094372776177156518403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24363396248517451437678935 36545094372776177156518403)
      ·
        refine ⟨54817641559164265734777605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36545094372776177156518403 54817641559164265734777605)
        ·
          refine ⟨10278307792343299825270801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54817641559164265734777605 10278307792343299825270801)
          ·
            refine ⟨7708730844257474868953101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10278307792343299825270801 7708730844257474868953101)
            ·
              refine ⟨2890774066596553075857413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7708730844257474868953101 2890774066596553075857413)
              ·
                refine ⟨542020137486853701723265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2890774066596553075857413 542020137486853701723265)
                ·
                  refine ⟨406515103115140276292449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542020137486853701723265 406515103115140276292449)
                  ·
                    refine ⟨304886327336355207219337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 406515103115140276292449 304886327336355207219337)
                    ·
                      refine ⟨228664745502266405414503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304886327336355207219337 228664745502266405414503)
                      ·
                        rfl

theorem cell23_445323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 2, 2].length) (baseStart_445323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445323 prefixEnd_445323 := by exact prefixLift 445323
  have htrace : WordTrace (prefixWord ++ tailWord_445323) baseStart_445323 baseEnd_445323 := by
    simpa [prefixWord, tailWord_445323, baseEnd_445323] using wordTrace_append hprefix tailTrace_445323
  have hstable : (prefixWord ++ tailWord_445323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445323).length < 2 ^ (prefixWord ++ tailWord_445323).sum := by decide
  have hdescent : baseEnd_445323 < baseStart_445323 := by decide
  rcases family_descends (prefixWord ++ tailWord_445323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445340 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_445340 : Nat := 118140960795 + 445340 * 2 ^ 59
def prefixEnd_445340 : Nat := 4983230072969 + 3 ^ 40 * 445340 * 2
def baseEnd_445340 : Nat := 228673474673392838901925

theorem tailTrace_445340 : CollatzResearch.WordTrace tailWord_445340 prefixEnd_445340 228673474673392838901925 := by
  unfold tailWord_445340
  simp only [CollatzResearch.WordTrace]
  refine ⟨8121442103308356430910737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10828589471077808574547649 8121442103308356430910737)
  ·
    refine ⟨6091081577481267323183053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8121442103308356430910737 6091081577481267323183053)
    ·
      refine ⟨2284155591555475246193645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6091081577481267323183053 2284155591555475246193645)
      ·
        refine ⟨856558346833303217322617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2284155591555475246193645 856558346833303217322617)
        ·
          refine ⟨642418760124977412991963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856558346833303217322617 642418760124977412991963)
          ·
            refine ⟨963628140187466119487945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642418760124977412991963 963628140187466119487945)
            ·
              refine ⟨722721105140599589615959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963628140187466119487945 722721105140599589615959)
              ·
                refine ⟨1084081657710899384423939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722721105140599589615959 1084081657710899384423939)
                ·
                  refine ⟨1626122486566349076635909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1084081657710899384423939 1626122486566349076635909)
                  ·
                    refine ⟨304897966231190451869233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1626122486566349076635909 304897966231190451869233)
                    ·
                      refine ⟨228673474673392838901925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 304897966231190451869233 228673474673392838901925)
                      ·
                        rfl

theorem cell23_445340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_445340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445340 prefixEnd_445340 := by exact prefixLift 445340
  have htrace : WordTrace (prefixWord ++ tailWord_445340) baseStart_445340 baseEnd_445340 := by
    simpa [prefixWord, tailWord_445340, baseEnd_445340] using wordTrace_append hprefix tailTrace_445340
  have hstable : (prefixWord ++ tailWord_445340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445340).length < 2 ^ (prefixWord ++ tailWord_445340).sum := by decide
  have hdescent : baseEnd_445340 < baseStart_445340 := by decide
  rcases family_descends (prefixWord ++ tailWord_445340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445346 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 7]
def baseStart_445346 : Nat := 118140960795 + 445346 * 2 ^ 59
def prefixEnd_445346 : Nat := 4983230072969 + 3 ^ 40 * 445346 * 2
def baseEnd_445346 : Nat := 25408506173035535047433

theorem tailTrace_445346 : CollatzResearch.WordTrace tailWord_445346 prefixEnd_445346 25408506173035535047433 := by
  unfold tailWord_445346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4060775761148743971634973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10828735363063317257693261 4060775761148743971634973)
  ·
    refine ⟨1522790910430778989363115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4060775761148743971634973 1522790910430778989363115)
    ·
      refine ⟨2284186365646168484044673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1522790910430778989363115 2284186365646168484044673)
      ·
        refine ⟨1713139774234626363033505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2284186365646168484044673 1713139774234626363033505)
        ·
          refine ⟨1284854830675969772275129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1713139774234626363033505 1284854830675969772275129)
          ·
            refine ⟨963641123006977329206347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1284854830675969772275129 963641123006977329206347)
            ·
              refine ⟨1445461684510465993809521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963641123006977329206347 1445461684510465993809521)
              ·
                refine ⟨1084096263382849495357141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445461684510465993809521 1084096263382849495357141)
                ·
                  refine ⟨25408506173035535047433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1084096263382849495357141 25408506173035535047433)
                  ·
                    rfl

theorem cell23_445346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_445346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445346 prefixEnd_445346 := by exact prefixLift 445346
  have htrace : WordTrace (prefixWord ++ tailWord_445346) baseStart_445346 baseEnd_445346 := by
    simpa [prefixWord, tailWord_445346, baseEnd_445346] using wordTrace_append hprefix tailTrace_445346
  have hstable : (prefixWord ++ tailWord_445346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445346).length < 2 ^ (prefixWord ++ tailWord_445346).sum := by decide
  have hdescent : baseEnd_445346 < baseStart_445346 := by decide
  rcases family_descends (prefixWord ++ tailWord_445346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445359 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 2, 5]
def baseStart_445359 : Nat := 118140960795 + 445359 * 2 ^ 59
def prefixEnd_445359 : Nat := 4983230072969 + 3 ^ 40 * 445359 * 2
def baseEnd_445359 : Nat := 76227743601942754854779

theorem tailTrace_445359 : CollatzResearch.WordTrace tailWord_445359 prefixEnd_445359 76227743601942754854779 := by
  unfold tailWord_445359
  simp only [CollatzResearch.WordTrace]
  refine ⟨16243577193547879106763131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10829051462365252737842087 16243577193547879106763131)
  ·
    refine ⟨24365365790321818660144697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16243577193547879106763131 24365365790321818660144697)
    ·
      refine ⟨18274024342741363995108523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24365365790321818660144697 18274024342741363995108523)
      ·
        refine ⟨27411036514112045992662785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18274024342741363995108523 27411036514112045992662785)
        ·
          refine ⟨20558277385584034494497089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27411036514112045992662785 20558277385584034494497089)
          ·
            refine ⟨15418708039188025870872817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20558277385584034494497089 15418708039188025870872817)
            ·
              refine ⟨11564031029391019403154613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15418708039188025870872817 11564031029391019403154613)
              ·
                refine ⟨1084127909005408069045745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11564031029391019403154613 1084127909005408069045745)
                ·
                  refine ⟨813095931754056051784309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1084127909005408069045745 813095931754056051784309)
                  ·
                    refine ⟨76227743601942754854779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 813095931754056051784309 76227743601942754854779)
                    ·
                      rfl

theorem cell23_445359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_445359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445359 prefixEnd_445359 := by exact prefixLift 445359
  have htrace : WordTrace (prefixWord ++ tailWord_445359) baseStart_445359 baseEnd_445359 := by
    simpa [prefixWord, tailWord_445359, baseEnd_445359] using wordTrace_append hprefix tailTrace_445359
  have hstable : (prefixWord ++ tailWord_445359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445359).length < 2 ^ (prefixWord ++ tailWord_445359).sum := by decide
  have hdescent : baseEnd_445359 < baseStart_445359 := by decide
  rcases family_descends (prefixWord ++ tailWord_445359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445396 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_445396 : Nat := 118140960795 + 445396 * 2 ^ 59
def prefixEnd_445396 : Nat := 4983230072969 + 3 ^ 40 * 445396 * 2
def baseEnd_445396 : Nat := 228702229590044619801667

theorem tailTrace_445396 : CollatzResearch.WordTrace tailWord_445396 prefixEnd_445396 228702229590044619801667 := by
  unfold tailWord_445396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8122463347206917212930021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10829951129609222950573361 8122463347206917212930021)
  ·
    refine ⟨1522961877601296977424379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8122463347206917212930021 1522961877601296977424379)
    ·
      refine ⟨2284442816401945466136569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1522961877601296977424379 2284442816401945466136569)
      ·
        refine ⟨1713332112301459099602427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2284442816401945466136569 1713332112301459099602427)
        ·
          refine ⟨2569998168452188649403641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1713332112301459099602427 2569998168452188649403641)
          ·
            refine ⟨1927498626339141487052731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2569998168452188649403641 1927498626339141487052731)
            ·
              refine ⟨2891247939508712230579097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927498626339141487052731 2891247939508712230579097)
              ·
                refine ⟨2168435954631534172934323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2891247939508712230579097 2168435954631534172934323)
                ·
                  refine ⟨3252653931947301259401485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168435954631534172934323 3252653931947301259401485)
                  ·
                    refine ⟨1219745224480237972275557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3252653931947301259401485 1219745224480237972275557)
                    ·
                      refine ⟨228702229590044619801667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1219745224480237972275557 228702229590044619801667)
                      ·
                        rfl

theorem cell23_445396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_445396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445396 prefixEnd_445396 := by exact prefixLift 445396
  have htrace : WordTrace (prefixWord ++ tailWord_445396) baseStart_445396 baseEnd_445396 := by
    simpa [prefixWord, tailWord_445396, baseEnd_445396] using wordTrace_append hprefix tailTrace_445396
  have hstable : (prefixWord ++ tailWord_445396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445396).length < 2 ^ (prefixWord ++ tailWord_445396).sum := by decide
  have hdescent : baseEnd_445396 < baseStart_445396 := by decide
  rcases family_descends (prefixWord ++ tailWord_445396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445409 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_445409 : Nat := 118140960795 + 445409 * 2 ^ 59
def prefixEnd_445409 : Nat := 4983230072969 + 3 ^ 40 * 445409 * 2
def baseEnd_445409 : Nat := 228708904838553068939107

theorem tailTrace_445409 : CollatzResearch.WordTrace tailWord_445409 prefixEnd_445409 228708904838553068939107 := by
  unfold tailWord_445409
  simp only [CollatzResearch.WordTrace]
  refine ⟨16245400843366737646083281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10830267228911158430722187 16245400843366737646083281)
  ·
    refine ⟨12184050632525053234562461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16245400843366737646083281 12184050632525053234562461)
    ·
      refine ⟨4569018987196894962960923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12184050632525053234562461 4569018987196894962960923)
      ·
        refine ⟨6853528480795342444441385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569018987196894962960923 6853528480795342444441385)
        ·
          refine ⟨5140146360596506833331039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6853528480795342444441385 5140146360596506833331039)
          ·
            refine ⟨7710219540894760249996559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140146360596506833331039 7710219540894760249996559)
            ·
              refine ⟨11565329311342140374994839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7710219540894760249996559 11565329311342140374994839)
              ·
                refine ⟨17347993967013210562492259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11565329311342140374994839 17347993967013210562492259)
                ·
                  refine ⟨26021990950519815843738389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17347993967013210562492259 26021990950519815843738389)
                  ·
                    refine ⟨1219780825805616367675237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26021990950519815843738389 1219780825805616367675237)
                    ·
                      refine ⟨228708904838553068939107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1219780825805616367675237 228708904838553068939107)
                      ·
                        rfl

theorem cell23_445409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_445409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445409 prefixEnd_445409 := by exact prefixLift 445409
  have htrace : WordTrace (prefixWord ++ tailWord_445409) baseStart_445409 baseEnd_445409 := by
    simpa [prefixWord, tailWord_445409, baseEnd_445409] using wordTrace_append hprefix tailTrace_445409
  have hstable : (prefixWord ++ tailWord_445409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445409).length < 2 ^ (prefixWord ++ tailWord_445409).sum := by decide
  have hdescent : baseEnd_445409 < baseStart_445409 := by decide
  rcases family_descends (prefixWord ++ tailWord_445409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445416 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_445416 : Nat := 118140960795 + 445416 * 2 ^ 59
def prefixEnd_445416 : Nat := 4983230072969 + 3 ^ 40 * 445416 * 2
def baseEnd_445416 : Nat := 228712499203134541551575

theorem tailTrace_445416 : CollatzResearch.WordTrace tailWord_445416 prefixEnd_445416 228712499203134541551575 := by
  unfold tailWord_445416
  simp only [CollatzResearch.WordTrace]
  refine ⟨8122828077170688920794051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10830437436227585227725401 8122828077170688920794051)
  ·
    refine ⟨12184242115756033381191077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8122828077170688920794051 12184242115756033381191077)
    ·
      refine ⟨2284545396704256258973327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12184242115756033381191077 2284545396704256258973327)
      ·
        refine ⟨3426818095056384388459991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284545396704256258973327 3426818095056384388459991)
        ·
          refine ⟨5140227142584576582689987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3426818095056384388459991 5140227142584576582689987)
          ·
            refine ⟨7710340713876864874034981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140227142584576582689987 7710340713876864874034981)
            ·
              refine ⟨1445688883851912163881559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7710340713876864874034981 1445688883851912163881559)
              ·
                refine ⟨2168533325777868245822339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445688883851912163881559 2168533325777868245822339)
                ·
                  refine ⟨3252799988666802368733509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168533325777868245822339 3252799988666802368733509)
                  ·
                    refine ⟨609899997875025444137533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3252799988666802368733509 609899997875025444137533)
                    ·
                      refine ⟨228712499203134541551575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 609899997875025444137533 228712499203134541551575)
                      ·
                        rfl

theorem cell23_445416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_445416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445416 prefixEnd_445416 := by exact prefixLift 445416
  have htrace : WordTrace (prefixWord ++ tailWord_445416) baseStart_445416 baseEnd_445416 := by
    simpa [prefixWord, tailWord_445416, baseEnd_445416] using wordTrace_append hprefix tailTrace_445416
  have hstable : (prefixWord ++ tailWord_445416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445416).length < 2 ^ (prefixWord ++ tailWord_445416).sum := by decide
  have hdescent : baseEnd_445416 < baseStart_445416 := by decide
  rcases family_descends (prefixWord ++ tailWord_445416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445466 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_445466 : Nat := 118140960795 + 445466 * 2 ^ 59
def prefixEnd_445466 : Nat := 4983230072969 + 3 ^ 40 * 445466 * 2
def baseEnd_445466 : Nat := 76246057745286448642115

theorem tailTrace_445466 : CollatzResearch.WordTrace tailWord_445466 prefixEnd_445466 76246057745286448642115 := by
  unfold tailWord_445466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061869951040059095227063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10831653202773490920605501 4061869951040059095227063)
  ·
    refine ⟨6092804926560088642840595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4061869951040059095227063 6092804926560088642840595)
    ·
      refine ⟨9139207389840132964260893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6092804926560088642840595 9139207389840132964260893)
      ·
        refine ⟨3427202771190049861597835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9139207389840132964260893 3427202771190049861597835)
        ·
          refine ⟨5140804156785074792396753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3427202771190049861597835 5140804156785074792396753)
          ·
            refine ⟨3855603117588806094297565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5140804156785074792396753 3855603117588806094297565)
            ·
              refine ⟨1445851169095802285361587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3855603117588806094297565 1445851169095802285361587)
              ·
                refine ⟨2168776753643703428042381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445851169095802285361587 2168776753643703428042381)
                ·
                  refine ⟨813291282616388785515893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2168776753643703428042381 813291282616388785515893)
                  ·
                    refine ⟨76246057745286448642115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 813291282616388785515893 76246057745286448642115)
                    ·
                      rfl

theorem cell23_445466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_445466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445466 prefixEnd_445466 := by exact prefixLift 445466
  have htrace : WordTrace (prefixWord ++ tailWord_445466) baseStart_445466 baseEnd_445466 := by
    simpa [prefixWord, tailWord_445466, baseEnd_445466] using wordTrace_append hprefix tailTrace_445466
  have hstable : (prefixWord ++ tailWord_445466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445466).length < 2 ^ (prefixWord ++ tailWord_445466).sum := by decide
  have hdescent : baseEnd_445466 < baseStart_445466 := by decide
  rcases family_descends (prefixWord ++ tailWord_445466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445483 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 1, 5]
def baseStart_445483 : Nat := 118140960795 + 445483 * 2 ^ 59
def prefixEnd_445483 : Nat := 4983230072969 + 3 ^ 40 * 445483 * 2
def baseEnd_445483 : Nat := 76248967468995259804589

theorem tailTrace_445483 : CollatzResearch.WordTrace tailWord_445483 prefixEnd_445483 76248967468995259804589 := by
  unfold tailWord_445483
  simp only [CollatzResearch.WordTrace]
  refine ⟨16248099845098648284277103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10832066563399098856184735 16248099845098648284277103)
  ·
    refine ⟨24372149767647972426415655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16248099845098648284277103 24372149767647972426415655)
    ·
      refine ⟨36558224651471958639623483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24372149767647972426415655 36558224651471958639623483)
      ·
        refine ⟨54837336977207937959435225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36558224651471958639623483 54837336977207937959435225)
        ·
          refine ⟨41128002732905953469576419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54837336977207937959435225 41128002732905953469576419)
          ·
            refine ⟨61692004099358930204364629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41128002732905953469576419 61692004099358930204364629)
            ·
              refine ⟨361476586519681231666199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 61692004099358930204364629 361476586519681231666199)
              ·
                refine ⟨542214879779521847499299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361476586519681231666199 542214879779521847499299)
                ·
                  refine ⟨813322319669282771248949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542214879779521847499299 813322319669282771248949)
                  ·
                    refine ⟨76248967468995259804589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 813322319669282771248949 76248967468995259804589)
                    ·
                      rfl

theorem cell23_445483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 5].length) (baseStart_445483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445483 prefixEnd_445483 := by exact prefixLift 445483
  have htrace : WordTrace (prefixWord ++ tailWord_445483) baseStart_445483 baseEnd_445483 := by
    simpa [prefixWord, tailWord_445483, baseEnd_445483] using wordTrace_append hprefix tailTrace_445483
  have hstable : (prefixWord ++ tailWord_445483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445483).length < 2 ^ (prefixWord ++ tailWord_445483).sum := by decide
  have hdescent : baseEnd_445483 < baseStart_445483 := by decide
  rcases family_descends (prefixWord ++ tailWord_445483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445497 : List Nat := [1, 2, 1, 5, 2, 2, 1, 4, 1, 1, 3]
def baseStart_445497 : Nat := 118140960795 + 445497 * 2 ^ 59
def prefixEnd_445497 : Nat := 4983230072969 + 3 ^ 40 * 445497 * 2
def baseEnd_445497 : Nat := 228754091136148724638703

theorem tailTrace_445497 : CollatzResearch.WordTrace tailWord_445497 prefixEnd_445497 228754091136148724638703 := by
  unfold tailWord_445497
  simp only [CollatzResearch.WordTrace]
  refine ⟨16248610467047928675286745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10832406978031952450191163 16248610467047928675286745)
  ·
    refine ⟨12186457850285946506465059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16248610467047928675286745 12186457850285946506465059)
    ·
      refine ⟨18279686775428919759697589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12186457850285946506465059 18279686775428919759697589)
      ·
        refine ⟨1713720635196461227471649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18279686775428919759697589 1713720635196461227471649)
        ·
          refine ⟨1285290476397345920603737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1713720635196461227471649 1285290476397345920603737)
          ·
            refine ⟨963967857298009440452803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285290476397345920603737 963967857298009440452803)
            ·
              refine ⟨1445951785947014160679205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963967857298009440452803 1445951785947014160679205)
              ·
                refine ⟨271115959865065155127351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1445951785947014160679205 271115959865065155127351)
                ·
                  refine ⟨406673939797597732691027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271115959865065155127351 406673939797597732691027)
                  ·
                    refine ⟨610010909696396599036541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 406673939797597732691027 610010909696396599036541)
                    ·
                      refine ⟨228754091136148724638703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 610010909696396599036541 228754091136148724638703)
                      ·
                        rfl

theorem cell23_445497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_445497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445497 prefixEnd_445497 := by exact prefixLift 445497
  have htrace : WordTrace (prefixWord ++ tailWord_445497) baseStart_445497 baseEnd_445497 := by
    simpa [prefixWord, tailWord_445497, baseEnd_445497] using wordTrace_append hprefix tailTrace_445497
  have hstable : (prefixWord ++ tailWord_445497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445497).length < 2 ^ (prefixWord ++ tailWord_445497).sum := by decide
  have hdescent : baseEnd_445497 < baseStart_445497 := by decide
  rcases family_descends (prefixWord ++ tailWord_445497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445534 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_445534 : Nat := 118140960795 + 445534 * 2 ^ 59
def prefixEnd_445534 : Nat := 4983230072969 + 3 ^ 40 * 445534 * 2
def baseEnd_445534 : Nat := 76257696640121693292011

theorem tailTrace_445534 : CollatzResearch.WordTrace tailWord_445534 prefixEnd_445534 76257696640121693292011 := by
  unfold tailWord_445534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031244995989235499297957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10833306645275922662922437 2031244995989235499297957)
  ·
    refine ⟨380858436747981656118367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2031244995989235499297957 380858436747981656118367)
    ·
      refine ⟨571287655121972484177551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380858436747981656118367 571287655121972484177551)
      ·
        refine ⟨856931482682958726266327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571287655121972484177551 856931482682958726266327)
        ·
          refine ⟨1285397224024438089399491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856931482682958726266327 1285397224024438089399491)
          ·
            refine ⟨1928095836036657134099237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285397224024438089399491 1928095836036657134099237)
            ·
              refine ⟨361517969256873212643607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1928095836036657134099237 361517969256873212643607)
              ·
                refine ⟨542276953885309818965411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361517969256873212643607 542276953885309818965411)
                ·
                  refine ⟨813415430827964728448117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542276953885309818965411 813415430827964728448117)
                  ·
                    refine ⟨76257696640121693292011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 813415430827964728448117 76257696640121693292011)
                    ·
                      rfl

theorem cell23_445534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_445534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445534 prefixEnd_445534 := by exact prefixLift 445534
  have htrace : WordTrace (prefixWord ++ tailWord_445534) baseStart_445534 baseEnd_445534 := by
    simpa [prefixWord, tailWord_445534, baseEnd_445534] using wordTrace_append hprefix tailTrace_445534
  have hstable : (prefixWord ++ tailWord_445534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445534).length < 2 ^ (prefixWord ++ tailWord_445534).sum := by decide
  have hdescent : baseEnd_445534 < baseStart_445534 := by decide
  rcases family_descends (prefixWord ++ tailWord_445534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445537 : List Nat := [1, 2, 3, 1, 1, 2, 3, 5, 1, 2, 2]
def baseStart_445537 : Nat := 118140960795 + 445537 * 2 ^ 59
def prefixEnd_445537 : Nat := 4983230072969 + 3 ^ 40 * 445537 * 2
def baseEnd_445537 : Nat := 228774630362328568138519

theorem tailTrace_445537 : CollatzResearch.WordTrace tailWord_445537 prefixEnd_445537 228774630362328568138519 := by
  unfold tailWord_445537
  simp only [CollatzResearch.WordTrace]
  refine ⟨16250069386903015506742865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10833379591268677004495243 16250069386903015506742865)
  ·
    refine ⟨12187552040177261630057149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16250069386903015506742865 12187552040177261630057149)
    ·
      refine ⟨4570332015066473111271431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12187552040177261630057149 4570332015066473111271431)
      ·
        refine ⟨6855498022599709666907147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4570332015066473111271431 6855498022599709666907147)
        ·
          refine ⟨10283247033899564500360721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6855498022599709666907147 10283247033899564500360721)
          ·
            refine ⟨7712435275424673375270541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10283247033899564500360721 7712435275424673375270541)
            ·
              refine ⟨2892163228284252515726453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7712435275424673375270541 2892163228284252515726453)
              ·
                refine ⟨271140302651648673349355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2892163228284252515726453 271140302651648673349355)
                ·
                  refine ⟨406710453977473010024033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271140302651648673349355 406710453977473010024033)
                  ·
                    refine ⟨305032840483104757518025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 406710453977473010024033 305032840483104757518025)
                    ·
                      refine ⟨228774630362328568138519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305032840483104757518025 228774630362328568138519)
                      ·
                        rfl

theorem cell23_445537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_445537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445537 prefixEnd_445537 := by exact prefixLift 445537
  have htrace : WordTrace (prefixWord ++ tailWord_445537) baseStart_445537 baseEnd_445537 := by
    simpa [prefixWord, tailWord_445537, baseEnd_445537] using wordTrace_append hprefix tailTrace_445537
  have hstable : (prefixWord ++ tailWord_445537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445537).length < 2 ^ (prefixWord ++ tailWord_445537).sum := by decide
  have hdescent : baseEnd_445537 < baseStart_445537 := by decide
  rcases family_descends (prefixWord ++ tailWord_445537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445563 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 5, 3, 2]
def baseStart_445563 : Nat := 118140960795 + 445563 * 2 ^ 59
def prefixEnd_445563 : Nat := 4983230072969 + 3 ^ 40 * 445563 * 2
def baseEnd_445563 : Nat := 228787980859345466413399

theorem tailTrace_445563 : CollatzResearch.WordTrace tailWord_445563 prefixEnd_445563 228787980859345466413399 := by
  unfold tailWord_445563
  simp only [CollatzResearch.WordTrace]
  refine ⟨16251017684808821947189343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10834011789872547964792895 16251017684808821947189343)
  ·
    refine ⟨24376526527213232920784015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16251017684808821947189343 24376526527213232920784015)
    ·
      refine ⟨36564789790819849381176023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24376526527213232920784015 36564789790819849381176023)
      ·
        refine ⟨54847184686229774071764035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36564789790819849381176023 54847184686229774071764035)
        ·
          refine ⟨82270777029344661107646053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54847184686229774071764035 82270777029344661107646053)
          ·
            refine ⟨15425770693002123957683635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82270777029344661107646053 15425770693002123957683635)
            ·
              refine ⟨23138656039503185936525453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15425770693002123957683635 23138656039503185936525453)
              ·
                refine ⟨8676996014813694726197045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23138656039503185936525453 8676996014813694726197045)
                ·
                  refine ⟨813468376388783880580973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8676996014813694726197045 813468376388783880580973)
                  ·
                    refine ⟨305050641145793955217865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 813468376388783880580973 305050641145793955217865)
                    ·
                      refine ⟨228787980859345466413399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305050641145793955217865 228787980859345466413399)
                      ·
                        rfl

theorem cell23_445563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 3, 2].length) (baseStart_445563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445563 prefixEnd_445563 := by exact prefixLift 445563
  have htrace : WordTrace (prefixWord ++ tailWord_445563) baseStart_445563 baseEnd_445563 := by
    simpa [prefixWord, tailWord_445563, baseEnd_445563] using wordTrace_append hprefix tailTrace_445563
  have hstable : (prefixWord ++ tailWord_445563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445563).length < 2 ^ (prefixWord ++ tailWord_445563).sum := by decide
  have hdescent : baseEnd_445563 < baseStart_445563 := by decide
  rcases family_descends (prefixWord ++ tailWord_445563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445650 : List Nat := [3, 2, 2, 2, 1, 1, 2, 5, 5]
def baseStart_445650 : Nat := 118140960795 + 445650 * 2 ^ 59
def prefixEnd_445650 : Nat := 4983230072969 + 3 ^ 40 * 445650 * 2
def baseEnd_445650 : Nat := 25425850408476291780611

theorem tailTrace_445650 : CollatzResearch.WordTrace tailWord_445650 prefixEnd_445650 25425850408476291780611 := by
  unfold tailWord_445650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4063547708873408951401601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10836127223662423870404269 4063547708873408951401601)
  ·
    refine ⟨3047660781655056713551201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4063547708873408951401601 3047660781655056713551201)
    ·
      refine ⟨2285745586241292535163401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3047660781655056713551201 2285745586241292535163401)
      ·
        refine ⟨1714309189680969401372551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2285745586241292535163401 1714309189680969401372551)
        ·
          refine ⟨2571463784521454102058827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714309189680969401372551 2571463784521454102058827)
          ·
            refine ⟨3857195676782181153088241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571463784521454102058827 3857195676782181153088241)
            ·
              refine ⟨2892896757586635864816181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3857195676782181153088241 2892896757586635864816181)
              ·
                refine ⟨271209071023747112326517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2892896757586635864816181 271209071023747112326517)
                ·
                  refine ⟨25425850408476291780611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 271209071023747112326517 25425850408476291780611)
                  ·
                    rfl

theorem cell23_445650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_445650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445650 prefixEnd_445650 := by exact prefixLift 445650
  have htrace : WordTrace (prefixWord ++ tailWord_445650) baseStart_445650 baseEnd_445650 := by
    simpa [prefixWord, tailWord_445650, baseEnd_445650] using wordTrace_append hprefix tailTrace_445650
  have hstable : (prefixWord ++ tailWord_445650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445650).length < 2 ^ (prefixWord ++ tailWord_445650).sum := by decide
  have hdescent : baseEnd_445650 < baseStart_445650 := by decide
  rcases family_descends (prefixWord ++ tailWord_445650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445661 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_445661 : Nat := 118140960795 + 445661 * 2 ^ 59
def prefixEnd_445661 : Nat := 4983230072969 + 3 ^ 40 * 445661 * 2
def baseEnd_445661 : Nat := 228838301963486082987949

theorem tailTrace_445661 : CollatzResearch.WordTrace tailWord_445661 prefixEnd_445661 228838301963486082987949 := by
  unfold tailWord_445661
  simp only [CollatzResearch.WordTrace]
  refine ⟨16254592038453784684256837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10836394692302523122837891 16254592038453784684256837)
  ·
    refine ⟨3047736007210084628298157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16254592038453784684256837 3047736007210084628298157)
    ·
      refine ⟨1142901002703781735611809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3047736007210084628298157 1142901002703781735611809)
      ·
        refine ⟨857175752027836301708857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1142901002703781735611809 857175752027836301708857)
        ·
          refine ⟨642881814020877226281643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857175752027836301708857 642881814020877226281643)
          ·
            refine ⟨964322721031315839422465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642881814020877226281643 964322721031315839422465)
            ·
              refine ⟨723242040773486879566849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964322721031315839422465 723242040773486879566849)
              ·
                refine ⟨542431530580115159675137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723242040773486879566849 542431530580115159675137)
                ·
                  refine ⟨406823647935086369756353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542431530580115159675137 406823647935086369756353)
                  ·
                    refine ⟨305117735951314777317265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 406823647935086369756353 305117735951314777317265)
                    ·
                      refine ⟨228838301963486082987949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305117735951314777317265 228838301963486082987949)
                      ·
                        rfl

theorem cell23_445661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_445661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445661 prefixEnd_445661 := by exact prefixLift 445661
  have htrace : WordTrace (prefixWord ++ tailWord_445661) baseStart_445661 baseEnd_445661 := by
    simpa [prefixWord, tailWord_445661, baseEnd_445661] using wordTrace_append hprefix tailTrace_445661
  have hstable : (prefixWord ++ tailWord_445661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445661).length < 2 ^ (prefixWord ++ tailWord_445661).sum := by decide
  have hdescent : baseEnd_445661 < baseStart_445661 := by decide
  rcases family_descends (prefixWord ++ tailWord_445661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445663 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 2, 5]
def baseStart_445663 : Nat := 118140960795 + 445663 * 2 ^ 59
def prefixEnd_445663 : Nat := 4983230072969 + 3 ^ 40 * 445663 * 2
def baseEnd_445663 : Nat := 76279776308265025054313

theorem tailTrace_445663 : CollatzResearch.WordTrace tailWord_445663 prefixEnd_445663 76279776308265025054313 := by
  unfold tailWord_445663
  simp only [CollatzResearch.WordTrace]
  refine ⟨16254664984446539025829643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10836443322964359350553095 16254664984446539025829643)
  ·
    refine ⟨24381997476669808538744465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16254664984446539025829643 24381997476669808538744465)
    ·
      refine ⟨18286498107502356404058349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24381997476669808538744465 18286498107502356404058349)
      ·
        refine ⟨6857436790313383651521881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18286498107502356404058349 6857436790313383651521881)
        ·
          refine ⟨5143077592735037738641411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6857436790313383651521881 5143077592735037738641411)
          ·
            refine ⟨7714616389102556607962117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143077592735037738641411 7714616389102556607962117)
            ·
              refine ⟨1446490572956729363992897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7714616389102556607962117 1446490572956729363992897)
              ·
                refine ⟨1084867929717547022994673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1446490572956729363992897 1084867929717547022994673)
                ·
                  refine ⟨813650947288160267246005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1084867929717547022994673 813650947288160267246005)
                  ·
                    refine ⟨76279776308265025054313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 813650947288160267246005 76279776308265025054313)
                    ·
                      rfl

theorem cell23_445663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_445663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445663 prefixEnd_445663 := by exact prefixLift 445663
  have htrace : WordTrace (prefixWord ++ tailWord_445663) baseStart_445663 baseEnd_445663 := by
    simpa [prefixWord, tailWord_445663, baseEnd_445663] using wordTrace_append hprefix tailTrace_445663
  have hstable : (prefixWord ++ tailWord_445663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445663).length < 2 ^ (prefixWord ++ tailWord_445663).sum := by decide
  have hdescent : baseEnd_445663 < baseStart_445663 := by decide
  rcases family_descends (prefixWord ++ tailWord_445663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445684 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 7]
def baseStart_445684 : Nat := 118140960795 + 445684 * 2 ^ 59
def prefixEnd_445684 : Nat := 4983230072969 + 3 ^ 40 * 445684 * 2
def baseEnd_445684 : Nat := 25427790224282165888927

theorem tailTrace_445684 : CollatzResearch.WordTrace tailWord_445684 prefixEnd_445684 25427790224282165888927 := by
  unfold tailWord_445684
  simp only [CollatzResearch.WordTrace]
  refine ⟨8127715458685229806172053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10836953944913639741562737 8127715458685229806172053)
  ·
    refine ⟨380986662125870147164315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8127715458685229806172053 380986662125870147164315)
    ·
      refine ⟨571479993188805220746473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380986662125870147164315 571479993188805220746473)
      ·
        refine ⟨428609994891603915559855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571479993188805220746473 428609994891603915559855)
        ·
          refine ⟨642914992337405873339783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428609994891603915559855 642914992337405873339783)
          ·
            refine ⟨964372488506108810009675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642914992337405873339783 964372488506108810009675)
            ·
              refine ⟨1446558732759163215014513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964372488506108810009675 1446558732759163215014513)
              ·
                refine ⟨1084919049569372411260885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1446558732759163215014513 1084919049569372411260885)
                ·
                  refine ⟨25427790224282165888927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1084919049569372411260885 25427790224282165888927)
                  ·
                    rfl

theorem cell23_445684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_445684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445684 prefixEnd_445684 := by exact prefixLift 445684
  have htrace : WordTrace (prefixWord ++ tailWord_445684) baseStart_445684 baseEnd_445684 := by
    simpa [prefixWord, tailWord_445684, baseEnd_445684] using wordTrace_append hprefix tailTrace_445684
  have hstable : (prefixWord ++ tailWord_445684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445684).length < 2 ^ (prefixWord ++ tailWord_445684).sum := by decide
  have hdescent : baseEnd_445684 < baseStart_445684 := by decide
  rcases family_descends (prefixWord ++ tailWord_445684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445700 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_445700 : Nat := 118140960795 + 445700 * 2 ^ 59
def prefixEnd_445700 : Nat := 4983230072969 + 3 ^ 40 * 445700 * 2
def baseEnd_445700 : Nat := 228858327709011430400269

theorem tailTrace_445700 : CollatzResearch.WordTrace tailWord_445700 prefixEnd_445700 228858327709011430400269 := by
  unfold tailWord_445700
  simp only [CollatzResearch.WordTrace]
  refine ⟨8128007242656247172463277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10837342990208329563284369 8128007242656247172463277)
  ·
    refine ⟨3048002715996092689673729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8128007242656247172463277 3048002715996092689673729)
    ·
      refine ⟨2286002036997069517255297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3048002715996092689673729 2286002036997069517255297)
      ·
        refine ⟨1714501527747802137941473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2286002036997069517255297 1714501527747802137941473)
        ·
          refine ⟨1285876145810851603456105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1714501527747802137941473 1285876145810851603456105)
          ·
            refine ⟨964407109358138702592079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285876145810851603456105 964407109358138702592079)
            ·
              refine ⟨1446610664037208053888119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964407109358138702592079 1446610664037208053888119)
              ·
                refine ⟨2169915996055812080832179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446610664037208053888119 2169915996055812080832179)
                ·
                  refine ⟨3254873994083718121248269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169915996055812080832179 3254873994083718121248269)
                  ·
                    refine ⟨1220577747781394295468101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3254873994083718121248269 1220577747781394295468101)
                    ·
                      refine ⟨228858327709011430400269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1220577747781394295468101 228858327709011430400269)
                      ·
                        rfl

theorem cell23_445700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_445700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445700 prefixEnd_445700 := by exact prefixLift 445700
  have htrace : WordTrace (prefixWord ++ tailWord_445700) baseStart_445700 baseEnd_445700 := by
    simpa [prefixWord, tailWord_445700, baseEnd_445700] using wordTrace_append hprefix tailTrace_445700
  have hstable : (prefixWord ++ tailWord_445700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445700).length < 2 ^ (prefixWord ++ tailWord_445700).sum := by decide
  have hdescent : baseEnd_445700 < baseStart_445700 := by decide
  rcases family_descends (prefixWord ++ tailWord_445700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445727 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 3, 4]
def baseStart_445727 : Nat := 118140960795 + 445727 * 2 ^ 59
def prefixEnd_445727 : Nat := 4983230072969 + 3 ^ 40 * 445727 * 2
def baseEnd_445727 : Nat := 76290730562227608254215

theorem tailTrace_445727 : CollatzResearch.WordTrace tailWord_445727 prefixEnd_445727 76290730562227608254215 := by
  unfold tailWord_445727
  simp only [CollatzResearch.WordTrace]
  refine ⟨16256999256214677956159435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10837999504143118637439623 16256999256214677956159435)
  ·
    refine ⟨24385498884322016934239153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16256999256214677956159435 24385498884322016934239153)
    ·
      refine ⟨18289124163241512700679365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24385498884322016934239153 18289124163241512700679365)
      ·
        refine ⟨3429210780607783631377381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18289124163241512700679365 3429210780607783631377381)
        ·
          refine ⟨642977021363959430883259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3429210780607783631377381 642977021363959430883259)
          ·
            refine ⟨964465532045939146324889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642977021363959430883259 964465532045939146324889)
            ·
              refine ⟨723349149034454359743667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964465532045939146324889 723349149034454359743667)
              ·
                refine ⟨1085023723551681539615501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723349149034454359743667 1085023723551681539615501)
                ·
                  refine ⟨406883896331880577355813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1085023723551681539615501 406883896331880577355813)
                  ·
                    refine ⟨76290730562227608254215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 406883896331880577355813 76290730562227608254215)
                    ·
                      rfl

theorem cell23_445727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 4].length) (baseStart_445727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445727 prefixEnd_445727 := by exact prefixLift 445727
  have htrace : WordTrace (prefixWord ++ tailWord_445727) baseStart_445727 baseEnd_445727 := by
    simpa [prefixWord, tailWord_445727, baseEnd_445727] using wordTrace_append hprefix tailTrace_445727
  have hstable : (prefixWord ++ tailWord_445727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445727).length < 2 ^ (prefixWord ++ tailWord_445727).sum := by decide
  have hdescent : baseEnd_445727 < baseStart_445727 := by decide
  rcases family_descends (prefixWord ++ tailWord_445727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445760 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 1, 5, 2]
def baseStart_445760 : Nat := 118140960795 + 445760 * 2 ^ 59
def prefixEnd_445760 : Nat := 4983230072969 + 3 ^ 40 * 445760 * 2
def baseEnd_445760 : Nat := 228889136548281195649993

theorem tailTrace_445760 : CollatzResearch.WordTrace tailWord_445760 prefixEnd_445760 228889136548281195649993 := by
  unfold tailWord_445760
  simp only [CollatzResearch.WordTrace]
  refine ⟨8129101432547562296055367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10838801910063416394740489 8129101432547562296055367)
  ·
    refine ⟨12193652148821343444083051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8129101432547562296055367 12193652148821343444083051)
    ·
      refine ⟨18290478223232015166124577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12193652148821343444083051 18290478223232015166124577)
      ·
        refine ⟨13717858667424011374593433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18290478223232015166124577 13717858667424011374593433)
        ·
          refine ⟨10288394000568008530945075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13717858667424011374593433 10288394000568008530945075)
          ·
            refine ⟨15432591000852012796417613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10288394000568008530945075 15432591000852012796417613)
            ·
              refine ⟨5787221625319504798656605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15432591000852012796417613 5787221625319504798656605)
              ·
                refine ⟨2170208109494814299496227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5787221625319504798656605 2170208109494814299496227)
                ·
                  refine ⟨3255312164242221449244341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170208109494814299496227 3255312164242221449244341)
                  ·
                    refine ⟨305185515397708260866657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3255312164242221449244341 305185515397708260866657)
                    ·
                      refine ⟨228889136548281195649993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305185515397708260866657 228889136548281195649993)
                      ·
                        rfl

theorem cell23_445760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 5, 2].length) (baseStart_445760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445760 prefixEnd_445760 := by exact prefixLift 445760
  have htrace : WordTrace (prefixWord ++ tailWord_445760) baseStart_445760 baseEnd_445760 := by
    simpa [prefixWord, tailWord_445760, baseEnd_445760] using wordTrace_append hprefix tailTrace_445760
  have hstable : (prefixWord ++ tailWord_445760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445760).length < 2 ^ (prefixWord ++ tailWord_445760).sum := by decide
  have hdescent : baseEnd_445760 < baseStart_445760 := by decide
  rcases family_descends (prefixWord ++ tailWord_445760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445761 : List Nat := [1, 2, 5, 2, 1, 3, 1, 3, 1, 4]
def baseStart_445761 : Nat := 118140960795 + 445761 * 2 ^ 59
def prefixEnd_445761 : Nat := 4983230072969 + 3 ^ 40 * 445761 * 2
def baseEnd_445761 : Nat := 76296550009645230579163

theorem tailTrace_445761 : CollatzResearch.WordTrace tailWord_445761 prefixEnd_445761 76296550009645230579163 := by
  unfold tailWord_445761
  simp only [CollatzResearch.WordTrace]
  refine ⟨16258239338091501762897137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10838826225394334508598091 16258239338091501762897137)
  ·
    refine ⟨12193679503568626322172853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16258239338091501762897137 12193679503568626322172853)
    ·
      refine ⟨1143157453459558717703705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12193679503568626322172853 1143157453459558717703705)
      ·
        refine ⟨857368090094669038277779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1143157453459558717703705 857368090094669038277779)
        ·
          refine ⟨1286052135142003557416669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857368090094669038277779 1286052135142003557416669)
          ·
            refine ⟨482269550678251334031251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1286052135142003557416669 482269550678251334031251)
            ·
              refine ⟨723404326017377001046877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482269550678251334031251 723404326017377001046877)
              ·
                refine ⟨271276622256516375392579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 723404326017377001046877 271276622256516375392579)
                ·
                  refine ⟨406914933384774563088869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271276622256516375392579 406914933384774563088869)
                  ·
                    refine ⟨76296550009645230579163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 406914933384774563088869 76296550009645230579163)
                    ·
                      rfl

theorem cell23_445761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_445761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445761 prefixEnd_445761 := by exact prefixLift 445761
  have htrace : WordTrace (prefixWord ++ tailWord_445761) baseStart_445761 baseEnd_445761 := by
    simpa [prefixWord, tailWord_445761, baseEnd_445761] using wordTrace_append hprefix tailTrace_445761
  have hstable : (prefixWord ++ tailWord_445761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445761).length < 2 ^ (prefixWord ++ tailWord_445761).sum := by decide
  have hdescent : baseEnd_445761 < baseStart_445761 := by decide
  rcases family_descends (prefixWord ++ tailWord_445761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445777 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 2, 3, 2]
def baseStart_445777 : Nat := 118140960795 + 445777 * 2 ^ 59
def prefixEnd_445777 : Nat := 4983230072969 + 3 ^ 40 * 445777 * 2
def baseEnd_445777 : Nat := 228897865719407629137415

theorem tailTrace_445777 : CollatzResearch.WordTrace tailWord_445777 prefixEnd_445777 228897865719407629137415 := by
  unfold tailWord_445777
  simp only [CollatzResearch.WordTrace]
  refine ⟨16258822906033536495479585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10839215270689024330319723 16258822906033536495479585)
  ·
    refine ⟨12194117179525152371609689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16258822906033536495479585 12194117179525152371609689)
    ·
      refine ⟨9145587884643864278707267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12194117179525152371609689 9145587884643864278707267)
      ·
        refine ⟨13718381826965796418060901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9145587884643864278707267 13718381826965796418060901)
        ·
          refine ⟨2572196592556086828386419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13718381826965796418060901 2572196592556086828386419)
          ·
            refine ⟨3858294888834130242579629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572196592556086828386419 3858294888834130242579629)
            ·
              refine ⟨1446860583312798840967361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3858294888834130242579629 1446860583312798840967361)
              ·
                refine ⟨1085145437484599130725521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1446860583312798840967361 1085145437484599130725521)
                ·
                  refine ⟨813859078113449348044141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1085145437484599130725521 813859078113449348044141)
                  ·
                    refine ⟨305197154292543505516553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 813859078113449348044141 305197154292543505516553)
                    ·
                      refine ⟨228897865719407629137415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305197154292543505516553 228897865719407629137415)
                      ·
                        rfl

theorem cell23_445777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 3, 2].length) (baseStart_445777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445777 prefixEnd_445777 := by exact prefixLift 445777
  have htrace : WordTrace (prefixWord ++ tailWord_445777) baseStart_445777 baseEnd_445777 := by
    simpa [prefixWord, tailWord_445777, baseEnd_445777] using wordTrace_append hprefix tailTrace_445777
  have hstable : (prefixWord ++ tailWord_445777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445777).length < 2 ^ (prefixWord ++ tailWord_445777).sum := by decide
  have hdescent : baseEnd_445777 < baseStart_445777 := by decide
  rcases family_descends (prefixWord ++ tailWord_445777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445807 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 5, 2, 2]
def baseStart_445807 : Nat := 118140960795 + 445807 * 2 ^ 59
def prefixEnd_445807 : Nat := 4983230072969 + 3 ^ 40 * 445807 * 2
def baseEnd_445807 : Nat := 228913270139042511762277

theorem tailTrace_445807 : CollatzResearch.WordTrace tailWord_445807 prefixEnd_445807 228913270139042511762277 := by
  unfold tailWord_445807
  simp only [CollatzResearch.WordTrace]
  refine ⟨16259917095924851619071675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10839944730616567746047783 16259917095924851619071675)
  ·
    refine ⟨24389875643887277428607513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16259917095924851619071675 24389875643887277428607513)
    ·
      refine ⟨18292406732915458071455635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24389875643887277428607513 18292406732915458071455635)
      ·
        refine ⟨27438610099373187107183453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18292406732915458071455635 27438610099373187107183453)
        ·
          refine ⟨10289478787264945165193795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27438610099373187107183453 10289478787264945165193795)
          ·
            refine ⟨15434218180897417747790693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289478787264945165193795 15434218180897417747790693)
            ·
              refine ⟨2893915908918265827710755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15434218180897417747790693 2893915908918265827710755)
              ·
                refine ⟨4340873863377398741566133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893915908918265827710755 4340873863377398741566133)
                ·
                  refine ⟨406956924691631132021825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4340873863377398741566133 406956924691631132021825)
                  ·
                    refine ⟨305217693518723349016369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 406956924691631132021825 305217693518723349016369)
                    ·
                      refine ⟨228913270139042511762277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305217693518723349016369 228913270139042511762277)
                      ·
                        rfl

theorem cell23_445807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 2, 2].length) (baseStart_445807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445807 prefixEnd_445807 := by exact prefixLift 445807
  have htrace : WordTrace (prefixWord ++ tailWord_445807) baseStart_445807 baseEnd_445807 := by
    simpa [prefixWord, tailWord_445807, baseEnd_445807] using wordTrace_append hprefix tailTrace_445807
  have hstable : (prefixWord ++ tailWord_445807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445807).length < 2 ^ (prefixWord ++ tailWord_445807).sum := by decide
  have hdescent : baseEnd_445807 < baseStart_445807 := by decide
  rcases family_descends (prefixWord ++ tailWord_445807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445820 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_445820 : Nat := 118140960795 + 445820 * 2 ^ 59
def prefixEnd_445820 : Nat := 4983230072969 + 3 ^ 40 * 445820 * 2
def baseEnd_445820 : Nat := 228919945387550960899717

theorem tailTrace_445820 : CollatzResearch.WordTrace tailWord_445820 prefixEnd_445820 228919945387550960899717 := by
  unfold tailWord_445820
  simp only [CollatzResearch.WordTrace]
  refine ⟨8130195622438877419647457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10840260829918503226196609 8130195622438877419647457)
  ·
    refine ⟨6097646716829158064735593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8130195622438877419647457 6097646716829158064735593)
    ·
      refine ⟨4573235037621868548551695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6097646716829158064735593 4573235037621868548551695)
      ·
        refine ⟨6859852556432802822827543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4573235037621868548551695 6859852556432802822827543)
        ·
          refine ⟨10289778834649204234241315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6859852556432802822827543 10289778834649204234241315)
          ·
            refine ⟨15434668251973806351361973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289778834649204234241315 15434668251973806351361973)
            ·
              refine ⟨1447000148622544345440185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15434668251973806351361973 1447000148622544345440185)
              ·
                refine ⟨1085250111466908259080139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447000148622544345440185 1085250111466908259080139)
                ·
                  refine ⟨1627875167200362388620209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085250111466908259080139 1627875167200362388620209)
                  ·
                    refine ⟨1220906375400271791465157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1627875167200362388620209 1220906375400271791465157)
                    ·
                      refine ⟨228919945387550960899717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1220906375400271791465157 228919945387550960899717)
                      ·
                        rfl

theorem cell23_445820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_445820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445820 prefixEnd_445820 := by exact prefixLift 445820
  have htrace : WordTrace (prefixWord ++ tailWord_445820) baseStart_445820 baseEnd_445820 := by
    simpa [prefixWord, tailWord_445820, baseEnd_445820] using wordTrace_append hprefix tailTrace_445820
  have hstable : (prefixWord ++ tailWord_445820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445820).length < 2 ^ (prefixWord ++ tailWord_445820).sum := by decide
  have hdescent : baseEnd_445820 < baseStart_445820 := by decide
  rcases family_descends (prefixWord ++ tailWord_445820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445827 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 5]
def baseStart_445827 : Nat := 118140960795 + 445827 * 2 ^ 59
def prefixEnd_445827 : Nat := 4983230072969 + 3 ^ 40 * 445827 * 2
def baseEnd_445827 : Nat := 228923539752132433512185

theorem tailTrace_445827 : CollatzResearch.WordTrace tailWord_445827 prefixEnd_445827 228923539752132433512185 := by
  unfold tailWord_445827
  simp only [CollatzResearch.WordTrace]
  refine ⟨16260646555852395034799735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10840431037234930023199823 16260646555852395034799735)
  ·
    refine ⟨24390969833778592552199603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16260646555852395034799735 24390969833778592552199603)
    ·
      refine ⟨36586454750667888828299405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24390969833778592552199603 36586454750667888828299405)
      ·
        refine ⟨13719920531500458310612277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36586454750667888828299405 13719920531500458310612277)
        ·
          refine ⟨1286242549828167966619901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13719920531500458310612277 1286242549828167966619901)
          ·
            refine ⟨482340956185562987482463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1286242549828167966619901 482340956185562987482463)
            ·
              refine ⟨723511434278344481223695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482340956185562987482463 723511434278344481223695)
              ·
                refine ⟨1085267151417516721835543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723511434278344481223695 1085267151417516721835543)
                ·
                  refine ⟨1627900727126275082753315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085267151417516721835543 1627900727126275082753315)
                  ·
                    refine ⟨2441851090689412624129973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1627900727126275082753315 2441851090689412624129973)
                    ·
                      refine ⟨228923539752132433512185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2441851090689412624129973 228923539752132433512185)
                      ·
                        rfl

theorem cell23_445827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_445827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445827 prefixEnd_445827 := by exact prefixLift 445827
  have htrace : WordTrace (prefixWord ++ tailWord_445827) baseStart_445827 baseEnd_445827 := by
    simpa [prefixWord, tailWord_445827, baseEnd_445827] using wordTrace_append hprefix tailTrace_445827
  have hstable : (prefixWord ++ tailWord_445827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445827).length < 2 ^ (prefixWord ++ tailWord_445827).sum := by decide
  have hdescent : baseEnd_445827 < baseStart_445827 := by decide
  rcases family_descends (prefixWord ++ tailWord_445827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445864 : List Nat := [2, 1, 6, 1, 2, 1, 3, 7]
def baseStart_445864 : Nat := 118140960795 + 445864 * 2 ^ 59
def prefixEnd_445864 : Nat := 4983230072969 + 3 ^ 40 * 445864 * 2
def baseEnd_445864 : Nat := 8479353279124029212945

theorem tailTrace_445864 : CollatzResearch.WordTrace tailWord_445864 prefixEnd_445864 8479353279124029212945 := by
  unfold tailWord_445864
  simp only [CollatzResearch.WordTrace]
  refine ⟨8130998028359175176948323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10841330704478900235931097 8130998028359175176948323)
  ·
    refine ⟨12196497042538762765422485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8130998028359175176948323 12196497042538762765422485)
    ·
      refine ⟨571710798869004504629179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12196497042538762765422485 571710798869004504629179)
      ·
        refine ⟨857566198303506756943769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571710798869004504629179 857566198303506756943769)
        ·
          refine ⟨643174648727630067707827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857566198303506756943769 643174648727630067707827)
          ·
            refine ⟨964761973091445101561741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643174648727630067707827 964761973091445101561741)
            ·
              refine ⟨361785739909291913085653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 964761973091445101561741 361785739909291913085653)
              ·
                refine ⟨8479353279124029212945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 361785739909291913085653 8479353279124029212945)
                ·
                  rfl

theorem cell23_445864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 7].length) (baseStart_445864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445864 prefixEnd_445864 := by exact prefixLift 445864
  have htrace : WordTrace (prefixWord ++ tailWord_445864) baseStart_445864 baseEnd_445864 := by
    simpa [prefixWord, tailWord_445864, baseEnd_445864] using wordTrace_append hprefix tailTrace_445864
  have hstable : (prefixWord ++ tailWord_445864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445864).length < 2 ^ (prefixWord ++ tailWord_445864).sum := by decide
  have hdescent : baseEnd_445864 < baseStart_445864 := by decide
  rcases family_descends (prefixWord ++ tailWord_445864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445908 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_445908 : Nat := 118140960795 + 445908 * 2 ^ 59
def prefixEnd_445908 : Nat := 4983230072969 + 3 ^ 40 * 445908 * 2
def baseEnd_445908 : Nat := 228965131685146616599313

theorem tailTrace_445908 : CollatzResearch.WordTrace tailWord_445908 prefixEnd_445908 228965131685146616599313 := by
  unfold tailWord_445908
  simp only [CollatzResearch.WordTrace]
  refine ⟨8131800434279472934249189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10842400579039297245665585 8131800434279472934249189)
  ·
    refine ⟨1524712581427401175171723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8131800434279472934249189 1524712581427401175171723)
    ·
      refine ⟨2287068872141101762757585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1524712581427401175171723 2287068872141101762757585)
      ·
        refine ⟨1715301654105826322068189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2287068872141101762757585 1715301654105826322068189)
        ·
          refine ⟨643238120289684870775571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1715301654105826322068189 643238120289684870775571)
          ·
            refine ⟨964857180434527306163357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643238120289684870775571 964857180434527306163357)
            ·
              refine ⟨361821442662947739811259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 964857180434527306163357 361821442662947739811259)
              ·
                refine ⟨542732163994421609716889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361821442662947739811259 542732163994421609716889)
                ·
                  refine ⟨407049122995816207287667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542732163994421609716889 407049122995816207287667)
                  ·
                    refine ⟨610573684493724310931501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 407049122995816207287667 610573684493724310931501)
                    ·
                      refine ⟨228965131685146616599313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 610573684493724310931501 228965131685146616599313)
                      ·
                        rfl

theorem cell23_445908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_445908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445908 prefixEnd_445908 := by exact prefixLift 445908
  have htrace : WordTrace (prefixWord ++ tailWord_445908) baseStart_445908 baseEnd_445908 := by
    simpa [prefixWord, tailWord_445908, baseEnd_445908] using wordTrace_append hprefix tailTrace_445908
  have hstable : (prefixWord ++ tailWord_445908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445908).length < 2 ^ (prefixWord ++ tailWord_445908).sum := by decide
  have hdescent : baseEnd_445908 < baseStart_445908 := by decide
  rcases family_descends (prefixWord ++ tailWord_445908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445914 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2]
def baseStart_445914 : Nat := 118140960795 + 445914 * 2 ^ 59
def prefixEnd_445914 : Nat := 4983230072969 + 3 ^ 40 * 445914 * 2
def baseEnd_445914 : Nat := 228968212569073593124285

theorem tailTrace_445914 : CollatzResearch.WordTrace tailWord_445914 prefixEnd_445914 228968212569073593124285 := by
  unfold tailWord_445914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4065954926634302223304199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10842546471024805928811197 4065954926634302223304199)
  ·
    refine ⟨6098932389951453334956299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4065954926634302223304199 6098932389951453334956299)
    ·
      refine ⟨9148398584927180002434449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6098932389951453334956299 9148398584927180002434449)
      ·
        refine ⟨6861298938695385001825837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9148398584927180002434449 6861298938695385001825837)
        ·
          refine ⟨2572987102010769375684689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6861298938695385001825837 2572987102010769375684689)
          ·
            refine ⟨1929740326508077031763517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2572987102010769375684689 1929740326508077031763517)
            ·
              refine ⟨723652622440528886911319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1929740326508077031763517 723652622440528886911319)
              ·
                refine ⟨1085478933660793330366979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723652622440528886911319 1085478933660793330366979)
                ·
                  refine ⟨1628218400491189995550469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085478933660793330366979 1628218400491189995550469)
                  ·
                    refine ⟨305290950092098124165713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1628218400491189995550469 305290950092098124165713)
                    ·
                      refine ⟨228968212569073593124285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305290950092098124165713 228968212569073593124285)
                      ·
                        rfl

theorem cell23_445914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_445914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445914 prefixEnd_445914 := by exact prefixLift 445914
  have htrace : WordTrace (prefixWord ++ tailWord_445914) baseStart_445914 baseEnd_445914 := by
    simpa [prefixWord, tailWord_445914, baseEnd_445914] using wordTrace_append hprefix tailTrace_445914
  have hstable : (prefixWord ++ tailWord_445914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445914).length < 2 ^ (prefixWord ++ tailWord_445914).sum := by decide
  have hdescent : baseEnd_445914 < baseStart_445914 := by decide
  rcases family_descends (prefixWord ++ tailWord_445914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445954 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 7]
def baseStart_445954 : Nat := 118140960795 + 445954 * 2 ^ 59
def prefixEnd_445954 : Nat := 4983230072969 + 3 ^ 40 * 445954 * 2
def baseEnd_445954 : Nat := 25443194643917048513789

theorem tailTrace_445954 : CollatzResearch.WordTrace tailWord_445954 prefixEnd_445954 25443194643917048513789 := by
  unfold tailWord_445954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4066319656598073931168229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10843519084261530483115277 4066319656598073931168229)
  ·
    refine ⟨762434935612138862094043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4066319656598073931168229 762434935612138862094043)
    ·
      refine ⟨1143652403418208293141065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762434935612138862094043 1143652403418208293141065)
      ·
        refine ⟨857739302563656219855799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1143652403418208293141065 857739302563656219855799)
        ·
          refine ⟨1286608953845484329783699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857739302563656219855799 1286608953845484329783699)
          ·
            refine ⟨1929913430768226494675549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286608953845484329783699 1929913430768226494675549)
            ·
              refine ⟨723717536538084935503331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1929913430768226494675549 723717536538084935503331)
              ·
                refine ⟨1085576304807127403254997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723717536538084935503331 1085576304807127403254997)
                ·
                  refine ⟨25443194643917048513789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1085576304807127403254997 25443194643917048513789)
                  ·
                    rfl

theorem cell23_445954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_445954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445954 prefixEnd_445954 := by exact prefixLift 445954
  have htrace : WordTrace (prefixWord ++ tailWord_445954) baseStart_445954 baseEnd_445954 := by
    simpa [prefixWord, tailWord_445954, baseEnd_445954] using wordTrace_append hprefix tailTrace_445954
  have hstable : (prefixWord ++ tailWord_445954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445954).length < 2 ^ (prefixWord ++ tailWord_445954).sum := by decide
  have hdescent : baseEnd_445954 < baseStart_445954 := by decide
  rcases family_descends (prefixWord ++ tailWord_445954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445957 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 2, 5, 2]
def baseStart_445957 : Nat := 118140960795 + 445957 * 2 ^ 59
def prefixEnd_445957 : Nat := 4983230072969 + 3 ^ 40 * 445957 * 2
def baseEnd_445957 : Nat := 228990292237216924886587

theorem tailTrace_445957 : CollatzResearch.WordTrace tailWord_445957 prefixEnd_445957 228990292237216924886587 := by
  unfold tailWord_445957
  simp only [CollatzResearch.WordTrace]
  refine ⟨16265388045381427237032125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10843592030254284824688083 16265388045381427237032125)
  ·
    refine ⟨6099520517018035213887047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16265388045381427237032125 6099520517018035213887047)
    ·
      refine ⟨9149280775527052820830571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6099520517018035213887047 9149280775527052820830571)
      ·
        refine ⟨13723921163290579231245857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9149280775527052820830571 13723921163290579231245857)
        ·
          refine ⟨10292940872467934423434393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13723921163290579231245857 10292940872467934423434393)
          ·
            refine ⟨7719705654350950817575795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10292940872467934423434393 7719705654350950817575795)
            ·
              refine ⟨11579558481526426226363693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7719705654350950817575795 11579558481526426226363693)
              ·
                refine ⟨4342334430572409834886385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11579558481526426226363693 4342334430572409834886385)
                ·
                  refine ⟨3256750822929307376164789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4342334430572409834886385 3256750822929307376164789)
                  ·
                    refine ⟨305320389649622566515449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3256750822929307376164789 305320389649622566515449)
                    ·
                      refine ⟨228990292237216924886587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305320389649622566515449 228990292237216924886587)
                      ·
                        rfl

theorem cell23_445957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 5, 2].length) (baseStart_445957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445957 prefixEnd_445957 := by exact prefixLift 445957
  have htrace : WordTrace (prefixWord ++ tailWord_445957) baseStart_445957 baseEnd_445957 := by
    simpa [prefixWord, tailWord_445957, baseEnd_445957] using wordTrace_append hprefix tailTrace_445957
  have hstable : (prefixWord ++ tailWord_445957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445957).length < 2 ^ (prefixWord ++ tailWord_445957).sum := by decide
  have hdescent : baseEnd_445957 < baseStart_445957 := by decide
  rcases family_descends (prefixWord ++ tailWord_445957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445960 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_445960 : Nat := 118140960795 + 445960 * 2 ^ 59
def prefixEnd_445960 : Nat := 4983230072969 + 3 ^ 40 * 445960 * 2
def baseEnd_445960 : Nat := 228991832679180413149073

theorem tailTrace_445960 : CollatzResearch.WordTrace tailWord_445960 prefixEnd_445960 228991832679180413149073 := by
  unfold tailWord_445960
  simp only [CollatzResearch.WordTrace]
  refine ⟨8132748732185279374695667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10843664976247039166260889 8132748732185279374695667)
  ·
    refine ⟨12199123098277919062043501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8132748732185279374695667 12199123098277919062043501)
    ·
      refine ⟨4574671161854219648266313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12199123098277919062043501 4574671161854219648266313)
      ·
        refine ⟨3431003371390664736199735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4574671161854219648266313 3431003371390664736199735)
        ·
          refine ⟨5146505057085997104299603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3431003371390664736199735 5146505057085997104299603)
          ·
            refine ⟨7719757585628995656449405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5146505057085997104299603 7719757585628995656449405)
            ·
              refine ⟨2894909094610873371168527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7719757585628995656449405 2894909094610873371168527)
              ·
                refine ⟨4342363641916310056752791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2894909094610873371168527 4342363641916310056752791)
                ·
                  refine ⟨6513545462874465085129187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342363641916310056752791 6513545462874465085129187)
                  ·
                    refine ⟨9770318194311697627693781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6513545462874465085129187 9770318194311697627693781)
                    ·
                      refine ⟨228991832679180413149073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9770318194311697627693781 228991832679180413149073)
                      ·
                        rfl

theorem cell23_445960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_445960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445960 prefixEnd_445960 := by exact prefixLift 445960
  have htrace : WordTrace (prefixWord ++ tailWord_445960) baseStart_445960 baseEnd_445960 := by
    simpa [prefixWord, tailWord_445960, baseEnd_445960] using wordTrace_append hprefix tailTrace_445960
  have hstable : (prefixWord ++ tailWord_445960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445960).length < 2 ^ (prefixWord ++ tailWord_445960).sum := by decide
  have hdescent : baseEnd_445960 < baseStart_445960 := by decide
  rcases family_descends (prefixWord ++ tailWord_445960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445984 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 2, 5]
def baseStart_445984 : Nat := 118140960795 + 445984 * 2 ^ 59
def prefixEnd_445984 : Nat := 4983230072969 + 3 ^ 40 * 445984 * 2
def baseEnd_445984 : Nat := 76334718738296106416321

theorem tailTrace_445984 : CollatzResearch.WordTrace tailWord_445984 prefixEnd_445984 76334718738296106416321 := by
  unfold tailWord_445984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8133186408141805424132503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10844248544189073898843337 8133186408141805424132503)
  ·
    refine ⟨12199779612212708136198755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8133186408141805424132503 12199779612212708136198755)
    ·
      refine ⟨18299669418319062204298133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12199779612212708136198755 18299669418319062204298133)
      ·
        refine ⟨857797003983706040826475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18299669418319062204298133 857797003983706040826475)
        ·
          refine ⟨1286695505975559061239713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857797003983706040826475 1286695505975559061239713)
          ·
            refine ⟨965021629481669295929785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1286695505975559061239713 965021629481669295929785)
            ·
              refine ⟨723766222111251971947339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965021629481669295929785 723766222111251971947339)
              ·
                refine ⟨1085649333166877957921009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723766222111251971947339 1085649333166877957921009)
                ·
                  refine ⟨814236999875158468440757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1085649333166877957921009 814236999875158468440757)
                  ·
                    refine ⟨76334718738296106416321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 814236999875158468440757 76334718738296106416321)
                    ·
                      rfl

theorem cell23_445984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 5].length) (baseStart_445984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_445984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_445984 prefixEnd_445984 := by exact prefixLift 445984
  have htrace : WordTrace (prefixWord ++ tailWord_445984) baseStart_445984 baseEnd_445984 := by
    simpa [prefixWord, tailWord_445984, baseEnd_445984] using wordTrace_append hprefix tailTrace_445984
  have hstable : (prefixWord ++ tailWord_445984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445984).length < 2 ^ (prefixWord ++ tailWord_445984).sum := by decide
  have hdescent : baseEnd_445984 < baseStart_445984 := by decide
  rcases family_descends (prefixWord ++ tailWord_445984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446000 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_446000 : Nat := 118140960795 + 446000 * 2 ^ 59
def prefixEnd_446000 : Nat := 4983230072969 + 3 ^ 40 * 446000 * 2
def baseEnd_446000 : Nat := 229012371905360256648889

theorem tailTrace_446000 : CollatzResearch.WordTrace tailWord_446000 prefixEnd_446000 229012371905360256648889 := by
  unfold tailWord_446000
  simp only [CollatzResearch.WordTrace]
  refine ⟨8133478192112822790423727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10844637589483763720564969 8133478192112822790423727)
  ·
    refine ⟨12200217288169234185635591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8133478192112822790423727 12200217288169234185635591)
    ·
      refine ⟨18300325932253851278453387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12200217288169234185635591 18300325932253851278453387)
      ·
        refine ⟨27450488898380776917680081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18300325932253851278453387 27450488898380776917680081)
        ·
          refine ⟨20587866673785582688260061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27450488898380776917680081 20587866673785582688260061)
          ·
            refine ⟨7720450002669593508097523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20587866673785582688260061 7720450002669593508097523)
            ·
              refine ⟨11580675004004390262146285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7720450002669593508097523 11580675004004390262146285)
              ·
                refine ⟨4342753126501646348304857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11580675004004390262146285 4342753126501646348304857)
                ·
                  refine ⟨3257064844876234761228643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4342753126501646348304857 3257064844876234761228643)
                  ·
                    refine ⟨4885597267314352141842965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3257064844876234761228643 4885597267314352141842965)
                    ·
                      refine ⟨229012371905360256648889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4885597267314352141842965 229012371905360256648889)
                      ·
                        rfl

theorem cell23_446000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_446000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446000 prefixEnd_446000 := by exact prefixLift 446000
  have htrace : WordTrace (prefixWord ++ tailWord_446000) baseStart_446000 baseEnd_446000 := by
    simpa [prefixWord, tailWord_446000, baseEnd_446000] using wordTrace_append hprefix tailTrace_446000
  have hstable : (prefixWord ++ tailWord_446000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446000).length < 2 ^ (prefixWord ++ tailWord_446000).sum := by decide
  have hdescent : baseEnd_446000 < baseStart_446000 := by decide
  rcases family_descends (prefixWord ++ tailWord_446000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446038 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_446038 : Nat := 118140960795 + 446038 * 2 ^ 59
def prefixEnd_446038 : Nat := 4983230072969 + 3 ^ 40 * 446038 * 2
def baseEnd_446038 : Nat := 229031884170231107973715

theorem tailTrace_446038 : CollatzResearch.WordTrace tailWord_446038 prefixEnd_446038 229031884170231107973715 := by
  unfold tailWord_446038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016771397380498629420673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10845561572058652047153845 1016771397380498629420673)
  ·
    refine ⟨762578548035373972065505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1016771397380498629420673 762578548035373972065505)
    ·
      refine ⟨571933911026530479049129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 762578548035373972065505 571933911026530479049129)
      ·
        refine ⟨428950433269897859286847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571933911026530479049129 428950433269897859286847)
        ·
          refine ⟨643425649904846788930271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428950433269897859286847 643425649904846788930271)
          ·
            refine ⟨965138474857270183395407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643425649904846788930271 965138474857270183395407)
            ·
              refine ⟨1447707712285905275093111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965138474857270183395407 1447707712285905275093111)
              ·
                refine ⟨2171561568428857912639667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1447707712285905275093111 2171561568428857912639667)
                ·
                  refine ⟨3257342352643286868959501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171561568428857912639667 3257342352643286868959501)
                  ·
                    refine ⟨1221503382241232575859813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3257342352643286868959501 1221503382241232575859813)
                    ·
                      refine ⟨229031884170231107973715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1221503382241232575859813 229031884170231107973715)
                      ·
                        rfl

theorem cell23_446038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_446038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446038 prefixEnd_446038 := by exact prefixLift 446038
  have htrace : WordTrace (prefixWord ++ tailWord_446038) baseStart_446038 baseEnd_446038 := by
    simpa [prefixWord, tailWord_446038, baseEnd_446038] using wordTrace_append hprefix tailTrace_446038
  have hstable : (prefixWord ++ tailWord_446038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446038).length < 2 ^ (prefixWord ++ tailWord_446038).sum := by decide
  have hdescent : baseEnd_446038 < baseStart_446038 := by decide
  rcases family_descends (prefixWord ++ tailWord_446038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446061 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 6]
def baseStart_446061 : Nat := 118140960795 + 446061 * 2 ^ 59
def prefixEnd_446061 : Nat := 4983230072969 + 3 ^ 40 * 446061 * 2
def baseEnd_446061 : Nat := 25449299358364946442901

theorem tailTrace_446061 : CollatzResearch.WordTrace tailWord_446061 prefixEnd_446061 25449299358364946442901 := by
  unfold tailWord_446061
  simp only [CollatzResearch.WordTrace]
  refine ⟨16269181237004652998818037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10846120824669768665878691 16269181237004652998818037)
  ·
    refine ⟨1525235740969186218639191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16269181237004652998818037 1525235740969186218639191)
    ·
      refine ⟨2287853611453779327958787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1525235740969186218639191 2287853611453779327958787)
      ·
        refine ⟨3431780417180668991938181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2287853611453779327958787 3431780417180668991938181)
        ·
          refine ⟨643458828221375435988409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3431780417180668991938181 643458828221375435988409)
          ·
            refine ⟨482594121166031576991307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643458828221375435988409 482594121166031576991307)
            ·
              refine ⟨723891181749047365486961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482594121166031576991307 723891181749047365486961)
              ·
                refine ⟨542918386311785524115221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723891181749047365486961 542918386311785524115221)
                ·
                  refine ⟨25449299358364946442901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 542918386311785524115221 25449299358364946442901)
                  ·
                    rfl

theorem cell23_446061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_446061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446061 prefixEnd_446061 := by exact prefixLift 446061
  have htrace : WordTrace (prefixWord ++ tailWord_446061) baseStart_446061 baseEnd_446061 := by
    simpa [prefixWord, tailWord_446061, baseEnd_446061] using wordTrace_append hprefix tailTrace_446061
  have hstable : (prefixWord ++ tailWord_446061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446061).length < 2 ^ (prefixWord ++ tailWord_446061).sum := by decide
  have hdescent : baseEnd_446061 < baseStart_446061 := by decide
  rcases family_descends (prefixWord ++ tailWord_446061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446104 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 4, 4]
def baseStart_446104 : Nat := 118140960795 + 446104 * 2 ^ 59
def prefixEnd_446104 : Nat := 4983230072969 + 3 ^ 40 * 446104 * 2
def baseEnd_446104 : Nat := 76355257964475949916137

theorem tailTrace_446104 : CollatzResearch.WordTrace tailWord_446104 prefixEnd_446104 76355257964475949916137 := by
  unfold tailWord_446104
  simp only [CollatzResearch.WordTrace]
  refine ⟨8135374787924435671316683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10847166383899247561755577 8135374787924435671316683)
  ·
    refine ⟨12203062181886653506975025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8135374787924435671316683 12203062181886653506975025)
    ·
      refine ⟨9152296636414990130231269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12203062181886653506975025 9152296636414990130231269)
      ·
        refine ⟨1716055619327810649418363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9152296636414990130231269 1716055619327810649418363)
        ·
          refine ⟨2574083428991715974127545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716055619327810649418363 2574083428991715974127545)
          ·
            refine ⟨1930562571743786980595659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2574083428991715974127545 1930562571743786980595659)
            ·
              refine ⟨2895843857615680470893489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930562571743786980595659 2895843857615680470893489)
              ·
                refine ⟨2171882893211760353170117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2895843857615680470893489 2171882893211760353170117)
                ·
                  refine ⟨407228042477205066219397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2171882893211760353170117 407228042477205066219397)
                  ·
                    refine ⟨76355257964475949916137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 407228042477205066219397 76355257964475949916137)
                    ·
                      rfl

theorem cell23_446104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_446104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446104 prefixEnd_446104 := by exact prefixLift 446104
  have htrace : WordTrace (prefixWord ++ tailWord_446104) baseStart_446104 baseEnd_446104 := by
    simpa [prefixWord, tailWord_446104, baseEnd_446104] using wordTrace_append hprefix tailTrace_446104
  have hstable : (prefixWord ++ tailWord_446104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446104).length < 2 ^ (prefixWord ++ tailWord_446104).sum := by decide
  have hdescent : baseEnd_446104 < baseStart_446104 := by decide
  rcases family_descends (prefixWord ++ tailWord_446104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446128 : List Nat := [2, 1, 1, 1, 2, 1, 4, 6, 1, 2, 2]
def baseStart_446128 : Nat := 118140960795 + 446128 * 2 ^ 59
def prefixEnd_446128 : Nat := 4983230072969 + 3 ^ 40 * 446128 * 2
def baseEnd_446128 : Nat := 229078097429135755848301

theorem tailTrace_446128 : CollatzResearch.WordTrace tailWord_446128 prefixEnd_446128 229078097429135755848301 := by
  unfold tailWord_446128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8135812463880961720753519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10847749951841282294338025 8135812463880961720753519)
  ·
    refine ⟨12203718695821442581130279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8135812463880961720753519 12203718695821442581130279)
    ·
      refine ⟨18305578043732163871695419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12203718695821442581130279 18305578043732163871695419)
      ·
        refine ⟨27458367065598245807543129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18305578043732163871695419 27458367065598245807543129)
        ·
          refine ⟨20593775299198684355657347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27458367065598245807543129 20593775299198684355657347)
          ·
            refine ⟨30890662948798026533486021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20593775299198684355657347 30890662948798026533486021)
            ·
              refine ⟨5791999302899629975028629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30890662948798026533486021 5791999302899629975028629)
              ·
                refine ⟨271499967323420155079467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5791999302899629975028629 271499967323420155079467)
                ·
                  refine ⟨407249950985130232619201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271499967323420155079467 407249950985130232619201)
                  ·
                    refine ⟨305437463238847674464401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 407249950985130232619201 305437463238847674464401)
                    ·
                      refine ⟨229078097429135755848301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305437463238847674464401 229078097429135755848301)
                      ·
                        rfl

theorem cell23_446128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 1, 2, 2].length) (baseStart_446128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446128 prefixEnd_446128 := by exact prefixLift 446128
  have htrace : WordTrace (prefixWord ++ tailWord_446128) baseStart_446128 baseEnd_446128 := by
    simpa [prefixWord, tailWord_446128, baseEnd_446128] using wordTrace_append hprefix tailTrace_446128
  have hstable : (prefixWord ++ tailWord_446128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446128).length < 2 ^ (prefixWord ++ tailWord_446128).sum := by decide
  have hdescent : baseEnd_446128 < baseStart_446128 := by decide
  rcases family_descends (prefixWord ++ tailWord_446128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446138 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 2, 4]
def baseStart_446138 : Nat := 118140960795 + 446138 * 2 ^ 59
def prefixEnd_446138 : Nat := 4983230072969 + 3 ^ 40 * 446138 * 2
def baseEnd_446138 : Nat := 76361077411893572241085

theorem tailTrace_446138 : CollatzResearch.WordTrace tailWord_446138 prefixEnd_446138 76361077411893572241085 := by
  unfold tailWord_446138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4067997414431423787342767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10847993105150463432914045 4067997414431423787342767)
  ·
    refine ⟨6101996121647135681014151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4067997414431423787342767 6101996121647135681014151)
    ·
      refine ⟨9152994182470703521521227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6101996121647135681014151 9152994182470703521521227)
      ·
        refine ⟨13729491273706055282281841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9152994182470703521521227 13729491273706055282281841)
        ·
          refine ⟨10297118455279541461711381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13729491273706055282281841 10297118455279541461711381)
          ·
            refine ⟨482677427591228506017721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10297118455279541461711381 482677427591228506017721)
            ·
              refine ⟨362008070693421379513291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482677427591228506017721 362008070693421379513291)
              ·
                refine ⟨543012106040132069269937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362008070693421379513291 543012106040132069269937)
                ·
                  refine ⟨407259079530099051952453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543012106040132069269937 407259079530099051952453)
                  ·
                    refine ⟨76361077411893572241085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 407259079530099051952453 76361077411893572241085)
                    ·
                      rfl

theorem cell23_446138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_446138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446138 prefixEnd_446138 := by exact prefixLift 446138
  have htrace : WordTrace (prefixWord ++ tailWord_446138) baseStart_446138 baseEnd_446138 := by
    simpa [prefixWord, tailWord_446138, baseEnd_446138] using wordTrace_append hprefix tailTrace_446138
  have hstable : (prefixWord ++ tailWord_446138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446138).length < 2 ^ (prefixWord ++ tailWord_446138).sum := by decide
  have hdescent : baseEnd_446138 < baseStart_446138 := by decide
  rcases family_descends (prefixWord ++ tailWord_446138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446144 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 3]
def baseStart_446144 : Nat := 118140960795 + 446144 * 2 ^ 59
def prefixEnd_446144 : Nat := 4983230072969 + 3 ^ 40 * 446144 * 2
def baseEnd_446144 : Nat := 229086313119607693248227

theorem tailTrace_446144 : CollatzResearch.WordTrace tailWord_446144 prefixEnd_446144 229086313119607693248227 := by
  unfold tailWord_446144
  simp only [CollatzResearch.WordTrace]
  refine ⟨8136104247851979087044743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10848138997135972116059657 8136104247851979087044743)
  ·
    refine ⟨12204156371777968630567115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8136104247851979087044743 12204156371777968630567115)
    ·
      refine ⟨18306234557666952945850673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12204156371777968630567115 18306234557666952945850673)
      ·
        refine ⟨13729675918250214709388005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18306234557666952945850673 13729675918250214709388005)
        ·
          refine ⟨2574314234671915258010251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13729675918250214709388005 2574314234671915258010251)
          ·
            refine ⟨3861471352007872887015377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574314234671915258010251 3861471352007872887015377)
            ·
              refine ⟨2896103514005904665261533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3861471352007872887015377 2896103514005904665261533)
              ·
                refine ⟨1086038817752214249473075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2896103514005904665261533 1086038817752214249473075)
                ·
                  refine ⟨1629058226628321374209613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086038817752214249473075 1629058226628321374209613)
                  ·
                    refine ⟨610896834985620515328605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1629058226628321374209613 610896834985620515328605)
                    ·
                      refine ⟨229086313119607693248227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 610896834985620515328605 229086313119607693248227)
                      ·
                        rfl

theorem cell23_446144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_446144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446144 prefixEnd_446144 := by exact prefixLift 446144
  have htrace : WordTrace (prefixWord ++ tailWord_446144) baseStart_446144 baseEnd_446144 := by
    simpa [prefixWord, tailWord_446144, baseEnd_446144] using wordTrace_append hprefix tailTrace_446144
  have hstable : (prefixWord ++ tailWord_446144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446144).length < 2 ^ (prefixWord ++ tailWord_446144).sum := by decide
  have hdescent : baseEnd_446144 < baseStart_446144 := by decide
  rcases family_descends (prefixWord ++ tailWord_446144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446179 : List Nat := [1, 1, 1, 7, 2, 2, 2, 2, 1, 2, 2]
def baseStart_446179 : Nat := 118140960795 + 446179 * 2 ^ 59
def prefixEnd_446179 : Nat := 4983230072969 + 3 ^ 40 * 446179 * 2
def baseEnd_446179 : Nat := 229104284942515056310567

theorem tailTrace_446179 : CollatzResearch.WordTrace tailWord_446179 prefixEnd_446179 229104284942515056310567 := by
  unfold tailWord_446179
  simp only [CollatzResearch.WordTrace]
  refine ⟨16273485050577159151613591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10848990033718106101075727 16273485050577159151613591)
  ·
    refine ⟨24410227575865738727420387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16273485050577159151613591 24410227575865738727420387)
    ·
      refine ⟨36615341363798608091130581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24410227575865738727420387 36615341363798608091130581)
      ·
        refine ⟨858172063214029877135873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 36615341363798608091130581 858172063214029877135873)
        ·
          refine ⟨643629047410522407851905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858172063214029877135873 643629047410522407851905)
          ·
            refine ⟨482721785557891805888929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643629047410522407851905 482721785557891805888929)
            ·
              refine ⟨362041339168418854416697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482721785557891805888929 362041339168418854416697)
              ·
                refine ⟨271531004376314140812523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362041339168418854416697 271531004376314140812523)
                ·
                  refine ⟨407296506564471211218785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271531004376314140812523 407296506564471211218785)
                  ·
                    refine ⟨305472379923353408414089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 407296506564471211218785 305472379923353408414089)
                    ·
                      refine ⟨229104284942515056310567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305472379923353408414089 229104284942515056310567)
                      ·
                        rfl

theorem cell23_446179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_446179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446179 prefixEnd_446179 := by exact prefixLift 446179
  have htrace : WordTrace (prefixWord ++ tailWord_446179) baseStart_446179 baseEnd_446179 := by
    simpa [prefixWord, tailWord_446179, baseEnd_446179] using wordTrace_append hprefix tailTrace_446179
  have hstable : (prefixWord ++ tailWord_446179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446179).length < 2 ^ (prefixWord ++ tailWord_446179).sum := by decide
  have hdescent : baseEnd_446179 < baseStart_446179 := by decide
  rcases family_descends (prefixWord ++ tailWord_446179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446184 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_446184 : Nat := 118140960795 + 446184 * 2 ^ 59
def prefixEnd_446184 : Nat := 4983230072969 + 3 ^ 40 * 446184 * 2
def baseEnd_446184 : Nat := 229106852345787536748043

theorem tailTrace_446184 : CollatzResearch.WordTrace tailWord_446184 prefixEnd_446184 229106852345787536748043 := by
  unfold tailWord_446184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8136833707779522502772803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10849111610372696670363737 8136833707779522502772803)
  ·
    refine ⟨12205250561669283754159205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8136833707779522502772803 12205250561669283754159205)
    ·
      refine ⟨2288484480312990703904851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12205250561669283754159205 2288484480312990703904851)
      ·
        refine ⟨3432726720469486055857277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2288484480312990703904851 3432726720469486055857277)
        ·
          refine ⟨1287272520176057270946479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3432726720469486055857277 1287272520176057270946479)
          ·
            refine ⟨1930908780264085906419719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287272520176057270946479 1930908780264085906419719)
            ·
              refine ⟨2896363170396128859629579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930908780264085906419719 2896363170396128859629579)
              ·
                refine ⟨4344544755594193289444369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2896363170396128859629579 4344544755594193289444369)
                ·
                  refine ⟨3258408566695644967083277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344544755594193289444369 3258408566695644967083277)
                  ·
                    refine ⟨1221903212510866862656229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3258408566695644967083277 1221903212510866862656229)
                    ·
                      refine ⟨229106852345787536748043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1221903212510866862656229 229106852345787536748043)
                      ·
                        rfl

theorem cell23_446184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_446184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446184 prefixEnd_446184 := by exact prefixLift 446184
  have htrace : WordTrace (prefixWord ++ tailWord_446184) baseStart_446184 baseEnd_446184 := by
    simpa [prefixWord, tailWord_446184, baseEnd_446184] using wordTrace_append hprefix tailTrace_446184
  have hstable : (prefixWord ++ tailWord_446184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446184).length < 2 ^ (prefixWord ++ tailWord_446184).sum := by decide
  have hdescent : baseEnd_446184 < baseStart_446184 := by decide
  rcases family_descends (prefixWord ++ tailWord_446184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446187 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 5]
def baseStart_446187 : Nat := 118140960795 + 446187 * 2 ^ 59
def prefixEnd_446187 : Nat := 4983230072969 + 3 ^ 40 * 446187 * 2
def baseEnd_446187 : Nat := 229108392787751025010529

theorem tailTrace_446187 : CollatzResearch.WordTrace tailWord_446187 prefixEnd_446187 229108392787751025010529 := by
  unfold tailWord_446187
  simp only [CollatzResearch.WordTrace]
  refine ⟨16273776834548176517904815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10849184556365451011936543 16273776834548176517904815)
  ·
    refine ⟨24410665251822264776857223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16273776834548176517904815 24410665251822264776857223)
    ·
      refine ⟨36615997877733397165285835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24410665251822264776857223 36615997877733397165285835)
      ·
        refine ⟨54923996816600095747928753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36615997877733397165285835 54923996816600095747928753)
        ·
          refine ⟨41192997612450071810946565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54923996816600095747928753 41192997612450071810946565)
          ·
            refine ⟨7723687052334388464552481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41192997612450071810946565 7723687052334388464552481)
            ·
              refine ⟨5792765289250791348414361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7723687052334388464552481 5792765289250791348414361)
              ·
                refine ⟨4344573966938093511310771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792765289250791348414361 4344573966938093511310771)
                ·
                  refine ⟨6516860950407140266966157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344573966938093511310771 6516860950407140266966157)
                  ·
                    refine ⟨2443822856402677600112309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6516860950407140266966157 2443822856402677600112309)
                    ·
                      refine ⟨229108392787751025010529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2443822856402677600112309 229108392787751025010529)
                      ·
                        rfl

theorem cell23_446187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_446187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446187 prefixEnd_446187 := by exact prefixLift 446187
  have htrace : WordTrace (prefixWord ++ tailWord_446187) baseStart_446187 baseEnd_446187 := by
    simpa [prefixWord, tailWord_446187, baseEnd_446187] using wordTrace_append hprefix tailTrace_446187
  have hstable : (prefixWord ++ tailWord_446187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446187).length < 2 ^ (prefixWord ++ tailWord_446187).sum := by decide
  have hdescent : baseEnd_446187 < baseStart_446187 := by decide
  rcases family_descends (prefixWord ++ tailWord_446187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446194 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_446194 : Nat := 118140960795 + 446194 * 2 ^ 59
def prefixEnd_446194 : Nat := 4983230072969 + 3 ^ 40 * 446194 * 2
def baseEnd_446194 : Nat := 76370662384110832540999

theorem tailTrace_446194 : CollatzResearch.WordTrace tailWord_446194 prefixEnd_446194 76370662384110832540999 := by
  unfold tailWord_446194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4068508036380704178352409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10849354763681877808939757 4068508036380704178352409)
  ·
    refine ⟨3051381027285528133764307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4068508036380704178352409 3051381027285528133764307)
    ·
      refine ⟨4577071540928292200646461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3051381027285528133764307 4577071540928292200646461)
      ·
        refine ⟨1716401827848109575242423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4577071540928292200646461 1716401827848109575242423)
        ·
          refine ⟨2574602741772164362863635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716401827848109575242423 2574602741772164362863635)
          ·
            refine ⟨3861904112658246544295453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574602741772164362863635 3861904112658246544295453)
            ·
              refine ⟨1448214042246842454110795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3861904112658246544295453 1448214042246842454110795)
              ·
                refine ⟨2172321063370263681166193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448214042246842454110795 2172321063370263681166193)
                ·
                  refine ⟨1629240797527697760874645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2172321063370263681166193 1629240797527697760874645)
                  ·
                    refine ⟨76370662384110832540999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1629240797527697760874645 76370662384110832540999)
                    ·
                      rfl

theorem cell23_446194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_446194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446194 prefixEnd_446194 := by exact prefixLift 446194
  have htrace : WordTrace (prefixWord ++ tailWord_446194) baseStart_446194 baseEnd_446194 := by
    simpa [prefixWord, tailWord_446194, baseEnd_446194] using wordTrace_append hprefix tailTrace_446194
  have hstable : (prefixWord ++ tailWord_446194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446194).length < 2 ^ (prefixWord ++ tailWord_446194).sum := by decide
  have hdescent : baseEnd_446194 < baseStart_446194 := by decide
  rcases family_descends (prefixWord ++ tailWord_446194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446201 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 8, 2, 2]
def baseStart_446201 : Nat := 118140960795 + 446201 * 2 ^ 59
def prefixEnd_446201 : Nat := 4983230072969 + 3 ^ 40 * 446201 * 2
def baseEnd_446201 : Nat := 229115581516913970235465

theorem tailTrace_446201 : CollatzResearch.WordTrace tailWord_446201 prefixEnd_446201 229115581516913970235465 := by
  unfold tailWord_446201
  simp only [CollatzResearch.WordTrace]
  refine ⟨16274287456497456908914457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10849524970998304605942971 16274287456497456908914457)
  ·
    refine ⟨12205715592373092681685843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16274287456497456908914457 12205715592373092681685843)
    ·
      refine ⟨18308573388559639022528765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12205715592373092681685843 18308573388559639022528765)
      ·
        refine ⟨6865715020709864633448287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18308573388559639022528765 6865715020709864633448287)
        ·
          refine ⟨10298572531064796950172431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6865715020709864633448287 10298572531064796950172431)
          ·
            refine ⟨15447858796597195425258647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10298572531064796950172431 15447858796597195425258647)
            ·
              refine ⟨23171788194895793137887971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15447858796597195425258647 23171788194895793137887971)
              ·
                refine ⟨34757682292343689706831957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23171788194895793137887971 34757682292343689706831957)
                ·
                  refine ⟨407316589363402613751937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34757682292343689706831957 407316589363402613751937)
                  ·
                    refine ⟨305487442022551960313953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 407316589363402613751937 305487442022551960313953)
                    ·
                      refine ⟨229115581516913970235465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305487442022551960313953 229115581516913970235465)
                      ·
                        rfl

theorem cell23_446201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_446201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446201 prefixEnd_446201 := by exact prefixLift 446201
  have htrace : WordTrace (prefixWord ++ tailWord_446201) baseStart_446201 baseEnd_446201 := by
    simpa [prefixWord, tailWord_446201, baseEnd_446201] using wordTrace_append hprefix tailTrace_446201
  have hstable : (prefixWord ++ tailWord_446201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446201).length < 2 ^ (prefixWord ++ tailWord_446201).sum := by decide
  have hdescent : baseEnd_446201 < baseStart_446201 := by decide
  rcases family_descends (prefixWord ++ tailWord_446201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446204 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_446204 : Nat := 118140960795 + 446204 * 2 ^ 59
def prefixEnd_446204 : Nat := 4983230072969 + 3 ^ 40 * 446204 * 2
def baseEnd_446204 : Nat := 229117121958877458497951

theorem tailTrace_446204 : CollatzResearch.WordTrace tailWord_446204 prefixEnd_446204 229117121958877458497951 := by
  unfold tailWord_446204
  simp only [CollatzResearch.WordTrace]
  refine ⟨8137198437743294210636833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10849597916991058947515777 8137198437743294210636833)
  ·
    refine ⟨6102898828307470657977625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8137198437743294210636833 6102898828307470657977625)
    ·
      refine ⟨4577174121230602993483219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6102898828307470657977625 4577174121230602993483219)
      ·
        refine ⟨6865761181845904490224829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4577174121230602993483219 6865761181845904490224829)
        ·
          refine ⟨2574660443192214183834311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6865761181845904490224829 2574660443192214183834311)
          ·
            refine ⟨3861990664788321275751467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574660443192214183834311 3861990664788321275751467)
            ·
              refine ⟨5792985997182481913627201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861990664788321275751467 5792985997182481913627201)
              ·
                refine ⟨4344739497886861435220401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792985997182481913627201 4344739497886861435220401)
                ·
                  refine ⟨3258554623415146076415301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344739497886861435220401 3258554623415146076415301)
                  ·
                    refine ⟨610978991890339889327869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3258554623415146076415301 610978991890339889327869)
                    ·
                      refine ⟨229117121958877458497951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 610978991890339889327869 229117121958877458497951)
                      ·
                        rfl

theorem cell23_446204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_446204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446204 prefixEnd_446204 := by exact prefixLift 446204
  have htrace : WordTrace (prefixWord ++ tailWord_446204) baseStart_446204 baseEnd_446204 := by
    simpa [prefixWord, tailWord_446204, baseEnd_446204] using wordTrace_append hprefix tailTrace_446204
  have hstable : (prefixWord ++ tailWord_446204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446204).length < 2 ^ (prefixWord ++ tailWord_446204).sum := by decide
  have hdescent : baseEnd_446204 < baseStart_446204 := by decide
  rcases family_descends (prefixWord ++ tailWord_446204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446207 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 9]
def baseStart_446207 : Nat := 118140960795 + 446207 * 2 ^ 59
def prefixEnd_446207 : Nat := 4983230072969 + 3 ^ 40 * 446207 * 2
def baseEnd_446207 : Nat := 25457629155648994084493

theorem tailTrace_446207 : CollatzResearch.WordTrace tailWord_446207 prefixEnd_446207 25457629155648994084493 := by
  unfold tailWord_446207
  simp only [CollatzResearch.WordTrace]
  refine ⟨16274506294475719933632875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10849670862983813289088583 16274506294475719933632875)
  ·
    refine ⟨24411759441713579900449313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16274506294475719933632875 24411759441713579900449313)
    ·
      refine ⟨18308819581285184925336985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24411759441713579900449313 18308819581285184925336985)
      ·
        refine ⟨13731614685963888694002739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18308819581285184925336985 13731614685963888694002739)
        ·
          refine ⟨20597422028945833041004109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13731614685963888694002739 20597422028945833041004109)
          ·
            refine ⟨7724033260854687390376541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20597422028945833041004109 7724033260854687390376541)
            ·
              refine ⟨2896512472820507771391203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7724033260854687390376541 2896512472820507771391203)
              ·
                refine ⟨4344768709230761657086805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2896512472820507771391203 4344768709230761657086805)
                ·
                  refine ⟨25457629155648994084493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4344768709230761657086805 25457629155648994084493)
                  ·
                    rfl

theorem cell23_446207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 9].length) (baseStart_446207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446207 prefixEnd_446207 := by exact prefixLift 446207
  have htrace : WordTrace (prefixWord ++ tailWord_446207) baseStart_446207 baseEnd_446207 := by
    simpa [prefixWord, tailWord_446207, baseEnd_446207] using wordTrace_append hprefix tailTrace_446207
  have hstable : (prefixWord ++ tailWord_446207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446207).length < 2 ^ (prefixWord ++ tailWord_446207).sum := by decide
  have hdescent : baseEnd_446207 < baseStart_446207 := by decide
  rcases family_descends (prefixWord ++ tailWord_446207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446217 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_446217 : Nat := 118140960795 + 446217 * 2 ^ 59
def prefixEnd_446217 : Nat := 4983230072969 + 3 ^ 40 * 446217 * 2
def baseEnd_446217 : Nat := 229123797207385907635391

theorem tailTrace_446217 : CollatzResearch.WordTrace tailWord_446217 prefixEnd_446217 229123797207385907635391 := by
  unfold tailWord_446217
  simp only [CollatzResearch.WordTrace]
  refine ⟨16274871024439491641496905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10849914016292994427664603 16274871024439491641496905)
  ·
    refine ⟨12206153268329618731122679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16274871024439491641496905 12206153268329618731122679)
    ·
      refine ⟨18309229902494428096684019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12206153268329618731122679 18309229902494428096684019)
      ·
        refine ⟨27463844853741642145026029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18309229902494428096684019 27463844853741642145026029)
        ·
          refine ⟨10298941820153115804384761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27463844853741642145026029 10298941820153115804384761)
          ·
            refine ⟨7724206365114836853288571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10298941820153115804384761 7724206365114836853288571)
            ·
              refine ⟨11586309547672255279932857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7724206365114836853288571 11586309547672255279932857)
              ·
                refine ⟨8689732160754191459949643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11586309547672255279932857 8689732160754191459949643)
                ·
                  refine ⟨13034598241131287189924465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8689732160754191459949643 13034598241131287189924465)
                  ·
                    refine ⟨9775948680848465392443349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13034598241131287189924465 9775948680848465392443349)
                    ·
                      refine ⟨229123797207385907635391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9775948680848465392443349 229123797207385907635391)
                      ·
                        rfl

theorem cell23_446217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_446217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446217 prefixEnd_446217 := by exact prefixLift 446217
  have htrace : WordTrace (prefixWord ++ tailWord_446217) baseStart_446217 baseEnd_446217 := by
    simpa [prefixWord, tailWord_446217, baseEnd_446217] using wordTrace_append hprefix tailTrace_446217
  have hstable : (prefixWord ++ tailWord_446217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446217).length < 2 ^ (prefixWord ++ tailWord_446217).sum := by decide
  have hdescent : baseEnd_446217 < baseStart_446217 := by decide
  rcases family_descends (prefixWord ++ tailWord_446217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446241 : List Nat := [1, 2, 3, 2, 1, 3, 2, 4, 5]
def baseStart_446241 : Nat := 118140960795 + 446241 * 2 ^ 59
def prefixEnd_446241 : Nat := 4983230072969 + 3 ^ 40 * 446241 * 2
def baseEnd_446241 : Nat := 25459568971454868192809

theorem tailTrace_446241 : CollatzResearch.WordTrace tailWord_446241 prefixEnd_446241 25459568971454868192809 := by
  unfold tailWord_446241
  simp only [CollatzResearch.WordTrace]
  refine ⟨16275746376352543740370577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10850497584235029160247051 16275746376352543740370577)
  ·
    refine ⟨12206809782264407805277933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16275746376352543740370577 12206809782264407805277933)
    ·
      refine ⟨4577553668349152926979225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12206809782264407805277933 4577553668349152926979225)
      ·
        refine ⟨3433165251261864695234419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4577553668349152926979225 3433165251261864695234419)
        ·
          refine ⟨5149747876892797042851629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433165251261864695234419 5149747876892797042851629)
          ·
            refine ⟨1931155453834798891069361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5149747876892797042851629 1931155453834798891069361)
            ·
              refine ⟨1448366590376099168302021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1931155453834798891069361 1448366590376099168302021)
              ·
                refine ⟨271568735695518594056629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1448366590376099168302021 271568735695518594056629)
                ·
                  refine ⟨25459568971454868192809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 271568735695518594056629 25459568971454868192809)
                  ·
                    rfl

theorem cell23_446241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 5].length) (baseStart_446241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446241 prefixEnd_446241 := by exact prefixLift 446241
  have htrace : WordTrace (prefixWord ++ tailWord_446241) baseStart_446241 baseEnd_446241 := by
    simpa [prefixWord, tailWord_446241, baseEnd_446241] using wordTrace_append hprefix tailTrace_446241
  have hstable : (prefixWord ++ tailWord_446241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446241).length < 2 ^ (prefixWord ++ tailWord_446241).sum := by decide
  have hdescent : baseEnd_446241 < baseStart_446241 := by decide
  rcases family_descends (prefixWord ++ tailWord_446241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446311 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_446311 : Nat := 118140960795 + 446311 * 2 ^ 59
def prefixEnd_446311 : Nat := 4983230072969 + 3 ^ 40 * 446311 * 2
def baseEnd_446311 : Nat := 229172064388908539859959

theorem tailTrace_446311 : CollatzResearch.WordTrace tailWord_446311 prefixEnd_446311 229172064388908539859959 := by
  unfold tailWord_446311
  simp only [CollatzResearch.WordTrace]
  refine ⟨16278299486098945695418787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10852199657399297130279191 16278299486098945695418787)
  ·
    refine ⟨24417449229148418543128181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16278299486098945695418787 24417449229148418543128181)
    ·
      refine ⟨2289135865232664238418267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24417449229148418543128181 2289135865232664238418267)
      ·
        refine ⟨3433703797848996357627401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2289135865232664238418267 3433703797848996357627401)
        ·
          refine ⟨2575277848386747268220551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3433703797848996357627401 2575277848386747268220551)
          ·
            refine ⟨3862916772580120902330827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575277848386747268220551 3862916772580120902330827)
            ·
              refine ⟨5794375158870181353496241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862916772580120902330827 5794375158870181353496241)
              ·
                refine ⟨4345781369152636015122181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5794375158870181353496241 4345781369152636015122181)
                ·
                  refine ⟨814834006716119252835409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4345781369152636015122181 814834006716119252835409)
                  ·
                    refine ⟨611125505037089439626557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 814834006716119252835409 611125505037089439626557)
                    ·
                      refine ⟨229172064388908539859959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 611125505037089439626557 229172064388908539859959)
                      ·
                        rfl

theorem cell23_446311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_446311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446311 prefixEnd_446311 := by exact prefixLift 446311
  have htrace : WordTrace (prefixWord ++ tailWord_446311) baseStart_446311 baseEnd_446311 := by
    simpa [prefixWord, tailWord_446311, baseEnd_446311] using wordTrace_append hprefix tailTrace_446311
  have hstable : (prefixWord ++ tailWord_446311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446311).length < 2 ^ (prefixWord ++ tailWord_446311).sum := by decide
  have hdescent : baseEnd_446311 < baseStart_446311 := by decide
  rcases family_descends (prefixWord ++ tailWord_446311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446375 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_446375 : Nat := 118140960795 + 446375 * 2 ^ 59
def prefixEnd_446375 : Nat := 4983230072969 + 3 ^ 40 * 446375 * 2
def baseEnd_446375 : Nat := 229204927150796289459665

theorem tailTrace_446375 : CollatzResearch.WordTrace tailWord_446375 prefixEnd_446375 229204927150796289459665 := by
  unfold tailWord_446375
  simp only [CollatzResearch.WordTrace]
  refine ⟨16280633757867084625748579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10853755838578056417165719 16280633757867084625748579)
  ·
    refine ⟨24420950636800626938622869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16280633757867084625748579 24420950636800626938622869)
    ·
      refine ⟨1144732061100029387747947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24420950636800626938622869 1144732061100029387747947)
      ·
        refine ⟨1717098091650044081621921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144732061100029387747947 1717098091650044081621921)
        ·
          refine ⟨1287823568737533061216441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1717098091650044081621921 1287823568737533061216441)
          ·
            refine ⟨965867676553149795912331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287823568737533061216441 965867676553149795912331)
            ·
              refine ⟨1448801514829724693868497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965867676553149795912331 1448801514829724693868497)
              ·
                refine ⟨1086601136122293520401373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448801514829724693868497 1086601136122293520401373)
                ·
                  refine ⟨407475426045860070150515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086601136122293520401373 407475426045860070150515)
                  ·
                    refine ⟨611213139068790105225773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 407475426045860070150515 611213139068790105225773)
                    ·
                      refine ⟨229204927150796289459665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 611213139068790105225773 229204927150796289459665)
                      ·
                        rfl

theorem cell23_446375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_446375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446375 prefixEnd_446375 := by exact prefixLift 446375
  have htrace : WordTrace (prefixWord ++ tailWord_446375) baseStart_446375 baseEnd_446375 := by
    simpa [prefixWord, tailWord_446375, baseEnd_446375] using wordTrace_append hprefix tailTrace_446375
  have hstable : (prefixWord ++ tailWord_446375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446375).length < 2 ^ (prefixWord ++ tailWord_446375).sum := by decide
  have hdescent : baseEnd_446375 < baseStart_446375 := by decide
  rcases family_descends (prefixWord ++ tailWord_446375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446385 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 2, 3, 2]
def baseStart_446385 : Nat := 118140960795 + 446385 * 2 ^ 59
def prefixEnd_446385 : Nat := 4983230072969 + 3 ^ 40 * 446385 * 2
def baseEnd_446385 : Nat := 229210061957341250334619

theorem tailTrace_446385 : CollatzResearch.WordTrace tailWord_446385 prefixEnd_446385 229210061957341250334619 := by
  unfold tailWord_446385
  simp only [CollatzResearch.WordTrace]
  refine ⟨16280998487830856333612609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10853998991887237555741739 16280998487830856333612609)
  ·
    refine ⟨12210748865873142250209457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16280998487830856333612609 12210748865873142250209457)
    ·
      refine ⟨9158061649404856687657093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12210748865873142250209457 9158061649404856687657093)
      ·
        refine ⟨1717136559263410628935705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9158061649404856687657093 1717136559263410628935705)
        ·
          refine ⟨1287852419447557971701779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1717136559263410628935705 1287852419447557971701779)
          ·
            refine ⟨1931778629171336957552669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287852419447557971701779 1931778629171336957552669)
            ·
              refine ⟨724416985939251359082251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1931778629171336957552669 724416985939251359082251)
              ·
                refine ⟨1086625478908877038623377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724416985939251359082251 1086625478908877038623377)
                ·
                  refine ⟨814969109181657778967533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1086625478908877038623377 814969109181657778967533)
                  ·
                    refine ⟨305613415943121667112825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814969109181657778967533 305613415943121667112825)
                    ·
                      refine ⟨229210061957341250334619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305613415943121667112825 229210061957341250334619)
                      ·
                        rfl

theorem cell23_446385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_446385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446385 prefixEnd_446385 := by exact prefixLift 446385
  have htrace : WordTrace (prefixWord ++ tailWord_446385) baseStart_446385 baseEnd_446385 := by
    simpa [prefixWord, tailWord_446385, baseEnd_446385] using wordTrace_append hprefix tailTrace_446385
  have hstable : (prefixWord ++ tailWord_446385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446385).length < 2 ^ (prefixWord ++ tailWord_446385).sum := by decide
  have hdescent : baseEnd_446385 < baseStart_446385 := by decide
  rcases family_descends (prefixWord ++ tailWord_446385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446391 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 4, 4]
def baseStart_446391 : Nat := 118140960795 + 446391 * 2 ^ 59
def prefixEnd_446391 : Nat := 4983230072969 + 3 ^ 40 * 446391 * 2
def baseEnd_446391 : Nat := 76404380947089408953197

theorem tailTrace_446391 : CollatzResearch.WordTrace tailWord_446391 prefixEnd_446391 76404380947089408953197 := by
  unfold tailWord_446391
  simp only [CollatzResearch.WordTrace]
  refine ⟨16281217325809119358331027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10854144883872746238887351 16281217325809119358331027)
  ·
    refine ⟨24421825988713679037496541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16281217325809119358331027 24421825988713679037496541)
    ·
      refine ⟨9158184745767629639061203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24421825988713679037496541 9158184745767629639061203)
      ·
        refine ⟨13737277118651444458591805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9158184745767629639061203 13737277118651444458591805)
        ·
          refine ⟨5151478919494291671971927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13737277118651444458591805 5151478919494291671971927)
          ·
            refine ⟨7727218379241437507957891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151478919494291671971927 7727218379241437507957891)
            ·
              refine ⟨11590827568862156261936837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727218379241437507957891 11590827568862156261936837)
              ·
                refine ⟨2173280169161654299113157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11590827568862156261936837 2173280169161654299113157)
                ·
                  refine ⟨407490031717810181083717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2173280169161654299113157 407490031717810181083717)
                  ·
                    refine ⟨76404380947089408953197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 407490031717810181083717 76404380947089408953197)
                    ·
                      rfl

theorem cell23_446391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_446391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446391 prefixEnd_446391 := by exact prefixLift 446391
  have htrace : WordTrace (prefixWord ++ tailWord_446391) baseStart_446391 baseEnd_446391 := by
    simpa [prefixWord, tailWord_446391, baseEnd_446391] using wordTrace_append hprefix tailTrace_446391
  have hstable : (prefixWord ++ tailWord_446391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446391).length < 2 ^ (prefixWord ++ tailWord_446391).sum := by decide
  have hdescent : baseEnd_446391 < baseStart_446391 := by decide
  rcases family_descends (prefixWord ++ tailWord_446391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446408 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 4, 4]
def baseStart_446408 : Nat := 118140960795 + 446408 * 2 ^ 59
def prefixEnd_446408 : Nat := 4983230072969 + 3 ^ 40 * 446408 * 2
def baseEnd_446408 : Nat := 76407290670798220115671

theorem tailTrace_446408 : CollatzResearch.WordTrace tailWord_446408 prefixEnd_446408 76407290670798220115671 := by
  unfold tailWord_446408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140918683373765630849939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10854558244498354174466585 8140918683373765630849939)
  ·
    refine ⟨12211378025060648446274909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8140918683373765630849939 12211378025060648446274909)
    ·
      refine ⟨4579266759397743167353091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12211378025060648446274909 4579266759397743167353091)
      ·
        refine ⟨6868900139096614751029637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4579266759397743167353091 6868900139096614751029637)
        ·
          refine ⟨1287918776080615265818057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6868900139096614751029637 1287918776080615265818057)
          ·
            refine ⟨965939082060461449363543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287918776080615265818057 965939082060461449363543)
            ·
              refine ⟨1448908623090692174045315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965939082060461449363543 1448908623090692174045315)
              ·
                refine ⟨2173362934636038261067973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448908623090692174045315 2173362934636038261067973)
                ·
                  refine ⟨407505550244257173950245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2173362934636038261067973 407505550244257173950245)
                  ·
                    refine ⟨76407290670798220115671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 407505550244257173950245 76407290670798220115671)
                    ·
                      rfl

theorem cell23_446408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_446408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446408 prefixEnd_446408 := by exact prefixLift 446408
  have htrace : WordTrace (prefixWord ++ tailWord_446408) baseStart_446408 baseEnd_446408 := by
    simpa [prefixWord, tailWord_446408, baseEnd_446408] using wordTrace_append hprefix tailTrace_446408
  have hstable : (prefixWord ++ tailWord_446408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446408).length < 2 ^ (prefixWord ++ tailWord_446408).sum := by decide
  have hdescent : baseEnd_446408 < baseStart_446408 := by decide
  rcases family_descends (prefixWord ++ tailWord_446408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446415 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 3, 2, 2]
def baseStart_446415 : Nat := 118140960795 + 446415 * 2 ^ 59
def prefixEnd_446415 : Nat := 4983230072969 + 3 ^ 40 * 446415 * 2
def baseEnd_446415 : Nat := 229225466376976132959481

theorem tailTrace_446415 : CollatzResearch.WordTrace tailWord_446415 prefixEnd_446415 229225466376976132959481 := by
  unfold tailWord_446415
  simp only [CollatzResearch.WordTrace]
  refine ⟨16282092677722171457204699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10854728451814780971469799 16282092677722171457204699)
  ·
    refine ⟨24423139016583257185807049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16282092677722171457204699 24423139016583257185807049)
    ·
      refine ⟨18317354262437442889355287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24423139016583257185807049 18317354262437442889355287)
      ·
        refine ⟨27476031393656164334032931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18317354262437442889355287 27476031393656164334032931)
        ·
          refine ⟨41214047090484246501049397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27476031393656164334032931 41214047090484246501049397)
          ·
            refine ⟨3863816914732898109473381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41214047090484246501049397 3863816914732898109473381)
            ·
              refine ⟨724465671512418395526259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3863816914732898109473381 724465671512418395526259)
              ·
                refine ⟨1086698507268627593289389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724465671512418395526259 1086698507268627593289389)
                ·
                  refine ⟨407511940225735347483521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086698507268627593289389 407511940225735347483521)
                  ·
                    refine ⟨305633955169301510612641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 407511940225735347483521 305633955169301510612641)
                    ·
                      refine ⟨229225466376976132959481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305633955169301510612641 229225466376976132959481)
                      ·
                        rfl

theorem cell23_446415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 2, 2].length) (baseStart_446415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446415 prefixEnd_446415 := by exact prefixLift 446415
  have htrace : WordTrace (prefixWord ++ tailWord_446415) baseStart_446415 baseEnd_446415 := by
    simpa [prefixWord, tailWord_446415, baseEnd_446415] using wordTrace_append hprefix tailTrace_446415
  have hstable : (prefixWord ++ tailWord_446415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446415).length < 2 ^ (prefixWord ++ tailWord_446415).sum := by decide
  have hdescent : baseEnd_446415 < baseStart_446415 := by decide
  rcases family_descends (prefixWord ++ tailWord_446415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446425 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 1, 6]
def baseStart_446425 : Nat := 118140960795 + 446425 * 2 ^ 59
def prefixEnd_446425 : Nat := 4983230072969 + 3 ^ 40 * 446425 * 2
def baseEnd_446425 : Nat := 76410200394507031278145

theorem tailTrace_446425 : CollatzResearch.WordTrace tailWord_446425 prefixEnd_446425 76410200394507031278145 := by
  unfold tailWord_446425
  simp only [CollatzResearch.WordTrace]
  refine ⟨16282457407685943165068729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10854971605123962110045819 16282457407685943165068729)
  ·
    refine ⟨12211843055764457373801547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16282457407685943165068729 12211843055764457373801547)
    ·
      refine ⟨18317764583646686060702321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12211843055764457373801547 18317764583646686060702321)
      ·
        refine ⟨13738323437735014545526741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18317764583646686060702321 13738323437735014545526741)
        ·
          refine ⟨321991955571914403410783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 13738323437735014545526741 321991955571914403410783)
          ·
            refine ⟨482987933357871605116175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321991955571914403410783 482987933357871605116175)
            ·
              refine ⟨724481900036807407674263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482987933357871605116175 724481900036807407674263)
              ·
                refine ⟨1086722850055211111511395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724481900036807407674263 1086722850055211111511395)
                ·
                  refine ⟨1630084275082816667267093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086722850055211111511395 1630084275082816667267093)
                  ·
                    refine ⟨76410200394507031278145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1630084275082816667267093 76410200394507031278145)
                    ·
                      rfl

theorem cell23_446425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 6].length) (baseStart_446425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446425 prefixEnd_446425 := by exact prefixLift 446425
  have htrace : WordTrace (prefixWord ++ tailWord_446425) baseStart_446425 baseEnd_446425 := by
    simpa [prefixWord, tailWord_446425, baseEnd_446425] using wordTrace_append hprefix tailTrace_446425
  have hstable : (prefixWord ++ tailWord_446425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446425).length < 2 ^ (prefixWord ++ tailWord_446425).sum := by decide
  have hdescent : baseEnd_446425 < baseStart_446425 := by decide
  rcases family_descends (prefixWord ++ tailWord_446425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446435 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 1, 2, 3]
def baseStart_446435 : Nat := 118140960795 + 446435 * 2 ^ 59
def prefixEnd_446435 : Nat := 4983230072969 + 3 ^ 40 * 446435 * 2
def baseEnd_446435 : Nat := 229235735990066054709389

theorem tailTrace_446435 : CollatzResearch.WordTrace tailWord_446435 prefixEnd_446435 229235735990066054709389 := by
  unfold tailWord_446435
  simp only [CollatzResearch.WordTrace]
  refine ⟨16282822137649714872932759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10855214758433143248621839 16282822137649714872932759)
  ·
    refine ⟨24424233206474572309399139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16282822137649714872932759 24424233206474572309399139)
    ·
      refine ⟨36636349809711858464098709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24424233206474572309399139 36636349809711858464098709)
      ·
        refine ⟨1717328897330243365504627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36636349809711858464098709 1717328897330243365504627)
        ·
          refine ⟨2575993345995365048256941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717328897330243365504627 2575993345995365048256941)
          ·
            refine ⟨965997504748261893096353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2575993345995365048256941 965997504748261893096353)
            ·
              refine ⟨724498128561196419822265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965997504748261893096353 724498128561196419822265)
              ·
                refine ⟨543373596420897314866699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724498128561196419822265 543373596420897314866699)
                ·
                  refine ⟨815060394631345972300049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543373596420897314866699 815060394631345972300049)
                  ·
                    refine ⟨611295295973509479225037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 815060394631345972300049 611295295973509479225037)
                    ·
                      refine ⟨229235735990066054709389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 611295295973509479225037 229235735990066054709389)
                      ·
                        rfl

theorem cell23_446435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_446435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446435 prefixEnd_446435 := by exact prefixLift 446435
  have htrace : WordTrace (prefixWord ++ tailWord_446435) baseStart_446435 baseEnd_446435 := by
    simpa [prefixWord, tailWord_446435, baseEnd_446435] using wordTrace_append hprefix tailTrace_446435
  have hstable : (prefixWord ++ tailWord_446435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446435).length < 2 ^ (prefixWord ++ tailWord_446435).sum := by decide
  have hdescent : baseEnd_446435 < baseStart_446435 := by decide
  rcases family_descends (prefixWord ++ tailWord_446435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446448 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 4, 1, 3]
def baseStart_446448 : Nat := 118140960795 + 446448 * 2 ^ 59
def prefixEnd_446448 : Nat := 4983230072969 + 3 ^ 40 * 446448 * 2
def baseEnd_446448 : Nat := 229242411238574503846829

theorem tailTrace_446448 : CollatzResearch.WordTrace tailWord_446448 prefixEnd_446448 229242411238574503846829 := by
  unfold tailWord_446448
  simp only [CollatzResearch.WordTrace]
  refine ⟨8141648143301309046577999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10855530857735078728770665 8141648143301309046577999)
  ·
    refine ⟨12212472214951963569866999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8141648143301309046577999 12212472214951963569866999)
    ·
      refine ⟨18318708322427945354800499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12212472214951963569866999 18318708322427945354800499)
      ·
        refine ⟨27478062483641918032200749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18318708322427945354800499 27478062483641918032200749)
        ·
          refine ⟨10304273431365719262075281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27478062483641918032200749 10304273431365719262075281)
          ·
            refine ⟨7728205073524289446556461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10304273431365719262075281 7728205073524289446556461)
            ·
              refine ⟨2898076902571608542458673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7728205073524289446556461 2898076902571608542458673)
              ·
                refine ⟨2173557676928706406844005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2898076902571608542458673 2173557676928706406844005)
                ·
                  refine ⟨407542064424132451283251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2173557676928706406844005 407542064424132451283251)
                  ·
                    refine ⟨611313096636198676924877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 407542064424132451283251 611313096636198676924877)
                    ·
                      refine ⟨229242411238574503846829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 611313096636198676924877 229242411238574503846829)
                      ·
                        rfl

theorem cell23_446448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4, 1, 3].length) (baseStart_446448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446448 prefixEnd_446448 := by exact prefixLift 446448
  have htrace : WordTrace (prefixWord ++ tailWord_446448) baseStart_446448 baseEnd_446448 := by
    simpa [prefixWord, tailWord_446448, baseEnd_446448] using wordTrace_append hprefix tailTrace_446448
  have hstable : (prefixWord ++ tailWord_446448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446448).length < 2 ^ (prefixWord ++ tailWord_446448).sum := by decide
  have hdescent : baseEnd_446448 < baseStart_446448 := by decide
  rcases family_descends (prefixWord ++ tailWord_446448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446458 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2]
def baseStart_446458 : Nat := 118140960795 + 446458 * 2 ^ 59
def prefixEnd_446458 : Nat := 4983230072969 + 3 ^ 40 * 446458 * 2
def baseEnd_446458 : Nat := 229247546045119464721783

theorem tailTrace_446458 : CollatzResearch.WordTrace tailWord_446458 prefixEnd_446458 229247546045119464721783 := by
  unfold tailWord_446458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4070915254141597450255007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10855774011044259867346685 4070915254141597450255007)
  ·
    refine ⟨6106372881212396175382511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4070915254141597450255007 6106372881212396175382511)
    ·
      refine ⟨9159559321818594263073767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6106372881212396175382511 9159559321818594263073767)
      ·
        refine ⟨13739338982727891394610651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9159559321818594263073767 13739338982727891394610651)
        ·
          refine ⟨20609008474091837091915977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13739338982727891394610651 20609008474091837091915977)
          ·
            refine ⟨15456756355568877818936983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20609008474091837091915977 15456756355568877818936983)
            ·
              refine ⟨23185134533353316728405475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15456756355568877818936983 23185134533353316728405475)
              ·
                refine ⟨34777701800029975092608213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23185134533353316728405475 34777701800029975092608213)
                ·
                  refine ⟨815102385938202541233005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 34777701800029975092608213 815102385938202541233005)
                  ·
                    refine ⟨305663394726825952962377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 815102385938202541233005 305663394726825952962377)
                    ·
                      refine ⟨229247546045119464721783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305663394726825952962377 229247546045119464721783)
                      ·
                        rfl

theorem cell23_446458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2].length) (baseStart_446458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446458 prefixEnd_446458 := by exact prefixLift 446458
  have htrace : WordTrace (prefixWord ++ tailWord_446458) baseStart_446458 baseEnd_446458 := by
    simpa [prefixWord, tailWord_446458, baseEnd_446458] using wordTrace_append hprefix tailTrace_446458
  have hstable : (prefixWord ++ tailWord_446458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446458).length < 2 ^ (prefixWord ++ tailWord_446458).sum := by decide
  have hdescent : baseEnd_446458 < baseStart_446458 := by decide
  rcases family_descends (prefixWord ++ tailWord_446458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446465 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_446465 : Nat := 118140960795 + 446465 * 2 ^ 59
def prefixEnd_446465 : Nat := 4983230072969 + 3 ^ 40 * 446465 * 2
def baseEnd_446465 : Nat := 229251140409700937334251

theorem tailTrace_446465 : CollatzResearch.WordTrace tailWord_446465 prefixEnd_446465 229251140409700937334251 := by
  unfold tailWord_446465
  simp only [CollatzResearch.WordTrace]
  refine ⟨16283916327541029996524849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10855944218360686664349899 16283916327541029996524849)
  ·
    refine ⟨12212937245655772497393637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16283916327541029996524849 12212937245655772497393637)
    ·
      refine ⟨2289925733560457343261307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12212937245655772497393637 2289925733560457343261307)
      ·
        refine ⟨3434888600340686014891961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2289925733560457343261307 3434888600340686014891961)
        ·
          refine ⟨2576166450255514511168971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3434888600340686014891961 2576166450255514511168971)
          ·
            refine ⟨3864249675383271766753457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576166450255514511168971 3864249675383271766753457)
            ·
              refine ⟨2898187256537453825065093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3864249675383271766753457 2898187256537453825065093)
              ·
                refine ⟨543410110600772592199705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2898187256537453825065093 543410110600772592199705)
                ·
                  refine ⟨407557582950579444149779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543410110600772592199705 407557582950579444149779)
                  ·
                    refine ⟨611336374425869166224669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 407557582950579444149779 611336374425869166224669)
                    ·
                      refine ⟨229251140409700937334251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 611336374425869166224669 229251140409700937334251)
                      ·
                        rfl

theorem cell23_446465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_446465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446465 prefixEnd_446465 := by exact prefixLift 446465
  have htrace : WordTrace (prefixWord ++ tailWord_446465) baseStart_446465 baseEnd_446465 := by
    simpa [prefixWord, tailWord_446465, baseEnd_446465] using wordTrace_append hprefix tailTrace_446465
  have hstable : (prefixWord ++ tailWord_446465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446465).length < 2 ^ (prefixWord ++ tailWord_446465).sum := by decide
  have hdescent : baseEnd_446465 < baseStart_446465 := by decide
  rcases family_descends (prefixWord ++ tailWord_446465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446491 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 3]
def baseStart_446491 : Nat := 118140960795 + 446491 * 2 ^ 59
def prefixEnd_446491 : Nat := 4983230072969 + 3 ^ 40 * 446491 * 2
def baseEnd_446491 : Nat := 229264490906717835609131

theorem tailTrace_446491 : CollatzResearch.WordTrace tailWord_446491 prefixEnd_446491 229264490906717835609131 := by
  unfold tailWord_446491
  simp only [CollatzResearch.WordTrace]
  refine ⟨16284864625446836436971327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10856576416964557624647551 16284864625446836436971327)
  ·
    refine ⟨24427296938170254655456991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16284864625446836436971327 24427296938170254655456991)
    ·
      refine ⟨36640945407255381983185487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24427296938170254655456991 36640945407255381983185487)
      ·
        refine ⟨54961418110883072974778231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36640945407255381983185487 54961418110883072974778231)
        ·
          refine ⟨82442127166324609462167347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54961418110883072974778231 82442127166324609462167347)
          ·
            refine ⟨123663190749486914193251021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82442127166324609462167347 123663190749486914193251021)
            ·
              refine ⟨46373696531057592822469133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123663190749486914193251021 46373696531057592822469133)
              ·
                refine ⟨17390136199146597308425925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46373696531057592822469133 17390136199146597308425925)
                ·
                  refine ⟨3260650537339986995329861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17390136199146597308425925 3260650537339986995329861)
                  ·
                    refine ⟨611371975751247561624349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3260650537339986995329861 611371975751247561624349)
                    ·
                      refine ⟨229264490906717835609131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 611371975751247561624349 229264490906717835609131)
                      ·
                        rfl

theorem cell23_446491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 3].length) (baseStart_446491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446491 prefixEnd_446491 := by exact prefixLift 446491
  have htrace : WordTrace (prefixWord ++ tailWord_446491) baseStart_446491 baseEnd_446491 := by
    simpa [prefixWord, tailWord_446491, baseEnd_446491] using wordTrace_append hprefix tailTrace_446491
  have hstable : (prefixWord ++ tailWord_446491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446491).length < 2 ^ (prefixWord ++ tailWord_446491).sum := by decide
  have hdescent : baseEnd_446491 < baseStart_446491 := by decide
  rcases family_descends (prefixWord ++ tailWord_446491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446492 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_446492 : Nat := 118140960795 + 446492 * 2 ^ 59
def prefixEnd_446492 : Nat := 4983230072969 + 3 ^ 40 * 446492 * 2
def baseEnd_446492 : Nat := 229265004387372331696627

theorem tailTrace_446492 : CollatzResearch.WordTrace tailWord_446492 prefixEnd_446492 229265004387372331696627 := by
  unfold tailWord_446492
  simp only [CollatzResearch.WordTrace]
  refine ⟨8142450549221606803878865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10856600732295475738505153 8142450549221606803878865)
  ·
    refine ⟨6106837911916205102909149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8142450549221606803878865 6106837911916205102909149)
    ·
      refine ⟨2290064216968576913590931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6106837911916205102909149 2290064216968576913590931)
      ·
        refine ⟨3435096325452865370386397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290064216968576913590931 3435096325452865370386397)
        ·
          refine ⟨1288161122044824513894899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3435096325452865370386397 1288161122044824513894899)
          ·
            refine ⟨1932241683067236770842349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288161122044824513894899 1932241683067236770842349)
            ·
              refine ⟨724590631150213789065881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1932241683067236770842349 724590631150213789065881)
              ·
                refine ⟨543442973362660341799411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724590631150213789065881 543442973362660341799411)
                ·
                  refine ⟨815164460043990512699117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543442973362660341799411 815164460043990512699117)
                  ·
                    refine ⟨305686672516496442262169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 815164460043990512699117 305686672516496442262169)
                    ·
                      refine ⟨229265004387372331696627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305686672516496442262169 229265004387372331696627)
                      ·
                        rfl

theorem cell23_446492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_446492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446492 prefixEnd_446492 := by exact prefixLift 446492
  have htrace : WordTrace (prefixWord ++ tailWord_446492) baseStart_446492 baseEnd_446492 := by
    simpa [prefixWord, tailWord_446492, baseEnd_446492] using wordTrace_append hprefix tailTrace_446492
  have hstable : (prefixWord ++ tailWord_446492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446492).length < 2 ^ (prefixWord ++ tailWord_446492).sum := by decide
  have hdescent : baseEnd_446492 < baseStart_446492 := by decide
  rcases family_descends (prefixWord ++ tailWord_446492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446551 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_446551 : Nat := 118140960795 + 446551 * 2 ^ 59
def prefixEnd_446551 : Nat := 4983230072969 + 3 ^ 40 * 446551 * 2
def baseEnd_446551 : Nat := 229295299745987600858855

theorem tailTrace_446551 : CollatzResearch.WordTrace tailWord_446551 prefixEnd_446551 229295299745987600858855 := by
  unfold tailWord_446551
  simp only [CollatzResearch.WordTrace]
  refine ⟨16287053005229466684155507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10858035336819644456103671 16287053005229466684155507)
  ·
    refine ⟨24430579507844200026233261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16287053005229466684155507 24430579507844200026233261)
    ·
      refine ⟨9161467315441575009837473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24430579507844200026233261 9161467315441575009837473)
      ·
        refine ⟨6871100486581181257378105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9161467315441575009837473 6871100486581181257378105)
        ·
          refine ⟨5153325364935885943033579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6871100486581181257378105 5153325364935885943033579)
          ·
            refine ⟨7729988047403828914550369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5153325364935885943033579 7729988047403828914550369)
            ·
              refine ⟨5797491035552871685912777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7729988047403828914550369 5797491035552871685912777)
              ·
                refine ⟨4348118276664653764434583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5797491035552871685912777 4348118276664653764434583)
                ·
                  refine ⟨6522177414996980646651875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348118276664653764434583 6522177414996980646651875)
                  ·
                    refine ⟨9783266122495470969977813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6522177414996980646651875 9783266122495470969977813)
                    ·
                      refine ⟨229295299745987600858855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9783266122495470969977813 229295299745987600858855)
                      ·
                        rfl

theorem cell23_446551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_446551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446551 prefixEnd_446551 := by exact prefixLift 446551
  have htrace : WordTrace (prefixWord ++ tailWord_446551) baseStart_446551 baseEnd_446551 := by
    simpa [prefixWord, tailWord_446551, baseEnd_446551] using wordTrace_append hprefix tailTrace_446551
  have hstable : (prefixWord ++ tailWord_446551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446551).length < 2 ^ (prefixWord ++ tailWord_446551).sum := by decide
  have hdescent : baseEnd_446551 < baseStart_446551 := by decide
  rcases family_descends (prefixWord ++ tailWord_446551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446595 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 2, 4, 2]
def baseStart_446595 : Nat := 118140960795 + 446595 * 2 ^ 59
def prefixEnd_446595 : Nat := 4983230072969 + 3 ^ 40 * 446595 * 2
def baseEnd_446595 : Nat := 229317892894785428708653

theorem tailTrace_446595 : CollatzResearch.WordTrace tailWord_446595 prefixEnd_446595 229317892894785428708653 := by
  unfold tailWord_446595
  simp only [CollatzResearch.WordTrace]
  refine ⟨16288657817070062198757239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10859105211380041465838159 16288657817070062198757239)
  ·
    refine ⟨24432986725605093298135859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16288657817070062198757239 24432986725605093298135859)
    ·
      refine ⟨36649480088407639947203789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24432986725605093298135859 36649480088407639947203789)
      ·
        refine ⟨13743555033152864980201421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36649480088407639947203789 13743555033152864980201421)
        ·
          refine ⟨5153833137432324367575533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13743555033152864980201421 5153833137432324367575533)
          ·
            refine ⟨1932687426537121637840825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5153833137432324367575533 1932687426537121637840825)
            ·
              refine ⟨1449515569902841228380619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1932687426537121637840825 1449515569902841228380619)
              ·
                refine ⟨2174273354854261842570929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449515569902841228380619 2174273354854261842570929)
                ·
                  refine ⟨1630705016140696381928197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2174273354854261842570929 1630705016140696381928197)
                  ·
                    refine ⟨305757190526380571611537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1630705016140696381928197 305757190526380571611537)
                    ·
                      refine ⟨229317892894785428708653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305757190526380571611537 229317892894785428708653)
                      ·
                        rfl

theorem cell23_446595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 4, 2].length) (baseStart_446595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446595 prefixEnd_446595 := by exact prefixLift 446595
  have htrace : WordTrace (prefixWord ++ tailWord_446595) baseStart_446595 baseEnd_446595 := by
    simpa [prefixWord, tailWord_446595, baseEnd_446595] using wordTrace_append hprefix tailTrace_446595
  have hstable : (prefixWord ++ tailWord_446595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446595).length < 2 ^ (prefixWord ++ tailWord_446595).sum := by decide
  have hdescent : baseEnd_446595 < baseStart_446595 := by decide
  rcases family_descends (prefixWord ++ tailWord_446595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446648 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 3, 5]
def baseStart_446648 : Nat := 118140960795 + 446648 * 2 ^ 59
def prefixEnd_446648 : Nat := 4983230072969 + 3 ^ 40 * 446648 * 2
def baseEnd_446648 : Nat := 76448369123157907115303

theorem tailTrace_446648 : CollatzResearch.WordTrace tailWord_446648 prefixEnd_446648 76448369123157907115303 := by
  unfold tailWord_446648
  simp only [CollatzResearch.WordTrace]
  refine ⟨8145295442939026125218299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10860393923918701500291065 8145295442939026125218299)
  ·
    refine ⟨12217943164408539187827449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8145295442939026125218299 12217943164408539187827449)
    ·
      refine ⟨9163457373306404390870587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12217943164408539187827449 9163457373306404390870587)
      ·
        refine ⟨13745186059959606586305881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9163457373306404390870587 13745186059959606586305881)
        ·
          refine ⟨10308889544969704939729411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13745186059959606586305881 10308889544969704939729411)
          ·
            refine ⟨15463334317454557409594117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10308889544969704939729411 15463334317454557409594117)
            ·
              refine ⟨2899375184522729514298897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15463334317454557409594117 2899375184522729514298897)
              ·
                refine ⟨2174531388392047135724173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2899375184522729514298897 2174531388392047135724173)
                ·
                  refine ⟨815449270647017675896565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2174531388392047135724173 815449270647017675896565)
                  ·
                    refine ⟨76448369123157907115303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 815449270647017675896565 76448369123157907115303)
                    ·
                      rfl

theorem cell23_446648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_446648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446648 prefixEnd_446648 := by exact prefixLift 446648
  have htrace : WordTrace (prefixWord ++ tailWord_446648) baseStart_446648 baseEnd_446648 := by
    simpa [prefixWord, tailWord_446648, baseEnd_446648] using wordTrace_append hprefix tailTrace_446648
  have hstable : (prefixWord ++ tailWord_446648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446648).length < 2 ^ (prefixWord ++ tailWord_446648).sum := by decide
  have hdescent : baseEnd_446648 < baseStart_446648 := by decide
  rcases family_descends (prefixWord ++ tailWord_446648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446655 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 6, 3, 2]
def baseStart_446655 : Nat := 118140960795 + 446655 * 2 ^ 59
def prefixEnd_446655 : Nat := 4983230072969 + 3 ^ 40 * 446655 * 2
def baseEnd_446655 : Nat := 229348701734055193958377

theorem tailTrace_446655 : CollatzResearch.WordTrace tailWord_446655 prefixEnd_446655 229348701734055193958377 := by
  unfold tailWord_446655
  simp only [CollatzResearch.WordTrace]
  refine ⟨16290846196852692445941419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10860564131235128297294279 16290846196852692445941419)
  ·
    refine ⟨24436269295279038668912129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16290846196852692445941419 24436269295279038668912129)
    ·
      refine ⟨18327201971459279001684097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24436269295279038668912129 18327201971459279001684097)
      ·
        refine ⟨13745401478594459251263073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18327201971459279001684097 13745401478594459251263073)
        ·
          refine ⟨10309051108945844438447305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13745401478594459251263073 10309051108945844438447305)
          ·
            refine ⟨7731788331709383328835479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10309051108945844438447305 7731788331709383328835479)
            ·
              refine ⟨11597682497564074993253219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7731788331709383328835479 11597682497564074993253219)
              ·
                refine ⟨17396523746346112489879829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11597682497564074993253219 17396523746346112489879829)
                ·
                  refine ⟨815462050609974022963117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17396523746346112489879829 815462050609974022963117)
                  ·
                    refine ⟨305798268978740258611169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 815462050609974022963117 305798268978740258611169)
                    ·
                      refine ⟨229348701734055193958377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305798268978740258611169 229348701734055193958377)
                      ·
                        rfl

theorem cell23_446655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 3, 2].length) (baseStart_446655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446655 prefixEnd_446655 := by exact prefixLift 446655
  have htrace : WordTrace (prefixWord ++ tailWord_446655) baseStart_446655 baseEnd_446655 := by
    simpa [prefixWord, tailWord_446655, baseEnd_446655] using wordTrace_append hprefix tailTrace_446655
  have hstable : (prefixWord ++ tailWord_446655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446655).length < 2 ^ (prefixWord ++ tailWord_446655).sum := by decide
  have hdescent : baseEnd_446655 < baseStart_446655 := by decide
  rcases family_descends (prefixWord ++ tailWord_446655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446696 : List Nat := [2, 1, 4, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_446696 : Nat := 118140960795 + 446696 * 2 ^ 59
def prefixEnd_446696 : Nat := 4983230072969 + 3 ^ 40 * 446696 * 2
def baseEnd_446696 : Nat := 229369754440889533545689

theorem tailTrace_446696 : CollatzResearch.WordTrace tailWord_446696 prefixEnd_446696 229369754440889533545689 := by
  unfold tailWord_446696
  simp only [CollatzResearch.WordTrace]
  refine ⟨8146170794852078224091971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10861561059802770965455961 8146170794852078224091971)
  ·
    refine ⟨12219256192278117336137957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8146170794852078224091971 12219256192278117336137957)
    ·
      refine ⟨2291110536052147000525867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12219256192278117336137957 2291110536052147000525867)
      ·
        refine ⟨3436665804078220500788801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291110536052147000525867 3436665804078220500788801)
        ·
          refine ⟨2577499353058665375591601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3436665804078220500788801 2577499353058665375591601)
          ·
            refine ⟨1933124514793999031693701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2577499353058665375591601 1933124514793999031693701)
            ·
              refine ⟨362460846523874818442569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1933124514793999031693701 362460846523874818442569)
              ·
                refine ⟨271845634892906113831927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362460846523874818442569 271845634892906113831927)
                ·
                  refine ⟨407768452339359170747891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271845634892906113831927 407768452339359170747891)
                  ·
                    refine ⟨611652678509038756121837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 407768452339359170747891 611652678509038756121837)
                    ·
                      refine ⟨229369754440889533545689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 611652678509038756121837 229369754440889533545689)
                      ·
                        rfl

theorem cell23_446696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_446696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446696 prefixEnd_446696 := by exact prefixLift 446696
  have htrace : WordTrace (prefixWord ++ tailWord_446696) baseStart_446696 baseEnd_446696 := by
    simpa [prefixWord, tailWord_446696, baseEnd_446696] using wordTrace_append hprefix tailTrace_446696
  have hstable : (prefixWord ++ tailWord_446696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446696).length < 2 ^ (prefixWord ++ tailWord_446696).sum := by decide
  have hdescent : baseEnd_446696 < baseStart_446696 := by decide
  rcases family_descends (prefixWord ++ tailWord_446696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446705 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 3, 2, 3]
def baseStart_446705 : Nat := 118140960795 + 446705 * 2 ^ 59
def prefixEnd_446705 : Nat := 4983230072969 + 3 ^ 40 * 446705 * 2
def baseEnd_446705 : Nat := 229374375766779998333147

theorem tailTrace_446705 : CollatzResearch.WordTrace tailWord_446705 prefixEnd_446705 229374375766779998333147 := by
  unfold tailWord_446705
  simp only [CollatzResearch.WordTrace]
  refine ⟨16292669846671550985261569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10861779897781033990174379 16292669846671550985261569)
  ·
    refine ⟨12219502385003663238946177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16292669846671550985261569 12219502385003663238946177)
    ·
      refine ⟨9164626788752747429209633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12219502385003663238946177 9164626788752747429209633)
      ·
        refine ⟨6873470091564560571907225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9164626788752747429209633 6873470091564560571907225)
        ·
          refine ⟨5155102568673420428930419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6873470091564560571907225 5155102568673420428930419)
          ·
            refine ⟨7732653853010130643395629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155102568673420428930419 7732653853010130643395629)
            ·
              refine ⟨2899745194878798991273361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7732653853010130643395629 2899745194878798991273361)
              ·
                refine ⟨2174808896159099243455021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2899745194878798991273361 2174808896159099243455021)
                ·
                  refine ⟨815553336059662216295633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2174808896159099243455021 815553336059662216295633)
                  ·
                    refine ⟨611665002044746662221725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 815553336059662216295633 611665002044746662221725)
                    ·
                      refine ⟨229374375766779998333147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 611665002044746662221725 229374375766779998333147)
                      ·
                        rfl

theorem cell23_446705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_446705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446705 prefixEnd_446705 := by exact prefixLift 446705
  have htrace : WordTrace (prefixWord ++ tailWord_446705) baseStart_446705 baseEnd_446705 := by
    simpa [prefixWord, tailWord_446705, baseEnd_446705] using wordTrace_append hprefix tailTrace_446705
  have hstable : (prefixWord ++ tailWord_446705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446705).length < 2 ^ (prefixWord ++ tailWord_446705).sum := by decide
  have hdescent : baseEnd_446705 < baseStart_446705 := by decide
  rcases family_descends (prefixWord ++ tailWord_446705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446746 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 2, 4]
def baseStart_446746 : Nat := 118140960795 + 446746 * 2 ^ 59
def prefixEnd_446746 : Nat := 4983230072969 + 3 ^ 40 * 446746 * 2
def baseEnd_446746 : Nat := 76465142824538112640153

theorem tailTrace_446746 : CollatzResearch.WordTrace tailWord_446746 prefixEnd_446746 76465142824538112640153 := by
  unfold tailWord_446746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4073541309880753746876023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10862776826348676658336061 4073541309880753746876023)
  ·
    refine ⟨6110311964821130620314035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4073541309880753746876023 6110311964821130620314035)
    ·
      refine ⟨9165467947231695930471053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6110311964821130620314035 9165467947231695930471053)
      ·
        refine ⟨3437050480211885973926645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9165467947231695930471053 3437050480211885973926645)
        ·
          refine ⟨322223482519864310055623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3437050480211885973926645 322223482519864310055623)
          ·
            refine ⟨483335223779796465083435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322223482519864310055623 483335223779796465083435)
            ·
              refine ⟨725002835669694697625153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483335223779796465083435 725002835669694697625153)
              ·
                refine ⟨543752126752271023218865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725002835669694697625153 543752126752271023218865)
                ·
                  refine ⟨407814095064203267414149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543752126752271023218865 407814095064203267414149)
                  ·
                    refine ⟨76465142824538112640153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 407814095064203267414149 76465142824538112640153)
                    ·
                      rfl

theorem cell23_446746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_446746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446746 prefixEnd_446746 := by exact prefixLift 446746
  have htrace : WordTrace (prefixWord ++ tailWord_446746) baseStart_446746 baseEnd_446746 := by
    simpa [prefixWord, tailWord_446746, baseEnd_446746] using wordTrace_append hprefix tailTrace_446746
  have hstable : (prefixWord ++ tailWord_446746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446746).length < 2 ^ (prefixWord ++ tailWord_446746).sum := by decide
  have hdescent : baseEnd_446746 < baseStart_446746 := by decide
  rcases family_descends (prefixWord ++ tailWord_446746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446766 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_446766 : Nat := 118140960795 + 446766 * 2 ^ 59
def prefixEnd_446766 : Nat := 4983230072969 + 3 ^ 40 * 446766 * 2
def baseEnd_446766 : Nat := 229405698086704259670367

theorem tailTrace_446766 : CollatzResearch.WordTrace tailWord_446766 prefixEnd_446766 229405698086704259670367 := by
  unfold tailWord_446766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2036861837431319800404019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10863263132967038935488101 2036861837431319800404019)
  ·
    refine ⟨3055292756146979700606029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2036861837431319800404019 3055292756146979700606029)
    ·
      refine ⟨1145734783555117387727261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3055292756146979700606029 1145734783555117387727261)
      ·
        refine ⟨429650543833169020397723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1145734783555117387727261 429650543833169020397723)
        ·
          refine ⟨644475815749753530596585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429650543833169020397723 644475815749753530596585)
          ·
            refine ⟨483356861812315147947439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644475815749753530596585 483356861812315147947439)
            ·
              refine ⟨725035292718472721921159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483356861812315147947439 725035292718472721921159)
              ·
                refine ⟨1087552939077709082881739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725035292718472721921159 1087552939077709082881739)
                ·
                  refine ⟨1631329408616563624322609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087552939077709082881739 1631329408616563624322609)
                  ·
                    refine ⟨1223497056462422718241957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1631329408616563624322609 1223497056462422718241957)
                    ·
                      refine ⟨229405698086704259670367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1223497056462422718241957 229405698086704259670367)
                      ·
                        rfl

theorem cell23_446766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_446766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446766 prefixEnd_446766 := by exact prefixLift 446766
  have htrace : WordTrace (prefixWord ++ tailWord_446766) baseStart_446766 baseEnd_446766 := by
    simpa [prefixWord, tailWord_446766, baseEnd_446766] using wordTrace_append hprefix tailTrace_446766
  have hstable : (prefixWord ++ tailWord_446766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446766).length < 2 ^ (prefixWord ++ tailWord_446766).sum := by decide
  have hdescent : baseEnd_446766 < baseStart_446766 := by decide
  rcases family_descends (prefixWord ++ tailWord_446766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446768 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 1, 8]
def baseStart_446768 : Nat := 118140960795 + 446768 * 2 ^ 59
def prefixEnd_446768 : Nat := 4983230072969 + 3 ^ 40 * 446768 * 2
def baseEnd_446768 : Nat := 76468908349337750615119

theorem tailTrace_446768 : CollatzResearch.WordTrace tailWord_446768 prefixEnd_446768 76468908349337750615119 := by
  unfold tailWord_446768
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147483822721656372402479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10863311763628875163203305 8147483822721656372402479)
  ·
    refine ⟨12221225734082484558603719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8147483822721656372402479 12221225734082484558603719)
    ·
      refine ⟨18331838601123726837905579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12221225734082484558603719 18331838601123726837905579)
      ·
        refine ⟨27497757901685590256858369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18331838601123726837905579 27497757901685590256858369)
        ·
          refine ⟨20623318426264192692643777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27497757901685590256858369 20623318426264192692643777)
          ·
            refine ⟨15467488819698144519482833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20623318426264192692643777 15467488819698144519482833)
            ·
              refine ⟨11600616614773608389612125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15467488819698144519482833 11600616614773608389612125)
              ·
                refine ⟨4350231230540103146104547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11600616614773608389612125 4350231230540103146104547)
                ·
                  refine ⟨6525346845810154719156821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4350231230540103146104547 6525346845810154719156821)
                  ·
                    refine ⟨76468908349337750615119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6525346845810154719156821 76468908349337750615119)
                    ·
                      rfl

theorem cell23_446768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_446768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446768 prefixEnd_446768 := by exact prefixLift 446768
  have htrace : WordTrace (prefixWord ++ tailWord_446768) baseStart_446768 baseEnd_446768 := by
    simpa [prefixWord, tailWord_446768, baseEnd_446768] using wordTrace_append hprefix tailTrace_446768
  have hstable : (prefixWord ++ tailWord_446768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446768).length < 2 ^ (prefixWord ++ tailWord_446768).sum := by decide
  have hdescent : baseEnd_446768 < baseStart_446768 := by decide
  rcases family_descends (prefixWord ++ tailWord_446768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446769 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 1, 3, 3]
def baseStart_446769 : Nat := 118140960795 + 446769 * 2 ^ 59
def prefixEnd_446769 : Nat := 4983230072969 + 3 ^ 40 * 446769 * 2
def baseEnd_446769 : Nat := 229407238528667747932853

theorem tailTrace_446769 : CollatzResearch.WordTrace tailWord_446769 prefixEnd_446769 229407238528667747932853 := by
  unfold tailWord_446769
  simp only [CollatzResearch.WordTrace]
  refine ⟨16295004118439689915591361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10863336078959793277060907 16295004118439689915591361)
  ·
    refine ⟨12221253088829767436693521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16295004118439689915591361 12221253088829767436693521)
    ·
      refine ⟨9165939816622325577520141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12221253088829767436693521 9165939816622325577520141)
      ·
        refine ⟨3437227431233372091570053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9165939816622325577520141 3437227431233372091570053)
        ·
          refine ⟨644480143356257267169385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3437227431233372091570053 644480143356257267169385)
          ·
            refine ⟨483360107517192950377039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644480143356257267169385 483360107517192950377039)
            ·
              refine ⟨725040161275789425565559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483360107517192950377039 725040161275789425565559)
              ·
                refine ⟨1087560241913684138348339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725040161275789425565559 1087560241913684138348339)
                ·
                  refine ⟨1631340362870526207522509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087560241913684138348339 1631340362870526207522509)
                  ·
                    refine ⟨611752636076447327820941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1631340362870526207522509 611752636076447327820941)
                    ·
                      refine ⟨229407238528667747932853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 611752636076447327820941 229407238528667747932853)
                      ·
                        rfl

theorem cell23_446769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_446769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446769 prefixEnd_446769 := by exact prefixLift 446769
  have htrace : WordTrace (prefixWord ++ tailWord_446769) baseStart_446769 baseEnd_446769 := by
    simpa [prefixWord, tailWord_446769, baseEnd_446769] using wordTrace_append hprefix tailTrace_446769
  have hstable : (prefixWord ++ tailWord_446769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446769).length < 2 ^ (prefixWord ++ tailWord_446769).sum := by decide
  have hdescent : baseEnd_446769 < baseStart_446769 := by decide
  rcases family_descends (prefixWord ++ tailWord_446769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446792 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 1, 4, 2]
def baseStart_446792 : Nat := 118140960795 + 446792 * 2 ^ 59
def prefixEnd_446792 : Nat := 4983230072969 + 3 ^ 40 * 446792 * 2
def baseEnd_446792 : Nat := 229419048583721157945247

theorem tailTrace_446792 : CollatzResearch.WordTrace tailWord_446792 prefixEnd_446792 229419048583721157945247 := by
  unfold tailWord_446792
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147921498678182421839315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10863895331570909895785753 8147921498678182421839315)
  ·
    refine ⟨12221882248017273632758973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8147921498678182421839315 12221882248017273632758973)
    ·
      refine ⟨4583205843006477612284615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12221882248017273632758973 4583205843006477612284615)
      ·
        refine ⟨6874808764509716418426923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583205843006477612284615 6874808764509716418426923)
        ·
          refine ⟨10312213146764574627640385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6874808764509716418426923 10312213146764574627640385)
          ·
            refine ⟨7734159860073430970730289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10312213146764574627640385 7734159860073430970730289)
            ·
              refine ⟨5800619895055073228047717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7734159860073430970730289 5800619895055073228047717)
              ·
                refine ⟨1087616230322826230258947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5800619895055073228047717 1087616230322826230258947)
                ·
                  refine ⟨1631424345484239345388421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087616230322826230258947 1631424345484239345388421)
                  ·
                    refine ⟨305892064778294877260329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1631424345484239345388421 305892064778294877260329)
                    ·
                      refine ⟨229419048583721157945247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305892064778294877260329 229419048583721157945247)
                      ·
                        rfl

theorem cell23_446792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_446792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446792 prefixEnd_446792 := by exact prefixLift 446792
  have htrace : WordTrace (prefixWord ++ tailWord_446792) baseStart_446792 baseEnd_446792 := by
    simpa [prefixWord, tailWord_446792, baseEnd_446792] using wordTrace_append hprefix tailTrace_446792
  have hstable : (prefixWord ++ tailWord_446792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446792).length < 2 ^ (prefixWord ++ tailWord_446792).sum := by decide
  have hdescent : baseEnd_446792 < baseStart_446792 := by decide
  rcases family_descends (prefixWord ++ tailWord_446792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446809 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 2, 2, 2]
def baseStart_446809 : Nat := 118140960795 + 446809 * 2 ^ 59
def prefixEnd_446809 : Nat := 4983230072969 + 3 ^ 40 * 446809 * 2
def baseEnd_446809 : Nat := 229427777754847591432669

theorem tailTrace_446809 : CollatzResearch.WordTrace tailWord_446809 prefixEnd_446809 229427777754847591432669 := by
  unfold tailWord_446809
  simp only [CollatzResearch.WordTrace]
  refine ⟨16296463038294776747047481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10864308692196517831364987 16296463038294776747047481)
  ·
    refine ⟨12222347278721082560285611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16296463038294776747047481 12222347278721082560285611)
    ·
      refine ⟨18333520918081623840428417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12222347278721082560285611 18333520918081623840428417)
      ·
        refine ⟨13750140688561217880321313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18333520918081623840428417 13750140688561217880321313)
        ·
          refine ⟨10312605516420913410240985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13750140688561217880321313 10312605516420913410240985)
          ·
            refine ⟨7734454137315685057680739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10312605516420913410240985 7734454137315685057680739)
            ·
              refine ⟨11601681205973527586521109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7734454137315685057680739 11601681205973527586521109)
              ·
                refine ⟨543828806530009105618177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11601681205973527586521109 543828806530009105618177)
                ·
                  refine ⟨407871604897506829213633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543828806530009105618177 407871604897506829213633)
                  ·
                    refine ⟨305903703673130121910225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 407871604897506829213633 305903703673130121910225)
                    ·
                      refine ⟨229427777754847591432669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 305903703673130121910225 229427777754847591432669)
                      ·
                        rfl

theorem cell23_446809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 2, 2].length) (baseStart_446809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446809 prefixEnd_446809 := by exact prefixLift 446809
  have htrace : WordTrace (prefixWord ++ tailWord_446809) baseStart_446809 baseEnd_446809 := by
    simpa [prefixWord, tailWord_446809, baseEnd_446809] using wordTrace_append hprefix tailTrace_446809
  have hstable : (prefixWord ++ tailWord_446809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446809).length < 2 ^ (prefixWord ++ tailWord_446809).sum := by decide
  have hdescent : baseEnd_446809 < baseStart_446809 := by decide
  rcases family_descends (prefixWord ++ tailWord_446809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446814 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_446814 : Nat := 118140960795 + 446814 * 2 ^ 59
def prefixEnd_446814 : Nat := 4983230072969 + 3 ^ 40 * 446814 * 2
def baseEnd_446814 : Nat := 76476781719373357290049

theorem tailTrace_446814 : CollatzResearch.WordTrace tailWord_446814 prefixEnd_446814 76476781719373357290049 := by
  unfold tailWord_446814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037080675409582825122437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10864430268851108400652997 2037080675409582825122437)
  ·
    refine ⟨381952626639296779710457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2037080675409582825122437 381952626639296779710457)
    ·
      refine ⟨286464469979472584782843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381952626639296779710457 286464469979472584782843)
      ·
        refine ⟨429696704969208877174265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286464469979472584782843 429696704969208877174265)
        ·
          refine ⟨322272528726906657880699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429696704969208877174265 322272528726906657880699)
          ·
            refine ⟨483408793090359986821049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322272528726906657880699 483408793090359986821049)
            ·
              refine ⟨362556594817769990115787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483408793090359986821049 362556594817769990115787)
              ·
                refine ⟨543834892226654985173681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362556594817769990115787 543834892226654985173681)
                ·
                  refine ⟨407876169169991238880261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543834892226654985173681 407876169169991238880261)
                  ·
                    refine ⟨76476781719373357290049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 407876169169991238880261 76476781719373357290049)
                    ·
                      rfl

theorem cell23_446814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_446814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446814 prefixEnd_446814 := by exact prefixLift 446814
  have htrace : WordTrace (prefixWord ++ tailWord_446814) baseStart_446814 baseEnd_446814 := by
    simpa [prefixWord, tailWord_446814, baseEnd_446814] using wordTrace_append hprefix tailTrace_446814
  have hstable : (prefixWord ++ tailWord_446814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446814).length < 2 ^ (prefixWord ++ tailWord_446814).sum := by decide
  have hdescent : baseEnd_446814 < baseStart_446814 := by decide
  rcases family_descends (prefixWord ++ tailWord_446814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446815 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 7]
def baseStart_446815 : Nat := 118140960795 + 446815 * 2 ^ 59
def prefixEnd_446815 : Nat := 4983230072969 + 3 ^ 40 * 446815 * 2
def baseEnd_446815 : Nat := 25492317626530507550849

theorem tailTrace_446815 : CollatzResearch.WordTrace tailWord_446815 prefixEnd_446815 25492317626530507550849 := by
  unfold tailWord_446815
  simp only [CollatzResearch.WordTrace]
  refine ⟨16296681876273039771765899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10864454584182026514510599 16296681876273039771765899)
  ·
    refine ⟨24445022814409559657648849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16296681876273039771765899 24445022814409559657648849)
    ·
      refine ⟨18333767110807169743236637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24445022814409559657648849 18333767110807169743236637)
      ·
        refine ⟨6875162666552688653713739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18333767110807169743236637 6875162666552688653713739)
        ·
          refine ⟨10312743999829032980570609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875162666552688653713739 10312743999829032980570609)
          ·
            refine ⟨7734557999871774735427957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10312743999829032980570609 7734557999871774735427957)
            ·
              refine ⟨725114812487978881446371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7734557999871774735427957 725114812487978881446371)
              ·
                refine ⟨1087672218731968322169557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725114812487978881446371 1087672218731968322169557)
                ·
                  refine ⟨25492317626530507550849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1087672218731968322169557 25492317626530507550849)
                  ·
                    rfl

theorem cell23_446815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 7].length) (baseStart_446815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446815 prefixEnd_446815 := by exact prefixLift 446815
  have htrace : WordTrace (prefixWord ++ tailWord_446815) baseStart_446815 baseEnd_446815 := by
    simpa [prefixWord, tailWord_446815, baseEnd_446815] using wordTrace_append hprefix tailTrace_446815
  have hstable : (prefixWord ++ tailWord_446815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446815).length < 2 ^ (prefixWord ++ tailWord_446815).sum := by decide
  have hdescent : baseEnd_446815 < baseStart_446815 := by decide
  rcases family_descends (prefixWord ++ tailWord_446815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446825 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 1, 5, 3]
def baseStart_446825 : Nat := 118140960795 + 446825 * 2 ^ 59
def prefixEnd_446825 : Nat := 4983230072969 + 3 ^ 40 * 446825 * 2
def baseEnd_446825 : Nat := 229435993445319528832595

theorem tailTrace_446825 : CollatzResearch.WordTrace tailWord_446825 prefixEnd_446825 229435993445319528832595 := by
  unfold tailWord_446825
  simp only [CollatzResearch.WordTrace]
  refine ⟨16297046606236811479629929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10864697737491207653086619 16297046606236811479629929)
  ·
    refine ⟨12222784954677608609722447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16297046606236811479629929 12222784954677608609722447)
    ·
      refine ⟨18334177432016412914583671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12222784954677608609722447 18334177432016412914583671)
      ·
        refine ⟨27501266148024619371875507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18334177432016412914583671 27501266148024619371875507)
        ·
          refine ⟨41251899222036929057813261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27501266148024619371875507 41251899222036929057813261)
          ·
            refine ⟨15469462208263848396679973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41251899222036929057813261 15469462208263848396679973)
            ·
              refine ⟨2900524164049471574377495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15469462208263848396679973 2900524164049471574377495)
              ·
                refine ⟨4350786246074207361566243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2900524164049471574377495 4350786246074207361566243)
                ·
                  refine ⟨6526179369111311042349365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4350786246074207361566243 6526179369111311042349365)
                  ·
                    refine ⟨611829315854185410220253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6526179369111311042349365 611829315854185410220253)
                    ·
                      refine ⟨229435993445319528832595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 611829315854185410220253 229435993445319528832595)
                      ·
                        rfl

theorem cell23_446825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 5, 3].length) (baseStart_446825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446825 prefixEnd_446825 := by exact prefixLift 446825
  have htrace : WordTrace (prefixWord ++ tailWord_446825) baseStart_446825 baseEnd_446825 := by
    simpa [prefixWord, tailWord_446825, baseEnd_446825] using wordTrace_append hprefix tailTrace_446825
  have hstable : (prefixWord ++ tailWord_446825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446825).length < 2 ^ (prefixWord ++ tailWord_446825).sum := by decide
  have hdescent : baseEnd_446825 < baseStart_446825 := by decide
  rcases family_descends (prefixWord ++ tailWord_446825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446855 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_446855 : Nat := 118140960795 + 446855 * 2 ^ 59
def prefixEnd_446855 : Nat := 4983230072969 + 3 ^ 40 * 446855 * 2
def baseEnd_446855 : Nat := 229451397864954411457457

theorem tailTrace_446855 : CollatzResearch.WordTrace tailWord_446855 prefixEnd_446855 229451397864954411457457 := by
  unfold tailWord_446855
  simp only [CollatzResearch.WordTrace]
  refine ⟨16298140796128126603222019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10865427197418751068814679 16298140796128126603222019)
  ·
    refine ⟨24447211194192189904833029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16298140796128126603222019 24447211194192189904833029)
    ·
      refine ⟨4583852098911035607156193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24447211194192189904833029 4583852098911035607156193)
      ·
        refine ⟨3437889074183276705367145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4583852098911035607156193 3437889074183276705367145)
        ·
          refine ⟨2578416805637457529025359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3437889074183276705367145 2578416805637457529025359)
          ·
            refine ⟨3867625208456186293538039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578416805637457529025359 3867625208456186293538039)
            ·
              refine ⟨5801437812684279440307059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867625208456186293538039 5801437812684279440307059)
              ·
                refine ⟨8702156719026419160460589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5801437812684279440307059 8702156719026419160460589)
                ·
                  refine ⟨3263308769634907185172721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8702156719026419160460589 3263308769634907185172721)
                  ·
                    refine ⟨2447481577226180388879541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3263308769634907185172721 2447481577226180388879541)
                    ·
                      refine ⟨229451397864954411457457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2447481577226180388879541 229451397864954411457457)
                      ·
                        rfl

theorem cell23_446855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_446855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446855 prefixEnd_446855 := by exact prefixLift 446855
  have htrace : WordTrace (prefixWord ++ tailWord_446855) baseStart_446855 baseEnd_446855 := by
    simpa [prefixWord, tailWord_446855, baseEnd_446855] using wordTrace_append hprefix tailTrace_446855
  have hstable : (prefixWord ++ tailWord_446855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446855).length < 2 ^ (prefixWord ++ tailWord_446855).sum := by decide
  have hdescent : baseEnd_446855 < baseStart_446855 := by decide
  rcases family_descends (prefixWord ++ tailWord_446855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446872 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_446872 : Nat := 118140960795 + 446872 * 2 ^ 59
def prefixEnd_446872 : Nat := 4983230072969 + 3 ^ 40 * 446872 * 2
def baseEnd_446872 : Nat := 229460127036080844944879

theorem tailTrace_446872 : CollatzResearch.WordTrace tailWord_446872 prefixEnd_446872 229460127036080844944879 := by
  unfold tailWord_446872
  simp only [CollatzResearch.WordTrace]
  refine ⟨8149380418533269253295435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10865840558044359004393913 8149380418533269253295435)
  ·
    refine ⟨12224070627799903879943153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8149380418533269253295435 12224070627799903879943153)
    ·
      refine ⟨9168052970849927909957365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12224070627799903879943153 9168052970849927909957365)
      ·
        refine ⟨859504966017180741558503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9168052970849927909957365 859504966017180741558503)
        ·
          refine ⟨1289257449025771112337755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859504966017180741558503 1289257449025771112337755)
          ·
            refine ⟨1933886173538656668506633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289257449025771112337755 1933886173538656668506633)
            ·
              refine ⟨1450414630153992501379975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1933886173538656668506633 1450414630153992501379975)
              ·
                refine ⟨2175621945230988752069963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450414630153992501379975 2175621945230988752069963)
                ·
                  refine ⟨3263432917846483128104945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175621945230988752069963 3263432917846483128104945)
                  ·
                    refine ⟨2447574688384862346078709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3263432917846483128104945 2447574688384862346078709)
                    ·
                      refine ⟨229460127036080844944879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2447574688384862346078709 229460127036080844944879)
                      ·
                        rfl

theorem cell23_446872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_446872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446872 prefixEnd_446872 := by exact prefixLift 446872
  have htrace : WordTrace (prefixWord ++ tailWord_446872) baseStart_446872 baseEnd_446872 := by
    simpa [prefixWord, tailWord_446872, baseEnd_446872] using wordTrace_append hprefix tailTrace_446872
  have hstable : (prefixWord ++ tailWord_446872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446872).length < 2 ^ (prefixWord ++ tailWord_446872).sum := by decide
  have hdescent : baseEnd_446872 < baseStart_446872 := by decide
  rcases family_descends (prefixWord ++ tailWord_446872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446882 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_446882 : Nat := 118140960795 + 446882 * 2 ^ 59
def prefixEnd_446882 : Nat := 4983230072969 + 3 ^ 40 * 446882 * 2
def baseEnd_446882 : Nat := 229465261842625805819833

theorem tailTrace_446882 : CollatzResearch.WordTrace tailWord_446882 prefixEnd_446882 229465261842625805819833 := by
  unfold tailWord_446882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4074781391757577553613725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10866083711353540142969933 4074781391757577553613725)
  ·
    refine ⟨1528043021909091582605147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4074781391757577553613725 1528043021909091582605147)
    ·
      refine ⟨2292064532863637373907721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528043021909091582605147 2292064532863637373907721)
      ·
        refine ⟨1719048399647728030430791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2292064532863637373907721 1719048399647728030430791)
        ·
          refine ⟨2578572599471592045646187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1719048399647728030430791 2578572599471592045646187)
          ·
            refine ⟨3867858899207388068469281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578572599471592045646187 3867858899207388068469281)
            ·
              refine ⟨2900894174405541051351961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3867858899207388068469281 2900894174405541051351961)
              ·
                refine ⟨2175670630804155788513971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2900894174405541051351961 2175670630804155788513971)
                ·
                  refine ⟨3263505946206233682770957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2175670630804155788513971 3263505946206233682770957)
                  ·
                    refine ⟨1223814729827337631039109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3263505946206233682770957 1223814729827337631039109)
                    ·
                      refine ⟨229465261842625805819833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1223814729827337631039109 229465261842625805819833)
                      ·
                        rfl

theorem cell23_446882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_446882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446882 prefixEnd_446882 := by exact prefixLift 446882
  have htrace : WordTrace (prefixWord ++ tailWord_446882) baseStart_446882 baseEnd_446882 := by
    simpa [prefixWord, tailWord_446882, baseEnd_446882] using wordTrace_append hprefix tailTrace_446882
  have hstable : (prefixWord ++ tailWord_446882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446882).length < 2 ^ (prefixWord ++ tailWord_446882).sum := by decide
  have hdescent : baseEnd_446882 < baseStart_446882 := by decide
  rcases family_descends (prefixWord ++ tailWord_446882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446959 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 2, 3, 2]
def baseStart_446959 : Nat := 118140960795 + 446959 * 2 ^ 59
def prefixEnd_446959 : Nat := 4983230072969 + 3 ^ 40 * 446959 * 2
def baseEnd_446959 : Nat := 229504799853022004556979

theorem tailTrace_446959 : CollatzResearch.WordTrace tailWord_446959 prefixEnd_446959 229504799853022004556979 := by
  unfold tailWord_446959
  simp only [CollatzResearch.WordTrace]
  refine ⟨16301933987751352365007931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10867955991834234910005287 16301933987751352365007931)
  ·
    refine ⟨24452900981627028547511897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16301933987751352365007931 24452900981627028547511897)
    ·
      refine ⟨18339675736220271410633923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24452900981627028547511897 18339675736220271410633923)
      ·
        refine ⟨27509513604330407115950885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18339675736220271410633923 27509513604330407115950885)
        ·
          refine ⟨5158033800811951334240791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27509513604330407115950885 5158033800811951334240791)
          ·
            refine ⟨7737050701217927001361187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158033800811951334240791 7737050701217927001361187)
            ·
              refine ⟨11605576051826890502041781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7737050701217927001361187 11605576051826890502041781)
              ·
                refine ⟨1088022754858770984566417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11605576051826890502041781 1088022754858770984566417)
                ·
                  refine ⟨816017066144078238424813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1088022754858770984566417 816017066144078238424813)
                  ·
                    refine ⟨306006399804029339409305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 816017066144078238424813 306006399804029339409305)
                    ·
                      refine ⟨229504799853022004556979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 306006399804029339409305 229504799853022004556979)
                      ·
                        rfl

theorem cell23_446959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 3, 2].length) (baseStart_446959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446959 prefixEnd_446959 := by exact prefixLift 446959
  have htrace : WordTrace (prefixWord ++ tailWord_446959) baseStart_446959 baseEnd_446959 := by
    simpa [prefixWord, tailWord_446959, baseEnd_446959] using wordTrace_append hprefix tailTrace_446959
  have hstable : (prefixWord ++ tailWord_446959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446959).length < 2 ^ (prefixWord ++ tailWord_446959).sum := by decide
  have hdescent : baseEnd_446959 < baseStart_446959 := by decide
  rcases family_descends (prefixWord ++ tailWord_446959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446972 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_446972 : Nat := 118140960795 + 446972 * 2 ^ 59
def prefixEnd_446972 : Nat := 4983230072969 + 3 ^ 40 * 446972 * 2
def baseEnd_446972 : Nat := 229511475101530453694419

theorem tailTrace_446972 : CollatzResearch.WordTrace tailWord_446972 prefixEnd_446972 229511475101530453694419 := by
  unfold tailWord_446972
  simp only [CollatzResearch.WordTrace]
  refine ⟨8151204068352127792615585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10868272091136170390154113 8151204068352127792615585)
  ·
    refine ⟨6113403051264095844461689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8151204068352127792615585 6113403051264095844461689)
    ·
      refine ⟨4585052288448071883346267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6113403051264095844461689 4585052288448071883346267)
      ·
        refine ⟨6877578432672107825019401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4585052288448071883346267 6877578432672107825019401)
        ·
          refine ⟨5158183824504080868764551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6877578432672107825019401 5158183824504080868764551)
          ·
            refine ⟨7737275736756121303146827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158183824504080868764551 7737275736756121303146827)
            ·
              refine ⟨11605913605134181954720241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7737275736756121303146827 11605913605134181954720241)
              ·
                refine ⟨8704435203850636466040181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11605913605134181954720241 8704435203850636466040181)
                ·
                  refine ⟨816040800360997168691267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8704435203850636466040181 816040800360997168691267)
                  ·
                    refine ⟨1224061200541495753036901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 816040800360997168691267 1224061200541495753036901)
                    ·
                      refine ⟨229511475101530453694419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1224061200541495753036901 229511475101530453694419)
                      ·
                        rfl

theorem cell23_446972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_446972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446972 prefixEnd_446972 := by exact prefixLift 446972
  have htrace : WordTrace (prefixWord ++ tailWord_446972) baseStart_446972 baseEnd_446972 := by
    simpa [prefixWord, tailWord_446972, baseEnd_446972] using wordTrace_append hprefix tailTrace_446972
  have hstable : (prefixWord ++ tailWord_446972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446972).length < 2 ^ (prefixWord ++ tailWord_446972).sum := by decide
  have hdescent : baseEnd_446972 < baseStart_446972 := by decide
  rcases family_descends (prefixWord ++ tailWord_446972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446983 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_446983 : Nat := 118140960795 + 446983 * 2 ^ 59
def prefixEnd_446983 : Nat := 4983230072969 + 3 ^ 40 * 446983 * 2
def baseEnd_446983 : Nat := 229517123388729910656869

theorem tailTrace_446983 : CollatzResearch.WordTrace tailWord_446983 prefixEnd_446983 229517123388729910656869 := by
  unfold tailWord_446983
  simp only [CollatzResearch.WordTrace]
  refine ⟨16302809339664404463881603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10868539559776269642587735 16302809339664404463881603)
  ·
    refine ⟨24454214009496606695822405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16302809339664404463881603 24454214009496606695822405)
    ·
      refine ⟨4585165126780613755466701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24454214009496606695822405 4585165126780613755466701)
      ·
        refine ⟨1719436922542730158300013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4585165126780613755466701 1719436922542730158300013)
        ·
          refine ⟨644788845953523809362505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1719436922542730158300013 644788845953523809362505)
          ·
            refine ⟨483591634465142857021879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644788845953523809362505 483591634465142857021879)
            ·
              refine ⟨725387451697714285532819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483591634465142857021879 725387451697714285532819)
              ·
                refine ⟨1088081177546571428299229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725387451697714285532819 1088081177546571428299229)
                ·
                  refine ⟨408030441579964285612211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1088081177546571428299229 408030441579964285612211)
                  ·
                    refine ⟨612045662369946428418317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 408030441579964285612211 612045662369946428418317)
                    ·
                      refine ⟨229517123388729910656869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 612045662369946428418317 229517123388729910656869)
                      ·
                        rfl

theorem cell23_446983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_446983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_446983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_446983 prefixEnd_446983 := by exact prefixLift 446983
  have htrace : WordTrace (prefixWord ++ tailWord_446983) baseStart_446983 baseEnd_446983 := by
    simpa [prefixWord, tailWord_446983, baseEnd_446983] using wordTrace_append hprefix tailTrace_446983
  have hstable : (prefixWord ++ tailWord_446983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446983).length < 2 ^ (prefixWord ++ tailWord_446983).sum := by decide
  have hdescent : baseEnd_446983 < baseStart_446983 := by decide
  rcases family_descends (prefixWord ++ tailWord_446983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447002 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_447002 : Nat := 118140960795 + 447002 * 2 ^ 59
def prefixEnd_447002 : Nat := 4983230072969 + 3 ^ 40 * 447002 * 2
def baseEnd_447002 : Nat := 229526879521165336319281

theorem tailTrace_447002 : CollatzResearch.WordTrace tailWord_447002 prefixEnd_447002 229526879521165336319281 := by
  unfold tailWord_447002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075875581648892677205815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10869001551063713805882173 4075875581648892677205815)
  ·
    refine ⟨6113813372473339015808723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4075875581648892677205815 6113813372473339015808723)
    ·
      refine ⟨9170720058710008523713085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6113813372473339015808723 9170720058710008523713085)
      ·
        refine ⟨3439020022016253196392407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9170720058710008523713085 3439020022016253196392407)
        ·
          refine ⟨5158530033024379794588611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3439020022016253196392407 5158530033024379794588611)
          ·
            refine ⟨7737795049536569691882917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5158530033024379794588611 7737795049536569691882917)
            ·
              refine ⟨1450836571788106817228047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7737795049536569691882917 1450836571788106817228047)
              ·
                refine ⟨2176254857682160225842071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450836571788106817228047 2176254857682160225842071)
                ·
                  refine ⟨3264382286523240338763107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176254857682160225842071 3264382286523240338763107)
                  ·
                    refine ⟨4896573429784860508144661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3264382286523240338763107 4896573429784860508144661)
                    ·
                      refine ⟨229526879521165336319281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4896573429784860508144661 229526879521165336319281)
                      ·
                        rfl

theorem cell23_447002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_447002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447002 prefixEnd_447002 := by exact prefixLift 447002
  have htrace : WordTrace (prefixWord ++ tailWord_447002) baseStart_447002 baseEnd_447002 := by
    simpa [prefixWord, tailWord_447002, baseEnd_447002] using wordTrace_append hprefix tailTrace_447002
  have hstable : (prefixWord ++ tailWord_447002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447002).length < 2 ^ (prefixWord ++ tailWord_447002).sum := by decide
  have hdescent : baseEnd_447002 < baseStart_447002 := by decide
  rcases family_descends (prefixWord ++ tailWord_447002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447009 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_447009 : Nat := 118140960795 + 447009 * 2 ^ 59
def prefixEnd_447009 : Nat := 4983230072969 + 3 ^ 40 * 447009 * 2
def baseEnd_447009 : Nat := 229530473885746808931749

theorem tailTrace_447009 : CollatzResearch.WordTrace tailWord_447009 prefixEnd_447009 229530473885746808931749 := by
  unfold tailWord_447009
  simp only [CollatzResearch.WordTrace]
  refine ⟨16303757637570210904328081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10869171758380140602885387 16303757637570210904328081)
  ·
    refine ⟨12227818228177658178246061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16303757637570210904328081 12227818228177658178246061)
    ·
      refine ⟨4585431835566621816842273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12227818228177658178246061 4585431835566621816842273)
      ·
        refine ⟨3439073876674966362631705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4585431835566621816842273 3439073876674966362631705)
        ·
          refine ⟨2579305407506224771973779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3439073876674966362631705 2579305407506224771973779)
          ·
            refine ⟨3868958111259337157960669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2579305407506224771973779 3868958111259337157960669)
            ·
              refine ⟨1450859291722251434235251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3868958111259337157960669 1450859291722251434235251)
              ·
                refine ⟨2176288937583377151352877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450859291722251434235251 2176288937583377151352877)
                ·
                  refine ⟨816108351593766431757329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2176288937583377151352877 816108351593766431757329)
                  ·
                    refine ⟨612081263695324823817997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 816108351593766431757329 612081263695324823817997)
                    ·
                      refine ⟨229530473885746808931749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 612081263695324823817997 229530473885746808931749)
                      ·
                        rfl

theorem cell23_447009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_447009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447009 prefixEnd_447009 := by exact prefixLift 447009
  have htrace : WordTrace (prefixWord ++ tailWord_447009) baseStart_447009 baseEnd_447009 := by
    simpa [prefixWord, tailWord_447009, baseEnd_447009] using wordTrace_append hprefix tailTrace_447009
  have hstable : (prefixWord ++ tailWord_447009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447009).length < 2 ^ (prefixWord ++ tailWord_447009).sum := by decide
  have hdescent : baseEnd_447009 < baseStart_447009 := by decide
  rcases family_descends (prefixWord ++ tailWord_447009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447040 : List Nat := [2, 1, 1, 2, 2, 2, 6, 2, 1, 2, 2]
def baseStart_447040 : Nat := 118140960795 + 447040 * 2 ^ 59
def prefixEnd_447040 : Nat := 4983230072969 + 3 ^ 40 * 447040 * 2
def baseEnd_447040 : Nat := 229546391786036187644107

theorem tailTrace_447040 : CollatzResearch.WordTrace tailWord_447040 prefixEnd_447040 229546391786036187644107 := by
  unfold tailWord_447040
  simp only [CollatzResearch.WordTrace]
  refine ⟨8152444150228951599353287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10869925533638602132471049 8152444150228951599353287)
  ·
    refine ⟨12228666225343427399029931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8152444150228951599353287 12228666225343427399029931)
    ·
      refine ⟨18342999338015141098544897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12228666225343427399029931 18342999338015141098544897)
      ·
        refine ⟨13757249503511355823908673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18342999338015141098544897 13757249503511355823908673)
        ·
          refine ⟨10317937127633516867931505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13757249503511355823908673 10317937127633516867931505)
          ·
            refine ⟨7738452845725137650948629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10317937127633516867931505 7738452845725137650948629)
            ·
              refine ⟨362739977143365827388217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7738452845725137650948629 362739977143365827388217)
              ·
                refine ⟨272054982857524370541163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362739977143365827388217 272054982857524370541163)
                ·
                  refine ⟨408082474286286555811745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272054982857524370541163 408082474286286555811745)
                  ·
                    refine ⟨306061855714714916858809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 408082474286286555811745 306061855714714916858809)
                    ·
                      refine ⟨229546391786036187644107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 306061855714714916858809 229546391786036187644107)
                      ·
                        rfl

theorem cell23_447040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 1, 2, 2].length) (baseStart_447040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447040 prefixEnd_447040 := by exact prefixLift 447040
  have htrace : WordTrace (prefixWord ++ tailWord_447040) baseStart_447040 baseEnd_447040 := by
    simpa [prefixWord, tailWord_447040, baseEnd_447040] using wordTrace_append hprefix tailTrace_447040
  have hstable : (prefixWord ++ tailWord_447040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447040).length < 2 ^ (prefixWord ++ tailWord_447040).sum := by decide
  have hdescent : baseEnd_447040 < baseStart_447040 := by decide
  rcases family_descends (prefixWord ++ tailWord_447040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447046 : List Nat := [6, 1, 1, 1, 2, 1, 3, 8]
def baseStart_447046 : Nat := 118140960795 + 447046 * 2 ^ 59
def prefixEnd_447046 : Nat := 4983230072969 + 3 ^ 40 * 447046 * 2
def baseEnd_447046 : Nat := 8501832321109746821077

theorem tailTrace_447046 : CollatzResearch.WordTrace tailWord_447046 prefixEnd_447046 8501832321109746821077 := by
  unfold tailWord_447046
  simp only [CollatzResearch.WordTrace]
  refine ⟨509534598076130194482031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10870071425624110815616661 509534598076130194482031)
  ·
    refine ⟨764301897114195291723047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 509534598076130194482031 764301897114195291723047)
    ·
      refine ⟨1146452845671292937584571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764301897114195291723047 1146452845671292937584571)
      ·
        refine ⟨1719679268506939406376857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146452845671292937584571 1719679268506939406376857)
        ·
          refine ⟨1289759451380204554782643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1719679268506939406376857 1289759451380204554782643)
          ·
            refine ⟨1934639177070306832173965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289759451380204554782643 1934639177070306832173965)
            ·
              refine ⟨725489691401365062065237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1934639177070306832173965 725489691401365062065237)
              ·
                refine ⟨8501832321109746821077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 725489691401365062065237 8501832321109746821077)
                ·
                  rfl

theorem cell23_447046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_447046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447046 prefixEnd_447046 := by exact prefixLift 447046
  have htrace : WordTrace (prefixWord ++ tailWord_447046) baseStart_447046 baseEnd_447046 := by
    simpa [prefixWord, tailWord_447046, baseEnd_447046] using wordTrace_append hprefix tailTrace_447046
  have hstable : (prefixWord ++ tailWord_447046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447046).length < 2 ^ (prefixWord ++ tailWord_447046).sum := by decide
  have hdescent : baseEnd_447046 < baseStart_447046 := by decide
  rcases family_descends (prefixWord ++ tailWord_447046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447074 : List Nat := [3, 3, 2, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_447074 : Nat := 118140960795 + 447074 * 2 ^ 59
def prefixEnd_447074 : Nat := 4983230072969 + 3 ^ 40 * 447074 * 2
def baseEnd_447074 : Nat := 229563850128289054618951

theorem tailTrace_447074 : CollatzResearch.WordTrace tailWord_447074 prefixEnd_447074 229563850128289054618951 := by
  unfold tailWord_447074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4076532095583681751361069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10870752254889818003629517 4076532095583681751361069)
  ·
    refine ⟨1528699535843880656760401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4076532095583681751361069 1528699535843880656760401)
    ·
      refine ⟨1146524651882910492570301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1528699535843880656760401 1146524651882910492570301)
      ·
        refine ⟨429946744456091434713863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1146524651882910492570301 429946744456091434713863)
        ·
          refine ⟨644920116684137152070795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429946744456091434713863 644920116684137152070795)
          ·
            refine ⟨967380175026205728106193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644920116684137152070795 967380175026205728106193)
            ·
              refine ⟨725535131269654296079645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967380175026205728106193 725535131269654296079645)
              ·
                refine ⟨272075674226120361029867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 725535131269654296079645 272075674226120361029867)
                ·
                  refine ⟨408113511339180541544801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272075674226120361029867 408113511339180541544801)
                  ·
                    refine ⟨306085133504385406158601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 408113511339180541544801 306085133504385406158601)
                    ·
                      refine ⟨229563850128289054618951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 306085133504385406158601 229563850128289054618951)
                      ·
                        rfl

theorem cell23_447074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_447074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447074 prefixEnd_447074 := by exact prefixLift 447074
  have htrace : WordTrace (prefixWord ++ tailWord_447074) baseStart_447074 baseEnd_447074 := by
    simpa [prefixWord, tailWord_447074, baseEnd_447074] using wordTrace_append hprefix tailTrace_447074
  have hstable : (prefixWord ++ tailWord_447074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447074).length < 2 ^ (prefixWord ++ tailWord_447074).sum := by decide
  have hdescent : baseEnd_447074 < baseStart_447074 := by decide
  rcases family_descends (prefixWord ++ tailWord_447074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447090 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_447090 : Nat := 118140960795 + 447090 * 2 ^ 59
def prefixEnd_447090 : Nat := 4983230072969 + 3 ^ 40 * 447090 * 2
def baseEnd_447090 : Nat := 229572065818760992018877

theorem tailTrace_447090 : CollatzResearch.WordTrace tailWord_447090 prefixEnd_447090 229572065818760992018877 := by
  unfold tailWord_447090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4076677987569190434506681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10871141300184507825351149 4076677987569190434506681)
  ·
    refine ⟨3057508490676892825880011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4076677987569190434506681 3057508490676892825880011)
    ·
      refine ⟨4586262736015339238820017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3057508490676892825880011 4586262736015339238820017)
      ·
        refine ⟨3439697052011504429115013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4586262736015339238820017 3439697052011504429115013)
        ·
          refine ⟨644943197252157080459065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3439697052011504429115013 644943197252157080459065)
          ·
            refine ⟨483707397939117810344299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644943197252157080459065 483707397939117810344299)
            ·
              refine ⟨725561096908676715516449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483707397939117810344299 725561096908676715516449)
              ·
                refine ⟨544170822681507536637337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725561096908676715516449 544170822681507536637337)
                ·
                  refine ⟨408128117011130652478003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544170822681507536637337 408128117011130652478003)
                  ·
                    refine ⟨612192175516695978717005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 408128117011130652478003 612192175516695978717005)
                    ·
                      refine ⟨229572065818760992018877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 612192175516695978717005 229572065818760992018877)
                      ·
                        rfl

theorem cell23_447090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_447090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447090 prefixEnd_447090 := by exact prefixLift 447090
  have htrace : WordTrace (prefixWord ++ tailWord_447090) baseStart_447090 baseEnd_447090 := by
    simpa [prefixWord, tailWord_447090, baseEnd_447090] using wordTrace_append hprefix tailTrace_447090
  have hstable : (prefixWord ++ tailWord_447090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447090).length < 2 ^ (prefixWord ++ tailWord_447090).sum := by decide
  have hdescent : baseEnd_447090 < baseStart_447090 := by decide
  rcases family_descends (prefixWord ++ tailWord_447090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447096 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 4, 2, 2]
def baseStart_447096 : Nat := 118140960795 + 447096 * 2 ^ 59
def prefixEnd_447096 : Nat := 4983230072969 + 3 ^ 40 * 447096 * 2
def baseEnd_447096 : Nat := 229575146702687968543849

theorem tailTrace_447096 : CollatzResearch.WordTrace tailWord_447096 prefixEnd_447096 229575146702687968543849 := by
  unfold tailWord_447096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8153465394127512381372571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10871287192170016508496761 8153465394127512381372571)
  ·
    refine ⟨12230198091191268572058857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8153465394127512381372571 12230198091191268572058857)
    ·
      refine ⟨9172648568393451429044143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12230198091191268572058857 9172648568393451429044143)
      ·
        refine ⟨13758972852590177143566215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9172648568393451429044143 13758972852590177143566215)
        ·
          refine ⟨20638459278885265715349323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13758972852590177143566215 20638459278885265715349323)
          ·
            refine ⟨30957688918327898573023985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20638459278885265715349323 30957688918327898573023985)
            ·
              refine ⟨23218266688745923929767989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30957688918327898573023985 23218266688745923929767989)
              ·
                refine ⟨2176712502069930368415749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23218266688745923929767989 2176712502069930368415749)
                ·
                  refine ⟨408133594138111944077953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176712502069930368415749 408133594138111944077953)
                  ·
                    refine ⟨306100195603583958058465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 408133594138111944077953 306100195603583958058465)
                    ·
                      refine ⟨229575146702687968543849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 306100195603583958058465 229575146702687968543849)
                      ·
                        rfl

theorem cell23_447096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 4, 2, 2].length) (baseStart_447096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447096 prefixEnd_447096 := by exact prefixLift 447096
  have htrace : WordTrace (prefixWord ++ tailWord_447096) baseStart_447096 baseEnd_447096 := by
    simpa [prefixWord, tailWord_447096, baseEnd_447096] using wordTrace_append hprefix tailTrace_447096
  have hstable : (prefixWord ++ tailWord_447096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447096).length < 2 ^ (prefixWord ++ tailWord_447096).sum := by decide
  have hdescent : baseEnd_447096 < baseStart_447096 := by decide
  rcases family_descends (prefixWord ++ tailWord_447096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447109 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_447109 : Nat := 118140960795 + 447109 * 2 ^ 59
def prefixEnd_447109 : Nat := 4983230072969 + 3 ^ 40 * 447109 * 2
def baseEnd_447109 : Nat := 229581821951196417681289

theorem tailTrace_447109 : CollatzResearch.WordTrace tailWord_447109 prefixEnd_447109 229581821951196417681289 := by
  unfold tailWord_447109
  simp only [CollatzResearch.WordTrace]
  refine ⟨16307404937207927982968381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10871603291471951988645587 16307404937207927982968381)
  ·
    refine ⟨6115276851452972993613143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16307404937207927982968381 6115276851452972993613143)
    ·
      refine ⟨9172915277179459490419715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6115276851452972993613143 9172915277179459490419715)
      ·
        refine ⟨13759372915769189235629573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9172915277179459490419715 13759372915769189235629573)
        ·
          refine ⟨2579882421706722981680545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13759372915769189235629573 2579882421706722981680545)
          ·
            refine ⟨1934911816280042236260409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2579882421706722981680545 1934911816280042236260409)
            ·
              refine ⟨1451183862210031677195307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1934911816280042236260409 1451183862210031677195307)
              ·
                refine ⟨2176775793315047515792961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451183862210031677195307 2176775793315047515792961)
                ·
                  refine ⟨1632581844986285636844721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2176775793315047515792961 1632581844986285636844721)
                  ·
                    refine ⟨1224436383739714227633541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1632581844986285636844721 1224436383739714227633541)
                    ·
                      refine ⟨229581821951196417681289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1224436383739714227633541 229581821951196417681289)
                      ·
                        rfl

theorem cell23_447109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_447109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447109 prefixEnd_447109 := by exact prefixLift 447109
  have htrace : WordTrace (prefixWord ++ tailWord_447109) baseStart_447109 baseEnd_447109 := by
    simpa [prefixWord, tailWord_447109, baseEnd_447109] using wordTrace_append hprefix tailTrace_447109
  have hstable : (prefixWord ++ tailWord_447109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447109).length < 2 ^ (prefixWord ++ tailWord_447109).sum := by decide
  have hdescent : baseEnd_447109 < baseStart_447109 := by decide
  rcases family_descends (prefixWord ++ tailWord_447109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447153 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 7]
def baseStart_447153 : Nat := 118140960795 + 447153 * 2 ^ 59
def prefixEnd_447153 : Nat := 4983230072969 + 3 ^ 40 * 447153 * 2
def baseEnd_447153 : Nat := 25511601677777138392343

theorem tailTrace_447153 : CollatzResearch.WordTrace tailWord_447153 prefixEnd_447153 25511601677777138392343 := by
  unfold tailWord_447153
  simp only [CollatzResearch.WordTrace]
  refine ⟨16309009749048523497570113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10872673166032348998380075 16309009749048523497570113)
  ·
    refine ⟨12231757311786392623177585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16309009749048523497570113 12231757311786392623177585)
    ·
      refine ⟨9173817983839794467383189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12231757311786392623177585 9173817983839794467383189)
      ·
        refine ⟨430022717992490365658587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9173817983839794467383189 430022717992490365658587)
        ·
          refine ⟨645034076988735548487881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430022717992490365658587 645034076988735548487881)
          ·
            refine ⟨483775557741551661365911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645034076988735548487881 483775557741551661365911)
            ·
              refine ⟨725663336612327492048867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483775557741551661365911 725663336612327492048867)
              ·
                refine ⟨1088495004918491238073301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725663336612327492048867 1088495004918491238073301)
                ·
                  refine ⟨25511601677777138392343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1088495004918491238073301 25511601677777138392343)
                  ·
                    rfl

theorem cell23_447153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 7].length) (baseStart_447153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447153 prefixEnd_447153 := by exact prefixLift 447153
  have htrace : WordTrace (prefixWord ++ tailWord_447153) baseStart_447153 baseEnd_447153 := by
    simpa [prefixWord, tailWord_447153, baseEnd_447153] using wordTrace_append hprefix tailTrace_447153
  have hstable : (prefixWord ++ tailWord_447153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447153).length < 2 ^ (prefixWord ++ tailWord_447153).sum := by decide
  have hdescent : baseEnd_447153 < baseStart_447153 := by decide
  rcases family_descends (prefixWord ++ tailWord_447153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447209 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 6]
def baseStart_447209 : Nat := 118140960795 + 447209 * 2 ^ 59
def prefixEnd_447209 : Nat := 4983230072969 + 3 ^ 40 * 447209 * 2
def baseEnd_447209 : Nat := 25514796668516225158981

theorem tailTrace_447209 : CollatzResearch.WordTrace tailWord_447209 prefixEnd_447209 25514796668516225158981 := by
  unfold tailWord_447209
  simp only [CollatzResearch.WordTrace]
  refine ⟨16311052236845645061608681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10874034824563763374405787 16311052236845645061608681)
  ·
    refine ⟨12233289177634233796206511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16311052236845645061608681 12233289177634233796206511)
    ·
      refine ⟨18349933766451350694309767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12233289177634233796206511 18349933766451350694309767)
      ·
        refine ⟨27524900649677026041464651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18349933766451350694309767 27524900649677026041464651)
        ·
          refine ⟨41287350974515539062196977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27524900649677026041464651 41287350974515539062196977)
          ·
            refine ⟨30965513230886654296647733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41287350974515539062196977 30965513230886654296647733)
            ·
              refine ⟨2903016865395623840310725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30965513230886654296647733 2903016865395623840310725)
              ·
                refine ⟨544315662261679470058261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2903016865395623840310725 544315662261679470058261)
                ·
                  refine ⟨25514796668516225158981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 544315662261679470058261 25514796668516225158981)
                  ·
                    rfl

theorem cell23_447209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 6].length) (baseStart_447209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447209 prefixEnd_447209 := by exact prefixLift 447209
  have htrace : WordTrace (prefixWord ++ tailWord_447209) baseStart_447209 baseEnd_447209 := by
    simpa [prefixWord, tailWord_447209, baseEnd_447209] using wordTrace_append hprefix tailTrace_447209
  have hstable : (prefixWord ++ tailWord_447209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447209).length < 2 ^ (prefixWord ++ tailWord_447209).sum := by decide
  have hdescent : baseEnd_447209 < baseStart_447209 := by decide
  rcases family_descends (prefixWord ++ tailWord_447209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447219 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 3]
def baseStart_447219 : Nat := 118140960795 + 447219 * 2 ^ 59
def prefixEnd_447219 : Nat := 4983230072969 + 3 ^ 40 * 447219 * 2
def baseEnd_447219 : Nat := 229638304823190987305783

theorem tailTrace_447219 : CollatzResearch.WordTrace tailWord_447219 prefixEnd_447219 229638304823190987305783 := by
  unfold tailWord_447219
  simp only [CollatzResearch.WordTrace]
  refine ⟨16311416966809416769472711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10874277977872944512981807 16311416966809416769472711)
  ·
    refine ⟨24467125450214125154209067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16311416966809416769472711 24467125450214125154209067)
    ·
      refine ⟨36700688175321187731313601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24467125450214125154209067 36700688175321187731313601)
      ·
        refine ⟨27525516131490890798485201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36700688175321187731313601 27525516131490890798485201)
        ·
          refine ⟨20644137098618168098863901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27525516131490890798485201 20644137098618168098863901)
          ·
            refine ⟨7741551411981813037073963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20644137098618168098863901 7741551411981813037073963)
            ·
              refine ⟨11612327117972719555610945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7741551411981813037073963 11612327117972719555610945)
              ·
                refine ⟨8709245338479539666708209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11612327117972719555610945 8709245338479539666708209)
                ·
                  refine ⟨6531934003859654750031157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8709245338479539666708209 6531934003859654750031157)
                  ·
                    refine ⟨612368812861842632815421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6531934003859654750031157 612368812861842632815421)
                    ·
                      refine ⟨229638304823190987305783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 612368812861842632815421 229638304823190987305783)
                      ·
                        rfl

theorem cell23_447219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 3].length) (baseStart_447219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447219 prefixEnd_447219 := by exact prefixLift 447219
  have htrace : WordTrace (prefixWord ++ tailWord_447219) baseStart_447219 baseEnd_447219 := by
    simpa [prefixWord, tailWord_447219, baseEnd_447219] using wordTrace_append hprefix tailTrace_447219
  have hstable : (prefixWord ++ tailWord_447219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447219).length < 2 ^ (prefixWord ++ tailWord_447219).sum := by decide
  have hdescent : baseEnd_447219 < baseStart_447219 := by decide
  rcases family_descends (prefixWord ++ tailWord_447219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447277 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 6]
def baseStart_447277 : Nat := 118140960795 + 447277 * 2 ^ 59
def prefixEnd_447277 : Nat := 4983230072969 + 3 ^ 40 * 447277 * 2
def baseEnd_447277 : Nat := 25518676300127973375613

theorem tailTrace_447277 : CollatzResearch.WordTrace tailWord_447277 prefixEnd_447277 25518676300127973375613 := by
  unfold tailWord_447277
  simp only [CollatzResearch.WordTrace]
  refine ⟨16313532400599292675084085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10875688267066195116722723 16313532400599292675084085)
  ·
    refine ⟨1529393662556183688289133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16313532400599292675084085 1529393662556183688289133)
    ·
      refine ⟨573522623458568883108425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1529393662556183688289133 573522623458568883108425)
      ·
        refine ⟨430141967593926662331319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573522623458568883108425 430141967593926662331319)
        ·
          refine ⟨645212951390889993496979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430141967593926662331319 645212951390889993496979)
          ·
            refine ⟨967819427086334990245469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645212951390889993496979 967819427086334990245469)
            ·
              refine ⟨362932285157375621342051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 967819427086334990245469 362932285157375621342051)
              ·
                refine ⟨544398427736063432013077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362932285157375621342051 544398427736063432013077)
                ·
                  refine ⟨25518676300127973375613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 544398427736063432013077 25518676300127973375613)
                  ·
                    rfl

theorem cell23_447277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_447277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447277 prefixEnd_447277 := by exact prefixLift 447277
  have htrace : WordTrace (prefixWord ++ tailWord_447277) baseStart_447277 baseEnd_447277 := by
    simpa [prefixWord, tailWord_447277, baseEnd_447277] using wordTrace_append hprefix tailTrace_447277
  have hstable : (prefixWord ++ tailWord_447277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447277).length < 2 ^ (prefixWord ++ tailWord_447277).sum := by decide
  have hdescent : baseEnd_447277 < baseStart_447277 := by decide
  rcases family_descends (prefixWord ++ tailWord_447277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447296 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 3]
def baseStart_447296 : Nat := 118140960795 + 447296 * 2 ^ 59
def prefixEnd_447296 : Nat := 4983230072969 + 3 ^ 40 * 447296 * 2
def baseEnd_447296 : Nat := 229677842833587186042929

theorem tailTrace_447296 : CollatzResearch.WordTrace tailWord_447296 prefixEnd_447296 229677842833587186042929 := by
  unfold tailWord_447296
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157112693765229460012871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10876150258353639280017161 8157112693765229460012871)
  ·
    refine ⟨12235669040647844190019307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8157112693765229460012871 12235669040647844190019307)
    ·
      refine ⟨18353503560971766285028961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12235669040647844190019307 18353503560971766285028961)
      ·
        refine ⟨13765127670728824713771721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18353503560971766285028961 13765127670728824713771721)
        ·
          refine ⟨10323845753046618535328791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13765127670728824713771721 10323845753046618535328791)
          ·
            refine ⟨15485768629569927802993187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10323845753046618535328791 15485768629569927802993187)
            ·
              refine ⟨23228652944354891704489781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15485768629569927802993187 23228652944354891704489781)
              ·
                refine ⟨2177686213533271097295917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23228652944354891704489781 2177686213533271097295917)
                ·
                  refine ⟨816632330074976661485969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2177686213533271097295917 816632330074976661485969)
                  ·
                    refine ⟨612474247556232496114477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 816632330074976661485969 612474247556232496114477)
                    ·
                      refine ⟨229677842833587186042929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 612474247556232496114477 229677842833587186042929)
                      ·
                        rfl

theorem cell23_447296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_447296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447296 prefixEnd_447296 := by exact prefixLift 447296
  have htrace : WordTrace (prefixWord ++ tailWord_447296) baseStart_447296 baseEnd_447296 := by
    simpa [prefixWord, tailWord_447296, baseEnd_447296] using wordTrace_append hprefix tailTrace_447296
  have hstable : (prefixWord ++ tailWord_447296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447296).length < 2 ^ (prefixWord ++ tailWord_447296).sum := by decide
  have hdescent : baseEnd_447296 < baseStart_447296 := by decide
  rcases family_descends (prefixWord ++ tailWord_447296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447299 : List Nat := [1, 1, 1, 3, 1, 4, 3, 9]
def baseStart_447299 : Nat := 118140960795 + 447299 * 2 ^ 59
def prefixEnd_447299 : Nat := 4983230072969 + 3 ^ 40 * 447299 * 2
def baseEnd_447299 : Nat := 8506643825020395344645

theorem tailTrace_447299 : CollatzResearch.WordTrace tailWord_447299 prefixEnd_447299 8506643825020395344645 := by
  unfold tailWord_447299
  simp only [CollatzResearch.WordTrace]
  refine ⟨16314334806519590432384951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10876223204346393621589967 16314334806519590432384951)
  ·
    refine ⟨24471502209779385648577427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16314334806519590432384951 24471502209779385648577427)
    ·
      refine ⟨36707253314669078472866141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24471502209779385648577427 36707253314669078472866141)
      ·
        refine ⟨13765219993000904427324803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36707253314669078472866141 13765219993000904427324803)
        ·
          refine ⟨20647829989501356640987205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13765219993000904427324803 20647829989501356640987205)
          ·
            refine ⟨3871468123031504370185101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20647829989501356640987205 3871468123031504370185101)
            ·
              refine ⟨1451800546136814138819413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3871468123031504370185101 1451800546136814138819413)
              ·
                refine ⟨8506643825020395344645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1451800546136814138819413 8506643825020395344645)
                ·
                  rfl

theorem cell23_447299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 9].length) (baseStart_447299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447299 prefixEnd_447299 := by exact prefixLift 447299
  have htrace : WordTrace (prefixWord ++ tailWord_447299) baseStart_447299 baseEnd_447299 := by
    simpa [prefixWord, tailWord_447299, baseEnd_447299] using wordTrace_append hprefix tailTrace_447299
  have hstable : (prefixWord ++ tailWord_447299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447299).length < 2 ^ (prefixWord ++ tailWord_447299).sum := by decide
  have hdescent : baseEnd_447299 < baseStart_447299 := by decide
  rcases family_descends (prefixWord ++ tailWord_447299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447313 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 5]
def baseStart_447313 : Nat := 118140960795 + 447313 * 2 ^ 59
def prefixEnd_447313 : Nat := 4983230072969 + 3 ^ 40 * 447313 * 2
def baseEnd_447313 : Nat := 229686572004713619530351

theorem tailTrace_447313 : CollatzResearch.WordTrace tailWord_447313 prefixEnd_447313 229686572004713619530351 := by
  unfold tailWord_447313
  simp only [CollatzResearch.WordTrace]
  refine ⟨16314845428468870823394593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10876563618979247215596395 16314845428468870823394593)
  ·
    refine ⟨12236134071351653117545945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16314845428468870823394593 12236134071351653117545945)
    ·
      refine ⟨9177100553513739838159459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12236134071351653117545945 9177100553513739838159459)
      ·
        refine ⟨13765650830270609757239189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9177100553513739838159459 13765650830270609757239189)
        ·
          refine ⟨645264882668934832370587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13765650830270609757239189 645264882668934832370587)
          ·
            refine ⟨967897324003402248555881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645264882668934832370587 967897324003402248555881)
            ·
              refine ⟨725922993002551686416911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967897324003402248555881 725922993002551686416911)
              ·
                refine ⟨1088884489503827529625367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725922993002551686416911 1088884489503827529625367)
                ·
                  refine ⟨1633326734255741294438051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088884489503827529625367 1633326734255741294438051)
                  ·
                    refine ⟨2449990101383611941657077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1633326734255741294438051 2449990101383611941657077)
                    ·
                      refine ⟨229686572004713619530351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2449990101383611941657077 229686572004713619530351)
                      ·
                        rfl

theorem cell23_447313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_447313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447313 prefixEnd_447313 := by exact prefixLift 447313
  have htrace : WordTrace (prefixWord ++ tailWord_447313) baseStart_447313 baseEnd_447313 := by
    simpa [prefixWord, tailWord_447313, baseEnd_447313] using wordTrace_append hprefix tailTrace_447313
  have hstable : (prefixWord ++ tailWord_447313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447313).length < 2 ^ (prefixWord ++ tailWord_447313).sum := by decide
  have hdescent : baseEnd_447313 < baseStart_447313 := by decide
  rcases family_descends (prefixWord ++ tailWord_447313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447378 : List Nat := [3, 2, 3, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_447378 : Nat := 118140960795 + 447378 * 2 ^ 59
def prefixEnd_447378 : Nat := 4983230072969 + 3 ^ 40 * 447378 * 2
def baseEnd_447378 : Nat := 229719948247255865217553

theorem tailTrace_447378 : CollatzResearch.WordTrace tailWord_447378 prefixEnd_447378 229719948247255865217553 := by
  unfold tailWord_447378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079304043308346731127697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10878144115488924616340525 4079304043308346731127697)
  ·
    refine ⟨3059478032481260048345773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4079304043308346731127697 3059478032481260048345773)
    ·
      refine ⟨1147304262180472518129665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3059478032481260048345773 1147304262180472518129665)
      ·
        refine ⟨860478196635354388597249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1147304262180472518129665 860478196635354388597249)
        ·
          refine ⟨645358647476515791447937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 860478196635354388597249 645358647476515791447937)
          ·
            refine ⟨484018985607386843585953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645358647476515791447937 484018985607386843585953)
            ·
              refine ⟨363014239205540132689465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484018985607386843585953 363014239205540132689465)
              ·
                refine ⟨272260679404155099517099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363014239205540132689465 272260679404155099517099)
                ·
                  refine ⟨408391019106232649275649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272260679404155099517099 408391019106232649275649)
                  ·
                    refine ⟨306293264329674486956737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 408391019106232649275649 306293264329674486956737)
                    ·
                      refine ⟨229719948247255865217553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 306293264329674486956737 229719948247255865217553)
                      ·
                        rfl

theorem cell23_447378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_447378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447378 prefixEnd_447378 := by exact prefixLift 447378
  have htrace : WordTrace (prefixWord ++ tailWord_447378) baseStart_447378 baseEnd_447378 := by
    simpa [prefixWord, tailWord_447378, baseEnd_447378] using wordTrace_append hprefix tailTrace_447378
  have hstable : (prefixWord ++ tailWord_447378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447378).length < 2 ^ (prefixWord ++ tailWord_447378).sum := by decide
  have hdescent : baseEnd_447378 < baseStart_447378 := by decide
  rcases family_descends (prefixWord ++ tailWord_447378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447383 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 3, 4, 2]
def baseStart_447383 : Nat := 118140960795 + 447383 * 2 ^ 59
def prefixEnd_447383 : Nat := 4983230072969 + 3 ^ 40 * 447383 * 2
def baseEnd_447383 : Nat := 229722515650528345655029

theorem tailTrace_447383 : CollatzResearch.WordTrace tailWord_447383 prefixEnd_447383 229722515650528345655029 := by
  unfold tailWord_447383
  simp only [CollatzResearch.WordTrace]
  refine ⟨16317398538215272778442803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10878265692143515185628535 16317398538215272778442803)
  ·
    refine ⟨24476097807322909167664205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16317398538215272778442803 24476097807322909167664205)
    ·
      refine ⟨9178536677746090937874077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24476097807322909167664205 9178536677746090937874077)
      ·
        refine ⟨3441951254154784101702779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9178536677746090937874077 3441951254154784101702779)
        ·
          refine ⟨5162926881232176152554169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441951254154784101702779 5162926881232176152554169)
          ·
            refine ⟨3872195160924132114415627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5162926881232176152554169 3872195160924132114415627)
            ·
              refine ⟨5808292741386198171623441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872195160924132114415627 5808292741386198171623441)
              ·
                refine ⟨4356219556039648628717581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5808292741386198171623441 4356219556039648628717581)
                ·
                  refine ⟨1633582333514868235769093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4356219556039648628717581 1633582333514868235769093)
                  ·
                    refine ⟨306296687534037794206705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1633582333514868235769093 306296687534037794206705)
                    ·
                      refine ⟨229722515650528345655029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 306296687534037794206705 229722515650528345655029)
                      ·
                        rfl

theorem cell23_447383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_447383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447383 prefixEnd_447383 := by exact prefixLift 447383
  have htrace : WordTrace (prefixWord ++ tailWord_447383) baseStart_447383 baseEnd_447383 := by
    simpa [prefixWord, tailWord_447383, baseEnd_447383] using wordTrace_append hprefix tailTrace_447383
  have hstable : (prefixWord ++ tailWord_447383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447383).length < 2 ^ (prefixWord ++ tailWord_447383).sum := by decide
  have hdescent : baseEnd_447383 < baseStart_447383 := by decide
  rcases family_descends (prefixWord ++ tailWord_447383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447393 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 2, 6]
def baseStart_447393 : Nat := 118140960795 + 447393 * 2 ^ 59
def prefixEnd_447393 : Nat := 4983230072969 + 3 ^ 40 * 447393 * 2
def baseEnd_447393 : Nat := 76575883485691102176661

theorem tailTrace_447393 : CollatzResearch.WordTrace tailWord_447393 prefixEnd_447393 76575883485691102176661 := by
  unfold tailWord_447393
  simp only [CollatzResearch.WordTrace]
  refine ⟨16317763268179044486306833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10878508845452696324204555 16317763268179044486306833)
  ·
    refine ⟨12238322451134283364730125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16317763268179044486306833 12238322451134283364730125)
    ·
      refine ⟨4589370919175356261773797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12238322451134283364730125 4589370919175356261773797)
      ·
        refine ⟨860507047345379299082587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4589370919175356261773797 860507047345379299082587)
        ·
          refine ⟨1290760571018068948623881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860507047345379299082587 1290760571018068948623881)
          ·
            refine ⟨968070428263551711467911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1290760571018068948623881 968070428263551711467911)
            ·
              refine ⟨1452105642395327567201867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968070428263551711467911 1452105642395327567201867)
              ·
                refine ⟨2178158463592991350802801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452105642395327567201867 2178158463592991350802801)
                ·
                  refine ⟨1633618847694743513102101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2178158463592991350802801 1633618847694743513102101)
                  ·
                    refine ⟨76575883485691102176661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1633618847694743513102101 76575883485691102176661)
                    ·
                      rfl

theorem cell23_447393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_447393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447393 prefixEnd_447393 := by exact prefixLift 447393
  have htrace : WordTrace (prefixWord ++ tailWord_447393) baseStart_447393 baseEnd_447393 := by
    simpa [prefixWord, tailWord_447393, baseEnd_447393] using wordTrace_append hprefix tailTrace_447393
  have hstable : (prefixWord ++ tailWord_447393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447393).length < 2 ^ (prefixWord ++ tailWord_447393).sum := by decide
  have hdescent : baseEnd_447393 < baseStart_447393 := by decide
  rcases family_descends (prefixWord ++ tailWord_447393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447421 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 1, 3, 2]
def baseStart_447421 : Nat := 118140960795 + 447421 * 2 ^ 59
def prefixEnd_447421 : Nat := 4983230072969 + 3 ^ 40 * 447421 * 2
def baseEnd_447421 : Nat := 229742027915399196979855

theorem tailTrace_447421 : CollatzResearch.WordTrace tailWord_447421 prefixEnd_447421 229742027915399196979855 := by
  unfold tailWord_447421
  simp only [CollatzResearch.WordTrace]
  refine ⟨16318784512077605268326117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10879189674718403512217411 16318784512077605268326117)
  ·
    refine ⟨3059772096014550987811147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16318784512077605268326117 3059772096014550987811147)
    ·
      refine ⟨4589658144021826481716721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059772096014550987811147 4589658144021826481716721)
      ·
        refine ⟨3442243608016369861287541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4589658144021826481716721 3442243608016369861287541)
        ·
          refine ⟨322710338251534674495707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3442243608016369861287541 322710338251534674495707)
          ·
            refine ⟨484065507377302011743561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322710338251534674495707 484065507377302011743561)
            ·
              refine ⟨363049130532976508807671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484065507377302011743561 363049130532976508807671)
              ·
                refine ⟨544573695799464763211507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363049130532976508807671 544573695799464763211507)
                ·
                  refine ⟨816860543699197144817261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544573695799464763211507 816860543699197144817261)
                  ·
                    refine ⟨306322703887198929306473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 816860543699197144817261 306322703887198929306473)
                    ·
                      refine ⟨229742027915399196979855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 306322703887198929306473 229742027915399196979855)
                      ·
                        rfl

theorem cell23_447421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_447421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447421 prefixEnd_447421 := by exact prefixLift 447421
  have htrace : WordTrace (prefixWord ++ tailWord_447421) baseStart_447421 baseEnd_447421 := by
    simpa [prefixWord, tailWord_447421, baseEnd_447421] using wordTrace_append hprefix tailTrace_447421
  have hstable : (prefixWord ++ tailWord_447421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447421).length < 2 ^ (prefixWord ++ tailWord_447421).sum := by decide
  have hdescent : baseEnd_447421 < baseStart_447421 := by decide
  rcases family_descends (prefixWord ++ tailWord_447421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447453 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_447453 : Nat := 118140960795 + 447453 * 2 ^ 59
def prefixEnd_447453 : Nat := 4983230072969 + 3 ^ 40 * 447453 * 2
def baseEnd_447453 : Nat := 76586153098781023926569

theorem tailTrace_447453 : CollatzResearch.WordTrace tailWord_447453 prefixEnd_447453 76586153098781023926569 := by
  unfold tailWord_447453
  simp only [CollatzResearch.WordTrace]
  refine ⟨16319951647961674733491013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10879967765307783155660675 16319951647961674733491013)
  ·
    refine ⟨3059990933992814012529565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16319951647961674733491013 3059990933992814012529565)
    ·
      refine ⟨1147496600247305254698587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3059990933992814012529565 1147496600247305254698587)
      ·
        refine ⟨1721244900370957882047881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147496600247305254698587 1721244900370957882047881)
        ·
          refine ⟨1290933675278218411535911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1721244900370957882047881 1290933675278218411535911)
          ·
            refine ⟨1936400512917327617303867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290933675278218411535911 1936400512917327617303867)
            ·
              refine ⟨2904600769375991425955801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936400512917327617303867 2904600769375991425955801)
              ·
                refine ⟨2178450577031993569466851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2904600769375991425955801 2178450577031993569466851)
                ·
                  refine ⟨3267675865547990354200277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178450577031993569466851 3267675865547990354200277)
                  ·
                    refine ⟨76586153098781023926569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3267675865547990354200277 76586153098781023926569)
                    ·
                      rfl

theorem cell23_447453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_447453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447453 prefixEnd_447453 := by exact prefixLift 447453
  have htrace : WordTrace (prefixWord ++ tailWord_447453) baseStart_447453 baseEnd_447453 := by
    simpa [prefixWord, tailWord_447453, baseEnd_447453] using wordTrace_append hprefix tailTrace_447453
  have hstable : (prefixWord ++ tailWord_447453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447453).length < 2 ^ (prefixWord ++ tailWord_447453).sum := by decide
  have hdescent : baseEnd_447453 < baseStart_447453 := by decide
  rcases family_descends (prefixWord ++ tailWord_447453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447473 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_447473 : Nat := 118140960795 + 447473 * 2 ^ 59
def prefixEnd_447473 : Nat := 4983230072969 + 3 ^ 40 * 447473 * 2
def baseEnd_447473 : Nat := 229768728909432993529615

theorem tailTrace_447473 : CollatzResearch.WordTrace tailWord_447473 prefixEnd_447473 229768728909432993529615 := by
  unfold tailWord_447473
  simp only [CollatzResearch.WordTrace]
  refine ⟨16320681107889218149219073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10880454071926145432812715 16320681107889218149219073)
  ·
    refine ⟨12240510830916913611914305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16320681107889218149219073 12240510830916913611914305)
    ·
      refine ⟨9180383123187685208935729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12240510830916913611914305 9180383123187685208935729)
      ·
        refine ⟨6885287342390763906701797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9180383123187685208935729 6885287342390763906701797)
        ·
          refine ⟨1290991376698268232506587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6885287342390763906701797 1290991376698268232506587)
          ·
            refine ⟨1936487065047402348759881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290991376698268232506587 1936487065047402348759881)
            ·
              refine ⟨1452365298785551761569911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1936487065047402348759881 1452365298785551761569911)
              ·
                refine ⟨2178547948178327642354867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452365298785551761569911 2178547948178327642354867)
                ·
                  refine ⟨3267821922267491463532301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178547948178327642354867 3267821922267491463532301)
                  ·
                    refine ⟨1225433220850309298824613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3267821922267491463532301 1225433220850309298824613)
                    ·
                      refine ⟨229768728909432993529615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1225433220850309298824613 229768728909432993529615)
                      ·
                        rfl

theorem cell23_447473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_447473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447473 prefixEnd_447473 := by exact prefixLift 447473
  have htrace : WordTrace (prefixWord ++ tailWord_447473) baseStart_447473 baseEnd_447473 := by
    simpa [prefixWord, tailWord_447473, baseEnd_447473] using wordTrace_append hprefix tailTrace_447473
  have hstable : (prefixWord ++ tailWord_447473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447473).length < 2 ^ (prefixWord ++ tailWord_447473).sum := by decide
  have hdescent : baseEnd_447473 < baseStart_447473 := by decide
  rcases family_descends (prefixWord ++ tailWord_447473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447474 : List Nat := [3, 2, 1, 5, 1, 2, 1, 3, 5]
def baseStart_447474 : Nat := 118140960795 + 447474 * 2 ^ 59
def prefixEnd_447474 : Nat := 4983230072969 + 3 ^ 40 * 447474 * 2
def baseEnd_447474 : Nat := 25529915821120832179679

theorem tailTrace_447474 : CollatzResearch.WordTrace tailWord_447474 prefixEnd_447474 25529915821120832179679 := by
  unfold tailWord_447474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4080179395221398830001369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10880478387257063546670317 4080179395221398830001369)
  ·
    refine ⟨3060134546416049122501027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4080179395221398830001369 3060134546416049122501027)
    ·
      refine ⟨4590201819624073683751541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3060134546416049122501027 4590201819624073683751541)
      ·
        refine ⟨430331420589756907851707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4590201819624073683751541 430331420589756907851707)
        ·
          refine ⟨645497130884635361777561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430331420589756907851707 645497130884635361777561)
          ·
            refine ⟨484122848163476521333171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645497130884635361777561 484122848163476521333171)
            ·
              refine ⟨726184272245214781999757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484122848163476521333171 726184272245214781999757)
              ·
                refine ⟨272319102091955543249909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 726184272245214781999757 272319102091955543249909)
                ·
                  refine ⟨25529915821120832179679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272319102091955543249909 25529915821120832179679)
                  ·
                    rfl

theorem cell23_447474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_447474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447474 prefixEnd_447474 := by exact prefixLift 447474
  have htrace : WordTrace (prefixWord ++ tailWord_447474) baseStart_447474 baseEnd_447474 := by
    simpa [prefixWord, tailWord_447474, baseEnd_447474] using wordTrace_append hprefix tailTrace_447474
  have hstable : (prefixWord ++ tailWord_447474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447474).length < 2 ^ (prefixWord ++ tailWord_447474).sum := by decide
  have hdescent : baseEnd_447474 < baseStart_447474 := by decide
  rcases family_descends (prefixWord ++ tailWord_447474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447500 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 3, 4]
def baseStart_447500 : Nat := 118140960795 + 447500 * 2 ^ 59
def prefixEnd_447500 : Nat := 4983230072969 + 3 ^ 40 * 447500 * 2
def baseEnd_447500 : Nat := 76594197629034795963997

theorem tailTrace_447500 : CollatzResearch.WordTrace tailWord_447500 prefixEnd_447500 76594197629034795963997 := by
  unfold tailWord_447500
  simp only [CollatzResearch.WordTrace]
  refine ⟨8160832939395700880225977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10881110585860934506967969 8160832939395700880225977)
  ·
    refine ⟨6120624704546775660169483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8160832939395700880225977 6120624704546775660169483)
    ·
      refine ⟨9180937056820163490254225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6120624704546775660169483 9180937056820163490254225)
      ·
        refine ⟨6885702792615122617690669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9180937056820163490254225 6885702792615122617690669)
        ·
          refine ⟨2582138547230670981634001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6885702792615122617690669 2582138547230670981634001)
          ·
            refine ⟨1936603910423003236225501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2582138547230670981634001 1936603910423003236225501)
            ·
              refine ⟨726226466408626213584563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1936603910423003236225501 726226466408626213584563)
              ·
                refine ⟨1089339699612939320376845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726226466408626213584563 1089339699612939320376845)
                ·
                  refine ⟨408502387354852245141317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1089339699612939320376845 408502387354852245141317)
                  ·
                    refine ⟨76594197629034795963997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 408502387354852245141317 76594197629034795963997)
                    ·
                      rfl

theorem cell23_447500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_447500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447500 prefixEnd_447500 := by exact prefixLift 447500
  have htrace : WordTrace (prefixWord ++ tailWord_447500) baseStart_447500 baseEnd_447500 := by
    simpa [prefixWord, tailWord_447500, baseEnd_447500] using wordTrace_append hprefix tailTrace_447500
  have hstable : (prefixWord ++ tailWord_447500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447500).length < 2 ^ (prefixWord ++ tailWord_447500).sum := by decide
  have hdescent : baseEnd_447500 < baseStart_447500 := by decide
  rcases family_descends (prefixWord ++ tailWord_447500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447527 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_447527 : Nat := 118140960795 + 447527 * 2 ^ 59
def prefixEnd_447527 : Nat := 4983230072969 + 3 ^ 40 * 447527 * 2
def baseEnd_447527 : Nat := 229796456864775782254367

theorem tailTrace_447527 : CollatzResearch.WordTrace tailWord_447527 prefixEnd_447527 229796456864775782254367 := by
  unfold tailWord_447527
  simp only [CollatzResearch.WordTrace]
  refine ⟨16322650649693585371684835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10881767099795723581123223 16322650649693585371684835)
  ·
    refine ⟨24483975974540378057527253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16322650649693585371684835 24483975974540378057527253)
    ·
      refine ⟨573843186903290110723295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24483975974540378057527253 573843186903290110723295)
      ·
        refine ⟨860764780354935166084943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573843186903290110723295 860764780354935166084943)
        ·
          refine ⟨1291147170532402749127415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860764780354935166084943 1291147170532402749127415)
          ·
            refine ⟨1936720755798604123691123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291147170532402749127415 1936720755798604123691123)
            ·
              refine ⟨2905081133697906185536685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936720755798604123691123 2905081133697906185536685)
              ·
                refine ⟨1089405425136714819576257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2905081133697906185536685 1089405425136714819576257)
                ·
                  refine ⟨817054068852536114682193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1089405425136714819576257 817054068852536114682193)
                  ·
                    refine ⟨612790551639402086011645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 817054068852536114682193 612790551639402086011645)
                    ·
                      refine ⟨229796456864775782254367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 612790551639402086011645 229796456864775782254367)
                      ·
                        rfl

theorem cell23_447527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_447527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447527 prefixEnd_447527 := by exact prefixLift 447527
  have htrace : WordTrace (prefixWord ++ tailWord_447527) baseStart_447527 baseEnd_447527 := by
    simpa [prefixWord, tailWord_447527, baseEnd_447527] using wordTrace_append hprefix tailTrace_447527
  have hstable : (prefixWord ++ tailWord_447527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447527).length < 2 ^ (prefixWord ++ tailWord_447527).sum := by decide
  have hdescent : baseEnd_447527 < baseStart_447527 := by decide
  rcases family_descends (prefixWord ++ tailWord_447527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447580 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_447580 : Nat := 118140960795 + 447580 * 2 ^ 59
def prefixEnd_447580 : Nat := 4983230072969 + 3 ^ 40 * 447580 * 2
def baseEnd_447580 : Nat := 229823671339464074891623

theorem tailTrace_447580 : CollatzResearch.WordTrace tailWord_447580 prefixEnd_447580 229823671339464074891623 := by
  unfold tailWord_447580
  simp only [CollatzResearch.WordTrace]
  refine ⟨8162291859250787711682097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10883055812334383615576129 8162291859250787711682097)
  ·
    refine ⟨6121718894438090783761573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8162291859250787711682097 6121718894438090783761573)
    ·
      refine ⟨1147822292707142021955295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6121718894438090783761573 1147822292707142021955295)
      ·
        refine ⟨1721733439060713032932943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147822292707142021955295 1721733439060713032932943)
        ·
          refine ⟨2582600158591069549399415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721733439060713032932943 2582600158591069549399415)
          ·
            refine ⟨3873900237886604324099123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582600158591069549399415 3873900237886604324099123)
            ·
              refine ⟨5810850356829906486148685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873900237886604324099123 5810850356829906486148685)
              ·
                refine ⟨2179068883811214932305757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5810850356829906486148685 2179068883811214932305757)
                ·
                  refine ⟨817150831429205599614659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2179068883811214932305757 817150831429205599614659)
                  ·
                    refine ⟨1225726247143808399421989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 817150831429205599614659 1225726247143808399421989)
                    ·
                      refine ⟨229823671339464074891623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1225726247143808399421989 229823671339464074891623)
                      ·
                        rfl

theorem cell23_447580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_447580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447580 prefixEnd_447580 := by exact prefixLift 447580
  have htrace : WordTrace (prefixWord ++ tailWord_447580) baseStart_447580 baseEnd_447580 := by
    simpa [prefixWord, tailWord_447580, baseEnd_447580] using wordTrace_append hprefix tailTrace_447580
  have hstable : (prefixWord ++ tailWord_447580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447580).length < 2 ^ (prefixWord ++ tailWord_447580).sum := by decide
  have hdescent : baseEnd_447580 < baseStart_447580 := by decide
  rcases family_descends (prefixWord ++ tailWord_447580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447594 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 1, 5]
def baseStart_447594 : Nat := 118140960795 + 447594 * 2 ^ 59
def prefixEnd_447594 : Nat := 4983230072969 + 3 ^ 40 * 447594 * 2
def baseEnd_447594 : Nat := 76610286689542340038853

theorem tailTrace_447594 : CollatzResearch.WordTrace tailWord_447594 prefixEnd_447594 76610286689542340038853 := by
  unfold tailWord_447594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4081273585112713953593459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10883396226967237209582557 4081273585112713953593459)
  ·
    refine ⟨6121910377669070930390189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4081273585112713953593459 6121910377669070930390189)
    ·
      refine ⟨2295716391625901598896321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6121910377669070930390189 2295716391625901598896321)
      ·
        refine ⟨1721787293719426199172241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2295716391625901598896321 1721787293719426199172241)
        ·
          refine ⟨1291340470289569649379181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1721787293719426199172241 1291340470289569649379181)
          ·
            refine ⟨484252676358588618517193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1291340470289569649379181 484252676358588618517193)
            ·
              refine ⟨363189507268941463887895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484252676358588618517193 363189507268941463887895)
              ·
                refine ⟨544784260903412195831843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363189507268941463887895 544784260903412195831843)
                ·
                  refine ⟨817176391355118293747765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544784260903412195831843 817176391355118293747765)
                  ·
                    refine ⟨76610286689542340038853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 817176391355118293747765 76610286689542340038853)
                    ·
                      rfl

theorem cell23_447594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_447594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447594 prefixEnd_447594 := by exact prefixLift 447594
  have htrace : WordTrace (prefixWord ++ tailWord_447594) baseStart_447594 baseEnd_447594 := by
    simpa [prefixWord, tailWord_447594, baseEnd_447594] using wordTrace_append hprefix tailTrace_447594
  have hstable : (prefixWord ++ tailWord_447594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447594).length < 2 ^ (prefixWord ++ tailWord_447594).sum := by decide
  have hdescent : baseEnd_447594 < baseStart_447594 := by decide
  rcases family_descends (prefixWord ++ tailWord_447594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447597 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_447597 : Nat := 118140960795 + 447597 * 2 ^ 59
def prefixEnd_447597 : Nat := 4983230072969 + 3 ^ 40 * 447597 * 2
def baseEnd_447597 : Nat := 229832400510590508379045

theorem tailTrace_447597 : CollatzResearch.WordTrace tailWord_447597 prefixEnd_447597 229832400510590508379045 := by
  unfold tailWord_447597
  simp only [CollatzResearch.WordTrace]
  refine ⟨16325203759439987326733045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10883469172959991551155363 16325203759439987326733045)
  ·
    refine ⟨1530487852447498811881223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16325203759439987326733045 1530487852447498811881223)
    ·
      refine ⟨2295731778671248217821835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530487852447498811881223 2295731778671248217821835)
      ·
        refine ⟨3443597668006872326732753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295731778671248217821835 3443597668006872326732753)
        ·
          refine ⟨2582698251005154245049565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3443597668006872326732753 2582698251005154245049565)
          ·
            refine ⟨968511844126932841893587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2582698251005154245049565 968511844126932841893587)
            ·
              refine ⟨1452767766190399262840381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968511844126932841893587 1452767766190399262840381)
              ·
                refine ⟨544787912321399723565143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1452767766190399262840381 544787912321399723565143)
                ·
                  refine ⟨817181868482099585347715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544787912321399723565143 817181868482099585347715)
                  ·
                    refine ⟨1225772802723149378021573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 817181868482099585347715 1225772802723149378021573)
                    ·
                      refine ⟨229832400510590508379045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1225772802723149378021573 229832400510590508379045)
                      ·
                        rfl

theorem cell23_447597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_447597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447597 prefixEnd_447597 := by exact prefixLift 447597
  have htrace : WordTrace (prefixWord ++ tailWord_447597) baseStart_447597 baseEnd_447597 := by
    simpa [prefixWord, tailWord_447597, baseEnd_447597] using wordTrace_append hprefix tailTrace_447597
  have hstable : (prefixWord ++ tailWord_447597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447597).length < 2 ^ (prefixWord ++ tailWord_447597).sum := by decide
  have hdescent : baseEnd_447597 < baseStart_447597 := by decide
  rcases family_descends (prefixWord ++ tailWord_447597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447624 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 1, 6]
def baseStart_447624 : Nat := 118140960795 + 447624 * 2 ^ 59
def prefixEnd_447624 : Nat := 4983230072969 + 3 ^ 40 * 447624 * 2
def baseEnd_447624 : Nat := 76615421496087300913807

theorem tailTrace_447624 : CollatzResearch.WordTrace tailWord_447624 prefixEnd_447624 76615421496087300913807 := by
  unfold tailWord_447624
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163094265171085468982963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10884125686894780625310617 8163094265171085468982963)
  ·
    refine ⟨12244641397756628203474445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8163094265171085468982963 12244641397756628203474445)
    ·
      refine ⟨4591740524158735576302917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12244641397756628203474445 4591740524158735576302917)
      ·
        refine ⟨860951348279762920556797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4591740524158735576302917 860951348279762920556797)
        ·
          refine ⟨322856755604911095208799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 860951348279762920556797 322856755604911095208799)
          ·
            refine ⟨484285133407366642813199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322856755604911095208799 484285133407366642813199)
            ·
              refine ⟨726427700111049964219799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484285133407366642813199 726427700111049964219799)
              ·
                refine ⟨1089641550166574946329699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726427700111049964219799 1089641550166574946329699)
                ·
                  refine ⟨1634462325249862419494549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089641550166574946329699 1634462325249862419494549)
                  ·
                    refine ⟨76615421496087300913807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1634462325249862419494549 76615421496087300913807)
                    ·
                      rfl

theorem cell23_447624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_447624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447624 prefixEnd_447624 := by exact prefixLift 447624
  have htrace : WordTrace (prefixWord ++ tailWord_447624) baseStart_447624 baseEnd_447624 := by
    simpa [prefixWord, tailWord_447624, baseEnd_447624] using wordTrace_append hprefix tailTrace_447624
  have hstable : (prefixWord ++ tailWord_447624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447624).length < 2 ^ (prefixWord ++ tailWord_447624).sum := by decide
  have hdescent : baseEnd_447624 < baseStart_447624 := by decide
  rcases family_descends (prefixWord ++ tailWord_447624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447634 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_447634 : Nat := 118140960795 + 447634 * 2 ^ 59
def prefixEnd_447634 : Nat := 4983230072969 + 3 ^ 40 * 447634 * 2
def baseEnd_447634 : Nat := 229851399294806863616375

theorem tailTrace_447634 : CollatzResearch.WordTrace tailWord_447634 prefixEnd_447634 229851399294806863616375 := by
  unfold tailWord_447634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4081638315076485661457489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10884368840203961763886637 4081638315076485661457489)
  ·
    refine ⟨3061228736307364246093117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4081638315076485661457489 3061228736307364246093117)
    ·
      refine ⟨1147960776115261592284919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3061228736307364246093117 1147960776115261592284919)
      ·
        refine ⟨1721941164172892388427379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147960776115261592284919 1721941164172892388427379)
        ·
          refine ⟨2582911746259338582641069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721941164172892388427379 2582911746259338582641069)
          ·
            refine ⟨968591904847251968490401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2582911746259338582641069 968591904847251968490401)
            ·
              refine ⟨726443928635438976367801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968591904847251968490401 726443928635438976367801)
              ·
                refine ⟨544832946476579232275851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726443928635438976367801 544832946476579232275851)
                ·
                  refine ⟨817249419714868848413777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544832946476579232275851 817249419714868848413777)
                  ·
                    refine ⟨612937064786151636310333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 817249419714868848413777 612937064786151636310333)
                    ·
                      refine ⟨229851399294806863616375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 612937064786151636310333 229851399294806863616375)
                      ·
                        rfl

theorem cell23_447634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_447634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447634 prefixEnd_447634 := by exact prefixLift 447634
  have htrace : WordTrace (prefixWord ++ tailWord_447634) baseStart_447634 baseEnd_447634 := by
    simpa [prefixWord, tailWord_447634, baseEnd_447634] using wordTrace_append hprefix tailTrace_447634
  have hstable : (prefixWord ++ tailWord_447634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447634).length < 2 ^ (prefixWord ++ tailWord_447634).sum := by decide
  have hdescent : baseEnd_447634 < baseStart_447634 := by decide
  rcases family_descends (prefixWord ++ tailWord_447634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447663 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 4, 6]
def baseStart_447663 : Nat := 118140960795 + 447663 * 2 ^ 59
def prefixEnd_447663 : Nat := 4983230072969 + 3 ^ 40 * 447663 * 2
def baseEnd_447663 : Nat := 76622096744595750051247

theorem tailTrace_447663 : CollatzResearch.WordTrace tailWord_447663 prefixEnd_447663 76622096744595750051247 := by
  unfold tailWord_447663
  simp only [CollatzResearch.WordTrace]
  refine ⟨16327610977200880598635643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10885073984800587065757095 16327610977200880598635643)
  ·
    refine ⟨24491416465801320897953465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16327610977200880598635643 24491416465801320897953465)
    ·
      refine ⟨18368562349350990673465099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24491416465801320897953465 18368562349350990673465099)
      ·
        refine ⟨27552843524026486010197649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18368562349350990673465099 27552843524026486010197649)
        ·
          refine ⟨20664632643019864507648237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27552843524026486010197649 20664632643019864507648237)
          ·
            refine ⟨7749237241132449190368089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20664632643019864507648237 7749237241132449190368089)
            ·
              refine ⟨5811927930849336892776067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7749237241132449190368089 5811927930849336892776067)
              ·
                refine ⟨8717891896274005339164101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811927930849336892776067 8717891896274005339164101)
                ·
                  refine ⟨1634604730551376001093269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8717891896274005339164101 1634604730551376001093269)
                  ·
                    refine ⟨76622096744595750051247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1634604730551376001093269 76622096744595750051247)
                    ·
                      rfl

theorem cell23_447663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_447663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447663 prefixEnd_447663 := by exact prefixLift 447663
  have htrace : WordTrace (prefixWord ++ tailWord_447663) baseStart_447663 baseEnd_447663 := by
    simpa [prefixWord, tailWord_447663, baseEnd_447663] using wordTrace_append hprefix tailTrace_447663
  have hstable : (prefixWord ++ tailWord_447663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447663).length < 2 ^ (prefixWord ++ tailWord_447663).sum := by decide
  have hdescent : baseEnd_447663 < baseStart_447663 := by decide
  rcases family_descends (prefixWord ++ tailWord_447663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447681 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_447681 : Nat := 118140960795 + 447681 * 2 ^ 59
def prefixEnd_447681 : Nat := 4983230072969 + 3 ^ 40 * 447681 * 2
def baseEnd_447681 : Nat := 229875532885568179728659

theorem tailTrace_447681 : CollatzResearch.WordTrace tailWord_447681 prefixEnd_447681 229875532885568179728659 := by
  unfold tailWord_447681
  simp only [CollatzResearch.WordTrace]
  refine ⟨16328267491135669672790897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10885511660757113115193931 16328267491135669672790897)
  ·
    refine ⟨12246200618351752254593173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16328267491135669672790897 12246200618351752254593173)
    ·
      refine ⟨574040653985238386934055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12246200618351752254593173 574040653985238386934055)
      ·
        refine ⟨861060980977857580401083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574040653985238386934055 861060980977857580401083)
        ·
          refine ⟨1291591471466786370601625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861060980977857580401083 1291591471466786370601625)
          ·
            refine ⟨968693603600089777951219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291591471466786370601625 968693603600089777951219)
            ·
              refine ⟨1453040405400134666926829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968693603600089777951219 1453040405400134666926829)
              ·
                refine ⟨544890152025050500097561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1453040405400134666926829 544890152025050500097561)
                ·
                  refine ⟨408667614018787875073171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 544890152025050500097561 408667614018787875073171)
                  ·
                    refine ⟨613001421028181812609757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 408667614018787875073171 613001421028181812609757)
                    ·
                      refine ⟨229875532885568179728659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 613001421028181812609757 229875532885568179728659)
                      ·
                        rfl

theorem cell23_447681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_447681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447681 prefixEnd_447681 := by exact prefixLift 447681
  have htrace : WordTrace (prefixWord ++ tailWord_447681) baseStart_447681 baseEnd_447681 := by
    simpa [prefixWord, tailWord_447681, baseEnd_447681] using wordTrace_append hprefix tailTrace_447681
  have hstable : (prefixWord ++ tailWord_447681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447681).length < 2 ^ (prefixWord ++ tailWord_447681).sum := by decide
  have hdescent : baseEnd_447681 < baseStart_447681 := by decide
  rcases family_descends (prefixWord ++ tailWord_447681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447690 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_447690 : Nat := 118140960795 + 447690 * 2 ^ 59
def prefixEnd_447690 : Nat := 4983230072969 + 3 ^ 40 * 447690 * 2
def baseEnd_447690 : Nat := 229880154211458644516117

theorem tailTrace_447690 : CollatzResearch.WordTrace tailWord_447690 prefixEnd_447690 229880154211458644516117 := by
  unfold tailWord_447690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4082148937025766052467131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10885730498735376139912349 4082148937025766052467131)
  ·
    refine ⟨6123223405538649078700697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4082148937025766052467131 6123223405538649078700697)
    ·
      refine ⟨4592417554153986809025523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6123223405538649078700697 4592417554153986809025523)
      ·
        refine ⟨6888626331230980213538285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4592417554153986809025523 6888626331230980213538285)
        ·
          refine ⟨2583234874211617580076857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6888626331230980213538285 2583234874211617580076857)
          ·
            refine ⟨1937426155658713185057643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2583234874211617580076857 1937426155658713185057643)
            ·
              refine ⟨2906139233488069777586465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937426155658713185057643 2906139233488069777586465)
              ·
                refine ⟨2179604425116052333189849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2906139233488069777586465 2179604425116052333189849)
                ·
                  refine ⟨1634703318837039249892387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2179604425116052333189849 1634703318837039249892387)
                  ·
                    refine ⟨2452054978255558874838581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1634703318837039249892387 2452054978255558874838581)
                    ·
                      refine ⟨229880154211458644516117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2452054978255558874838581 229880154211458644516117)
                      ·
                        rfl

theorem cell23_447690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_447690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447690 prefixEnd_447690 := by exact prefixLift 447690
  have htrace : WordTrace (prefixWord ++ tailWord_447690) baseStart_447690 baseEnd_447690 := by
    simpa [prefixWord, tailWord_447690, baseEnd_447690] using wordTrace_append hprefix tailTrace_447690
  have hstable : (prefixWord ++ tailWord_447690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447690).length < 2 ^ (prefixWord ++ tailWord_447690).sum := by decide
  have hdescent : baseEnd_447690 < baseStart_447690 := by decide
  rcases family_descends (prefixWord ++ tailWord_447690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447704 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 1, 4, 2]
def baseStart_447704 : Nat := 118140960795 + 447704 * 2 ^ 59
def prefixEnd_447704 : Nat := 4983230072969 + 3 ^ 40 * 447704 * 2
def baseEnd_447704 : Nat := 229887342940621589741053

theorem tailTrace_447704 : CollatzResearch.WordTrace tailWord_447704 prefixEnd_447704 229887342940621589741053 := by
  unfold tailWord_447704
  simp only [CollatzResearch.WordTrace]
  refine ⟨8164553185026172300439083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10886070913368229733918777 8164553185026172300439083)
  ·
    refine ⟨12246829777539258450658625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8164553185026172300439083 12246829777539258450658625)
    ·
      refine ⟨9185122333154443837993969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12246829777539258450658625 9185122333154443837993969)
      ·
        refine ⟨6888841749865832878495477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9185122333154443837993969 6888841749865832878495477)
        ·
          refine ⟨645828914049921832358951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6888841749865832878495477 645828914049921832358951)
          ·
            refine ⟨968743371074882748538427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645828914049921832358951 968743371074882748538427)
            ·
              refine ⟨1453115056612324122807641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968743371074882748538427 1453115056612324122807641)
              ·
                refine ⟨1089836292459243092105731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1453115056612324122807641 1089836292459243092105731)
                ·
                  refine ⟨1634754438688864638158597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089836292459243092105731 1634754438688864638158597)
                  ·
                    refine ⟨306516457254162119654737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1634754438688864638158597 306516457254162119654737)
                    ·
                      refine ⟨229887342940621589741053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 306516457254162119654737 229887342940621589741053)
                      ·
                        rfl

theorem cell23_447704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_447704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447704 prefixEnd_447704 := by exact prefixLift 447704
  have htrace : WordTrace (prefixWord ++ tailWord_447704) baseStart_447704 baseEnd_447704 := by
    simpa [prefixWord, tailWord_447704, baseEnd_447704] using wordTrace_append hprefix tailTrace_447704
  have hstable : (prefixWord ++ tailWord_447704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447704).length < 2 ^ (prefixWord ++ tailWord_447704).sum := by decide
  have hdescent : baseEnd_447704 < baseStart_447704 := by decide
  rcases family_descends (prefixWord ++ tailWord_447704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447794 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2]
def baseStart_447794 : Nat := 118140960795 + 447794 * 2 ^ 59
def prefixEnd_447794 : Nat := 4983230072969 + 3 ^ 40 * 447794 * 2
def baseEnd_447794 : Nat := 229933556199526237615639

theorem tailTrace_447794 : CollatzResearch.WordTrace tailWord_447794 prefixEnd_447794 229933556199526237615639 := by
  unfold tailWord_447794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4083097234931572492913609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10888259293150859981102957 4083097234931572492913609)
  ·
    refine ⟨3062322926198679369685207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4083097234931572492913609 3062322926198679369685207)
    ·
      refine ⟨4593484389298019054527811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3062322926198679369685207 4593484389298019054527811)
      ·
        refine ⟨6890226583947028581791717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4593484389298019054527811 6890226583947028581791717)
        ·
          refine ⟨1291917484490067859085947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6890226583947028581791717 1291917484490067859085947)
          ·
            refine ⟨1937876226735101788628921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291917484490067859085947 1937876226735101788628921)
            ·
              refine ⟨1453407170051326341471691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1937876226735101788628921 1453407170051326341471691)
              ·
                refine ⟨2180110755076989512207537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453407170051326341471691 2180110755076989512207537)
                ·
                  refine ⟨1635083066307742134155653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180110755076989512207537 1635083066307742134155653)
                  ·
                    refine ⟨306578074932701650154185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1635083066307742134155653 306578074932701650154185)
                    ·
                      refine ⟨229933556199526237615639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 306578074932701650154185 229933556199526237615639)
                      ·
                        rfl

theorem cell23_447794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_447794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447794 prefixEnd_447794 := by exact prefixLift 447794
  have htrace : WordTrace (prefixWord ++ tailWord_447794) baseStart_447794 baseEnd_447794 := by
    simpa [prefixWord, tailWord_447794, baseEnd_447794] using wordTrace_append hprefix tailTrace_447794
  have hstable : (prefixWord ++ tailWord_447794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447794).length < 2 ^ (prefixWord ++ tailWord_447794).sum := by decide
  have hdescent : baseEnd_447794 < baseStart_447794 := by decide
  rcases family_descends (prefixWord ++ tailWord_447794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447797 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_447797 : Nat := 118140960795 + 447797 * 2 ^ 59
def prefixEnd_447797 : Nat := 4983230072969 + 3 ^ 40 * 447797 * 2
def baseEnd_447797 : Nat := 229935096641489725878125

theorem tailTrace_447797 : CollatzResearch.WordTrace tailWord_447797 prefixEnd_447797 229935096641489725878125 := by
  unfold tailWord_447797
  simp only [CollatzResearch.WordTrace]
  refine ⟨16332498358715421484013645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10888332239143614322675763 16332498358715421484013645)
  ·
    refine ⟨6124686884518283056505117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16332498358715421484013645 6124686884518283056505117)
    ·
      refine ⟨2296757581694356146189419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6124686884518283056505117 2296757581694356146189419)
      ·
        refine ⟨3445136372541534219284129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296757581694356146189419 3445136372541534219284129)
        ·
          refine ⟨2583852279406150664463097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3445136372541534219284129 2583852279406150664463097)
          ·
            refine ⟨1937889209554612998347323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2583852279406150664463097 1937889209554612998347323)
            ·
              refine ⟨2906833814331919497520985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937889209554612998347323 2906833814331919497520985)
              ·
                refine ⟨2180125360748939623140739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2906833814331919497520985 2180125360748939623140739)
                ·
                  refine ⟨3270188041123409434711109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180125360748939623140739 3270188041123409434711109)
                  ·
                    refine ⟨613160257710639269008333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3270188041123409434711109 613160257710639269008333)
                    ·
                      refine ⟨229935096641489725878125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 613160257710639269008333 229935096641489725878125)
                      ·
                        rfl

theorem cell23_447797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_447797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447797 prefixEnd_447797 := by exact prefixLift 447797
  have htrace : WordTrace (prefixWord ++ tailWord_447797) baseStart_447797 baseEnd_447797 := by
    simpa [prefixWord, tailWord_447797, baseEnd_447797] using wordTrace_append hprefix tailTrace_447797
  have hstable : (prefixWord ++ tailWord_447797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447797).length < 2 ^ (prefixWord ++ tailWord_447797).sum := by decide
  have hdescent : baseEnd_447797 < baseStart_447797 := by decide
  rcases family_descends (prefixWord ++ tailWord_447797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447867 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 4]
def baseStart_447867 : Nat := 118140960795 + 447867 * 2 ^ 59
def prefixEnd_447867 : Nat := 4983230072969 + 3 ^ 40 * 447867 * 2
def baseEnd_447867 : Nat := 229971040287304452002803

theorem tailTrace_447867 : CollatzResearch.WordTrace tailWord_447867 prefixEnd_447867 229971040287304452002803 := by
  unfold tailWord_447867
  simp only [CollatzResearch.WordTrace]
  refine ⟨16335051468461823439061855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10890034312307882292707903 16335051468461823439061855)
  ·
    refine ⟨24502577202692735158592783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16335051468461823439061855 24502577202692735158592783)
    ·
      refine ⟨36753865804039102737889175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24502577202692735158592783 36753865804039102737889175)
      ·
        refine ⟨55130798706058654106833763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36753865804039102737889175 55130798706058654106833763)
        ·
          refine ⟨82696198059087981160250645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55130798706058654106833763 82696198059087981160250645)
          ·
            refine ⟨3876384284019749116886749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82696198059087981160250645 3876384284019749116886749)
            ·
              refine ⟨1453644106507405918832531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3876384284019749116886749 1453644106507405918832531)
              ·
                refine ⟨2180466159761108878248797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453644106507405918832531 2180466159761108878248797)
                ·
                  refine ⟨817674809910415829343299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2180466159761108878248797 817674809910415829343299)
                  ·
                    refine ⟨1226512214865623744014949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 817674809910415829343299 1226512214865623744014949)
                    ·
                      refine ⟨229971040287304452002803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1226512214865623744014949 229971040287304452002803)
                      ·
                        rfl

theorem cell23_447867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 1, 4].length) (baseStart_447867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447867 prefixEnd_447867 := by exact prefixLift 447867
  have htrace : WordTrace (prefixWord ++ tailWord_447867) baseStart_447867 baseEnd_447867 := by
    simpa [prefixWord, tailWord_447867, baseEnd_447867] using wordTrace_append hprefix tailTrace_447867
  have hstable : (prefixWord ++ tailWord_447867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447867).length < 2 ^ (prefixWord ++ tailWord_447867).sum := by decide
  have hdescent : baseEnd_447867 < baseStart_447867 := by decide
  rcases family_descends (prefixWord ++ tailWord_447867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447877 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 6, 4]
def baseStart_447877 : Nat := 118140960795 + 447877 * 2 ^ 59
def prefixEnd_447877 : Nat := 4983230072969 + 3 ^ 40 * 447877 * 2
def baseEnd_447877 : Nat := 76658725031283137625919

theorem tailTrace_447877 : CollatzResearch.WordTrace tailWord_447877 prefixEnd_447877 76658725031283137625919 := by
  unfold tailWord_447877
  simp only [CollatzResearch.WordTrace]
  refine ⟨16335416198425595146925885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10890277465617063431283923 16335416198425595146925885)
  ·
    refine ⟨6125781074409598180097207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16335416198425595146925885 6125781074409598180097207)
    ·
      refine ⟨9188671611614397270145811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6125781074409598180097207 9188671611614397270145811)
      ·
        refine ⟨13783007417421595905218717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9188671611614397270145811 13783007417421595905218717)
        ·
          refine ⟨5168627781533098464457019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13783007417421595905218717 5168627781533098464457019)
          ·
            refine ⟨7752941672299647696685529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5168627781533098464457019 7752941672299647696685529)
            ·
              refine ⟨5814706254224735772514147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7752941672299647696685529 5814706254224735772514147)
              ·
                refine ⟨8722059381337103658771221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5814706254224735772514147 8722059381337103658771221)
                ·
                  refine ⟨408846533500176734004901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8722059381337103658771221 408846533500176734004901)
                  ·
                    refine ⟨76658725031283137625919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 408846533500176734004901 76658725031283137625919)
                    ·
                      rfl

theorem cell23_447877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_447877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447877 prefixEnd_447877 := by exact prefixLift 447877
  have htrace : WordTrace (prefixWord ++ tailWord_447877) baseStart_447877 baseEnd_447877 := by
    simpa [prefixWord, tailWord_447877, baseEnd_447877] using wordTrace_append hprefix tailTrace_447877
  have hstable : (prefixWord ++ tailWord_447877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447877).length < 2 ^ (prefixWord ++ tailWord_447877).sum := by decide
  have hdescent : baseEnd_447877 < baseStart_447877 := by decide
  rcases family_descends (prefixWord ++ tailWord_447877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447881 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 1, 5]
def baseStart_447881 : Nat := 118140960795 + 447881 * 2 ^ 59
def prefixEnd_447881 : Nat := 4983230072969 + 3 ^ 40 * 447881 * 2
def baseEnd_447881 : Nat := 76659409672155799075913

theorem tailTrace_447881 : CollatzResearch.WordTrace tailWord_447881 prefixEnd_447881 76659409672155799075913 := by
  unfold tailWord_447881
  simp only [CollatzResearch.WordTrace]
  refine ⟨16335562090411103830071497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10890374726940735886714331 16335562090411103830071497)
  ·
    refine ⟨12251671567808327872553623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16335562090411103830071497 12251671567808327872553623)
    ·
      refine ⟨18377507351712491808830435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12251671567808327872553623 18377507351712491808830435)
      ·
        refine ⟨27566261027568737713245653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18377507351712491808830435 27566261027568737713245653)
        ·
          refine ⟨646084242833642290154195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27566261027568737713245653 646084242833642290154195)
          ·
            refine ⟨969126364250463435231293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646084242833642290154195 969126364250463435231293)
            ·
              refine ⟨363422386593923788211735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 969126364250463435231293 363422386593923788211735)
              ·
                refine ⟨545133579890885682317603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363422386593923788211735 545133579890885682317603)
                ·
                  refine ⟨817700369836328523476405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545133579890885682317603 817700369836328523476405)
                  ·
                    refine ⟨76659409672155799075913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 817700369836328523476405 76659409672155799075913)
                    ·
                      rfl

theorem cell23_447881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 5].length) (baseStart_447881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447881 prefixEnd_447881 := by exact prefixLift 447881
  have htrace : WordTrace (prefixWord ++ tailWord_447881) baseStart_447881 baseEnd_447881 := by
    simpa [prefixWord, tailWord_447881, baseEnd_447881] using wordTrace_append hprefix tailTrace_447881
  have hstable : (prefixWord ++ tailWord_447881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447881).length < 2 ^ (prefixWord ++ tailWord_447881).sum := by decide
  have hdescent : baseEnd_447881 < baseStart_447881 := by decide
  rcases family_descends (prefixWord ++ tailWord_447881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447951 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 2, 1, 3]
def baseStart_447951 : Nat := 118140960795 + 447951 * 2 ^ 59
def prefixEnd_447951 : Nat := 4983230072969 + 3 ^ 40 * 447951 * 2
def baseEnd_447951 : Nat := 230014172662282123352417

theorem tailTrace_447951 : CollatzResearch.WordTrace tailWord_447951 prefixEnd_447951 230014172662282123352417 := by
  unfold tailWord_447951
  simp only [CollatzResearch.WordTrace]
  refine ⟨16338115200157505785119707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10892076800105003856746471 16338115200157505785119707)
  ·
    refine ⟨24507172800236258677679561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16338115200157505785119707 24507172800236258677679561)
    ·
      refine ⟨18380379600177194008259671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24507172800236258677679561 18380379600177194008259671)
      ·
        refine ⟨27570569400265791012389507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18380379600177194008259671 27570569400265791012389507)
        ·
          refine ⟨41355854100398686518584261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27570569400265791012389507 41355854100398686518584261)
          ·
            refine ⟨7754222643824753722234549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41355854100398686518584261 7754222643824753722234549)
            ·
              refine ⟨726958372858570661459489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7754222643824753722234549 726958372858570661459489)
              ·
                refine ⟨545218779643927996094617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726958372858570661459489 545218779643927996094617)
                ·
                  refine ⟨408914084732945997070963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545218779643927996094617 408914084732945997070963)
                  ·
                    refine ⟨613371127099418995606445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 408914084732945997070963 613371127099418995606445)
                    ·
                      refine ⟨230014172662282123352417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 613371127099418995606445 230014172662282123352417)
                      ·
                        rfl

theorem cell23_447951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 1, 3].length) (baseStart_447951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447951 prefixEnd_447951 := by exact prefixLift 447951
  have htrace : WordTrace (prefixWord ++ tailWord_447951) baseStart_447951 baseEnd_447951 := by
    simpa [prefixWord, tailWord_447951, baseEnd_447951] using wordTrace_append hprefix tailTrace_447951
  have hstable : (prefixWord ++ tailWord_447951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447951).length < 2 ^ (prefixWord ++ tailWord_447951).sum := by decide
  have hdescent : baseEnd_447951 < baseStart_447951 := by decide
  rcases family_descends (prefixWord ++ tailWord_447951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447967 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 2, 6]
def baseStart_447967 : Nat := 118140960795 + 447967 * 2 ^ 59
def prefixEnd_447967 : Nat := 4983230072969 + 3 ^ 40 * 447967 * 2
def baseEnd_447967 : Nat := 76674129450918020250781

theorem tailTrace_447967 : CollatzResearch.WordTrace tailWord_447967 prefixEnd_447967 76674129450918020250781 := by
  unfold tailWord_447967
  simp only [CollatzResearch.WordTrace]
  refine ⟨16338698768099540517702155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10892465845399693678468103 16338698768099540517702155)
  ·
    refine ⟨24508048152149310776553233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16338698768099540517702155 24508048152149310776553233)
    ·
      refine ⟨18381036114111983082414925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24508048152149310776553233 18381036114111983082414925)
      ·
        refine ⟨6892888542791993655905597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18381036114111983082414925 6892888542791993655905597)
        ·
          refine ⟨2584833203546997620964599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6892888542791993655905597 2584833203546997620964599)
          ·
            refine ⟨3877249805320496431446899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584833203546997620964599 3877249805320496431446899)
            ·
              refine ⟨5815874707980744647170349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3877249805320496431446899 5815874707980744647170349)
              ·
                refine ⟨2180953015492779242688881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5815874707980744647170349 2180953015492779242688881)
                ·
                  refine ⟨1635714761619584432016661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180953015492779242688881 1635714761619584432016661)
                  ·
                    refine ⟨76674129450918020250781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1635714761619584432016661 76674129450918020250781)
                    ·
                      rfl

theorem cell23_447967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_447967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447967 prefixEnd_447967 := by exact prefixLift 447967
  have htrace : WordTrace (prefixWord ++ tailWord_447967) baseStart_447967 baseEnd_447967 := by
    simpa [prefixWord, tailWord_447967, baseEnd_447967] using wordTrace_append hprefix tailTrace_447967
  have hstable : (prefixWord ++ tailWord_447967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447967).length < 2 ^ (prefixWord ++ tailWord_447967).sum := by decide
  have hdescent : baseEnd_447967 < baseStart_447967 := by decide
  rcases family_descends (prefixWord ++ tailWord_447967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447977 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 3, 6, 3]
def baseStart_447977 : Nat := 118140960795 + 447977 * 2 ^ 59
def prefixEnd_447977 : Nat := 4983230072969 + 3 ^ 40 * 447977 * 2
def baseEnd_447977 : Nat := 230027523159299021627297

theorem tailTrace_447977 : CollatzResearch.WordTrace tailWord_447977 prefixEnd_447977 230027523159299021627297 := by
  unfold tailWord_447977
  simp only [CollatzResearch.WordTrace]
  refine ⟨16339063498063312225566185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10892708998708874817044123 16339063498063312225566185)
  ·
    refine ⟨12254297623547484169174639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16339063498063312225566185 12254297623547484169174639)
    ·
      refine ⟨18381446435321226253761959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12254297623547484169174639 18381446435321226253761959)
      ·
        refine ⟨27572169652981839380642939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18381446435321226253761959 27572169652981839380642939)
        ·
          refine ⟨41358254479472759070964409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27572169652981839380642939 41358254479472759070964409)
          ·
            refine ⟨31018690859604569303223307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41358254479472759070964409 31018690859604569303223307)
            ·
              refine ⟨46528036289406853954834961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31018690859604569303223307 46528036289406853954834961)
              ·
                refine ⟨34896027217055140466126221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46528036289406853954834961 34896027217055140466126221)
                ·
                  refine ⟨13086010206395677674797333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34896027217055140466126221 13086010206395677674797333)
                  ·
                    refine ⟨613406728424797391006125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13086010206395677674797333 613406728424797391006125)
                    ·
                      refine ⟨230027523159299021627297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 613406728424797391006125 230027523159299021627297)
                      ·
                        rfl

theorem cell23_447977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 6, 3].length) (baseStart_447977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447977 prefixEnd_447977 := by exact prefixLift 447977
  have htrace : WordTrace (prefixWord ++ tailWord_447977) baseStart_447977 baseEnd_447977 := by
    simpa [prefixWord, tailWord_447977, baseEnd_447977] using wordTrace_append hprefix tailTrace_447977
  have hstable : (prefixWord ++ tailWord_447977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447977).length < 2 ^ (prefixWord ++ tailWord_447977).sum := by decide
  have hdescent : baseEnd_447977 < baseStart_447977 := by decide
  rcases family_descends (prefixWord ++ tailWord_447977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447987 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 4]
def baseStart_447987 : Nat := 118140960795 + 447987 * 2 ^ 59
def prefixEnd_447987 : Nat := 4983230072969 + 3 ^ 40 * 447987 * 2
def baseEnd_447987 : Nat := 230032657965843982502251

theorem tailTrace_447987 : CollatzResearch.WordTrace tailWord_447987 prefixEnd_447987 230032657965843982502251 := by
  unfold tailWord_447987
  simp only [CollatzResearch.WordTrace]
  refine ⟨16339428228027083933430215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10892952152018055955620143 16339428228027083933430215)
  ·
    refine ⟨24509142342040625900145323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16339428228027083933430215 24509142342040625900145323)
    ·
      refine ⟨36763713513060938850217985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24509142342040625900145323 36763713513060938850217985)
      ·
        refine ⟨27572785134795704137663489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36763713513060938850217985 27572785134795704137663489)
        ·
          refine ⟨20679588851096778103247617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27572785134795704137663489 20679588851096778103247617)
          ·
            refine ⟨15509691638322583577435713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20679588851096778103247617 15509691638322583577435713)
            ·
              refine ⟨11632268728741937683076785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15509691638322583577435713 11632268728741937683076785)
              ·
                refine ⟨8724201546556453262307589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11632268728741937683076785 8724201546556453262307589)
                ·
                  refine ⟨1635787789979334986682673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8724201546556453262307589 1635787789979334986682673)
                  ·
                    refine ⟨1226840842484501240012005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1635787789979334986682673 1226840842484501240012005)
                    ·
                      refine ⟨230032657965843982502251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1226840842484501240012005 230032657965843982502251)
                      ·
                        rfl

theorem cell23_447987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_447987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_447987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_447987 prefixEnd_447987 := by exact prefixLift 447987
  have htrace : WordTrace (prefixWord ++ tailWord_447987) baseStart_447987 baseEnd_447987 := by
    simpa [prefixWord, tailWord_447987, baseEnd_447987] using wordTrace_append hprefix tailTrace_447987
  have hstable : (prefixWord ++ tailWord_447987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447987).length < 2 ^ (prefixWord ++ tailWord_447987).sum := by decide
  have hdescent : baseEnd_447987 < baseStart_447987 := by decide
  rcases family_descends (prefixWord ++ tailWord_447987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448037 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_448037 : Nat := 118140960795 + 448037 * 2 ^ 59
def prefixEnd_448037 : Nat := 4983230072969 + 3 ^ 40 * 448037 * 2
def baseEnd_448037 : Nat := 230058331998568786877021

theorem tailTrace_448037 : CollatzResearch.WordTrace tailWord_448037 prefixEnd_448037 230058331998568786877021 := by
  unfold tailWord_448037
  simp only [CollatzResearch.WordTrace]
  refine ⟨16341251877845942472750365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10894167918563961648500243 16341251877845942472750365)
  ·
    refine ⟨6127969454192228427281387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16341251877845942472750365 6127969454192228427281387)
    ·
      refine ⟨9191954181288342640922081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6127969454192228427281387 9191954181288342640922081)
      ·
        refine ⟨6893965635966256980691561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9191954181288342640922081 6893965635966256980691561)
        ·
          refine ⟨5170474226974692735518671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6893965635966256980691561 5170474226974692735518671)
          ·
            refine ⟨7755711340462039103278007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5170474226974692735518671 7755711340462039103278007)
            ·
              refine ⟨11633567010693058654917011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7755711340462039103278007 11633567010693058654917011)
              ·
                refine ⟨17450350516039587982375517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11633567010693058654917011 17450350516039587982375517)
                ·
                  refine ⟨6543881443514845493390819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17450350516039587982375517 6543881443514845493390819)
                  ·
                    refine ⟨9815822165272268240086229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6543881443514845493390819 9815822165272268240086229)
                    ·
                      refine ⟨230058331998568786877021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9815822165272268240086229 230058331998568786877021)
                      ·
                        rfl

theorem cell23_448037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_448037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448037 prefixEnd_448037 := by exact prefixLift 448037
  have htrace : WordTrace (prefixWord ++ tailWord_448037) baseStart_448037 baseEnd_448037 := by
    simpa [prefixWord, tailWord_448037, baseEnd_448037] using wordTrace_append hprefix tailTrace_448037
  have hstable : (prefixWord ++ tailWord_448037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448037).length < 2 ^ (prefixWord ++ tailWord_448037).sum := by decide
  have hdescent : baseEnd_448037 < baseStart_448037 := by decide
  rcases family_descends (prefixWord ++ tailWord_448037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448081 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 2, 4, 2]
def baseStart_448081 : Nat := 118140960795 + 448081 * 2 ^ 59
def prefixEnd_448081 : Nat := 4983230072969 + 3 ^ 40 * 448081 * 2
def baseEnd_448081 : Nat := 230080925147366614726819

theorem tailTrace_448081 : CollatzResearch.WordTrace tailWord_448081 prefixEnd_448081 230080925147366614726819 := by
  unfold tailWord_448081
  simp only [CollatzResearch.WordTrace]
  refine ⟨16342856689686537987352097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10895237793124358658234731 16342856689686537987352097)
  ·
    refine ⟨12257142517264903490514073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16342856689686537987352097 12257142517264903490514073)
    ·
      refine ⟨9192856887948677617885555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12257142517264903490514073 9192856887948677617885555)
      ·
        refine ⟨13789285331923016426828333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9192856887948677617885555 13789285331923016426828333)
        ·
          refine ⟨5170981999471131160060625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13789285331923016426828333 5170981999471131160060625)
          ·
            refine ⟨3878236499603348370045469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5170981999471131160060625 3878236499603348370045469)
            ·
              refine ⟨1454338687351255638767051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3878236499603348370045469 1454338687351255638767051)
              ·
                refine ⟨2181508031026883458150577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454338687351255638767051 2181508031026883458150577)
                ·
                  refine ⟨1636131023270162593612933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2181508031026883458150577 1636131023270162593612933)
                  ·
                    refine ⟨306774566863155486302425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1636131023270162593612933 306774566863155486302425)
                    ·
                      refine ⟨230080925147366614726819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 306774566863155486302425 230080925147366614726819)
                      ·
                        rfl

theorem cell23_448081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 4, 2].length) (baseStart_448081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448081 prefixEnd_448081 := by exact prefixLift 448081
  have htrace : WordTrace (prefixWord ++ tailWord_448081) baseStart_448081 baseEnd_448081 := by
    simpa [prefixWord, tailWord_448081, baseEnd_448081] using wordTrace_append hprefix tailTrace_448081
  have hstable : (prefixWord ++ tailWord_448081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448081).length < 2 ^ (prefixWord ++ tailWord_448081).sum := by decide
  have hdescent : baseEnd_448081 < baseStart_448081 := by decide
  rcases family_descends (prefixWord ++ tailWord_448081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448101 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 1, 4, 3]
def baseStart_448101 : Nat := 118140960795 + 448101 * 2 ^ 59
def prefixEnd_448101 : Nat := 4983230072969 + 3 ^ 40 * 448101 * 2
def baseEnd_448101 : Nat := 230091194760456536476727

theorem tailTrace_448101 : CollatzResearch.WordTrace tailWord_448101 prefixEnd_448101 230091194760456536476727 := by
  unfold tailWord_448101
  simp only [CollatzResearch.WordTrace]
  refine ⟨16343586149614081403080157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10895724099742720935386771 16343586149614081403080157)
  ·
    refine ⟨6128844806105280526155059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16343586149614081403080157 6128844806105280526155059)
    ·
      refine ⟨9193267209157920789232589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6128844806105280526155059 9193267209157920789232589)
      ·
        refine ⟨3447475203434220295962221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9193267209157920789232589 3447475203434220295962221)
        ·
          refine ⟨1292803201287832610985833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3447475203434220295962221 1292803201287832610985833)
          ·
            refine ⟨969602400965874458239375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1292803201287832610985833 969602400965874458239375)
            ·
              refine ⟨1454403601448811687359063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969602400965874458239375 1454403601448811687359063)
              ·
                refine ⟨2181605402173217531038595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454403601448811687359063 2181605402173217531038595)
                ·
                  refine ⟨3272408103259826296557893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181605402173217531038595 3272408103259826296557893)
                  ·
                    refine ⟨613576519361217430604605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3272408103259826296557893 613576519361217430604605)
                    ·
                      refine ⟨230091194760456536476727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 613576519361217430604605 230091194760456536476727)
                      ·
                        rfl

theorem cell23_448101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_448101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448101 prefixEnd_448101 := by exact prefixLift 448101
  have htrace : WordTrace (prefixWord ++ tailWord_448101) baseStart_448101 baseEnd_448101 := by
    simpa [prefixWord, tailWord_448101, baseEnd_448101] using wordTrace_append hprefix tailTrace_448101
  have hstable : (prefixWord ++ tailWord_448101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448101).length < 2 ^ (prefixWord ++ tailWord_448101).sum := by decide
  have hdescent : baseEnd_448101 < baseStart_448101 := by decide
  rcases family_descends (prefixWord ++ tailWord_448101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448138 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 6]
def baseStart_448138 : Nat := 118140960795 + 448138 * 2 ^ 59
def prefixEnd_448138 : Nat := 4983230072969 + 3 ^ 40 * 448138 * 2
def baseEnd_448138 : Nat := 25567799282741432412673

theorem tailTrace_448138 : CollatzResearch.WordTrace tailWord_448138 prefixEnd_448138 25567799282741432412673 := by
  unfold tailWord_448138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4086233912620009180544267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10896623766986691148118045 4086233912620009180544267)
  ·
    refine ⟨6129350868930013770816401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4086233912620009180544267 6129350868930013770816401)
    ·
      refine ⟨4597013151697510328112301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6129350868930013770816401 4597013151697510328112301)
      ·
        refine ⟨1723879931886566373042113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4597013151697510328112301 1723879931886566373042113)
        ·
          refine ⟨1292909948914924779781585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1723879931886566373042113 1292909948914924779781585)
          ·
            refine ⟨969682461686193584836189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1292909948914924779781585 969682461686193584836189)
            ·
              refine ⟨363630923132322594313571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 969682461686193584836189 363630923132322594313571)
              ·
                refine ⟨545446384698483891470357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363630923132322594313571 545446384698483891470357)
                ·
                  refine ⟨25567799282741432412673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 545446384698483891470357 25567799282741432412673)
                  ·
                    rfl

theorem cell23_448138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_448138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448138 prefixEnd_448138 := by exact prefixLift 448138
  have htrace : WordTrace (prefixWord ++ tailWord_448138) baseStart_448138 baseEnd_448138 := by
    simpa [prefixWord, tailWord_448138, baseEnd_448138] using wordTrace_append hprefix tailTrace_448138
  have hstable : (prefixWord ++ tailWord_448138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448138).length < 2 ^ (prefixWord ++ tailWord_448138).sum := by decide
  have hdescent : baseEnd_448138 < baseStart_448138 := by decide
  rcases family_descends (prefixWord ++ tailWord_448138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448151 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 1, 5]
def baseStart_448151 : Nat := 118140960795 + 448151 * 2 ^ 59
def prefixEnd_448151 : Nat := 4983230072969 + 3 ^ 40 * 448151 * 2
def baseEnd_448151 : Nat := 76705622931060446950499

theorem tailTrace_448151 : CollatzResearch.WordTrace tailWord_448151 prefixEnd_448151 76705622931060446950499 := by
  unfold tailWord_448151
  simp only [CollatzResearch.WordTrace]
  refine ⟨16345409799432939942400307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10896939866288626628266871 16345409799432939942400307)
  ·
    refine ⟨24518114699149409913600461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16345409799432939942400307 24518114699149409913600461)
    ·
      refine ⟨9194293012181028717600173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24518114699149409913600461 9194293012181028717600173)
      ·
        refine ⟨3447859879567885769100065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9194293012181028717600173 3447859879567885769100065)
        ·
          refine ⟨2585894909675914326825049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3447859879567885769100065 2585894909675914326825049)
          ·
            refine ⟨1939421182256935745118787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2585894909675914326825049 1939421182256935745118787)
            ·
              refine ⟨2909131773385403617678181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939421182256935745118787 2909131773385403617678181)
              ·
                refine ⟨545462207509763178314659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2909131773385403617678181 545462207509763178314659)
                ·
                  refine ⟨818193311264644767471989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545462207509763178314659 818193311264644767471989)
                  ·
                    refine ⟨76705622931060446950499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 818193311264644767471989 76705622931060446950499)
                    ·
                      rfl

theorem cell23_448151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_448151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448151 prefixEnd_448151 := by exact prefixLift 448151
  have htrace : WordTrace (prefixWord ++ tailWord_448151) baseStart_448151 baseEnd_448151 := by
    simpa [prefixWord, tailWord_448151, baseEnd_448151] using wordTrace_append hprefix tailTrace_448151
  have hstable : (prefixWord ++ tailWord_448151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448151).length < 2 ^ (prefixWord ++ tailWord_448151).sum := by decide
  have hdescent : baseEnd_448151 < baseStart_448151 := by decide
  rcases family_descends (prefixWord ++ tailWord_448151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448159 : List Nat := [1, 1, 2, 7, 2, 1, 1, 3, 1, 4]
def baseStart_448159 : Nat := 118140960795 + 448159 * 2 ^ 59
def prefixEnd_448159 : Nat := 4983230072969 + 3 ^ 40 * 448159 * 2
def baseEnd_448159 : Nat := 76706992212805769850487

theorem tailTrace_448159 : CollatzResearch.WordTrace tailWord_448159 prefixEnd_448159 76706992212805769850487 := by
  unfold tailWord_448159
  simp only [CollatzResearch.WordTrace]
  refine ⟨16345701583403957308691531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10897134388935971539127687 16345701583403957308691531)
  ·
    refine ⟨24518552375105935963037297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16345701583403957308691531 24518552375105935963037297)
    ·
      refine ⟨18388914281329451972277973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24518552375105935963037297 18388914281329451972277973)
      ·
        refine ⟨430990178468659030600265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18388914281329451972277973 430990178468659030600265)
        ·
          refine ⟨323242633851494272950199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430990178468659030600265 323242633851494272950199)
          ·
            refine ⟨484863950777241409425299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323242633851494272950199 484863950777241409425299)
            ·
              refine ⟨727295926165862114137949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484863950777241409425299 727295926165862114137949)
              ·
                refine ⟨272735972312198292801731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 727295926165862114137949 272735972312198292801731)
                ·
                  refine ⟨409103958468297439202597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272735972312198292801731 409103958468297439202597)
                  ·
                    refine ⟨76706992212805769850487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 409103958468297439202597 76706992212805769850487)
                    ·
                      rfl

theorem cell23_448159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 1, 4].length) (baseStart_448159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448159 prefixEnd_448159 := by exact prefixLift 448159
  have htrace : WordTrace (prefixWord ++ tailWord_448159) baseStart_448159 baseEnd_448159 := by
    simpa [prefixWord, tailWord_448159, baseEnd_448159] using wordTrace_append hprefix tailTrace_448159
  have hstable : (prefixWord ++ tailWord_448159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448159).length < 2 ^ (prefixWord ++ tailWord_448159).sum := by decide
  have hdescent : baseEnd_448159 < baseStart_448159 := by decide
  rcases family_descends (prefixWord ++ tailWord_448159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448165 : List Nat := [1, 3, 1, 2, 1, 2, 5, 3, 1, 1, 3]
def baseStart_448165 : Nat := 118140960795 + 448165 * 2 ^ 59
def prefixEnd_448165 : Nat := 4983230072969 + 3 ^ 40 * 448165 * 2
def baseEnd_448165 : Nat := 230124057522344286076433

theorem tailTrace_448165 : CollatzResearch.WordTrace tailWord_448165 prefixEnd_448165 230124057522344286076433 := by
  unfold tailWord_448165
  simp only [CollatzResearch.WordTrace]
  refine ⟨16345920421382220333409949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10897280280921480222273299 16345920421382220333409949)
  ·
    refine ⟨6129720158018332625028731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16345920421382220333409949 6129720158018332625028731)
    ·
      refine ⟨9194580237027498937543097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6129720158018332625028731 9194580237027498937543097)
      ·
        refine ⟨6895935177770624203157323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9194580237027498937543097 6895935177770624203157323)
        ·
          refine ⟨10343902766655936304735985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895935177770624203157323 10343902766655936304735985)
          ·
            refine ⟨7757927074991952228551989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10343902766655936304735985 7757927074991952228551989)
            ·
              refine ⟨727305663280495521426749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7757927074991952228551989 727305663280495521426749)
              ·
                refine ⟨272739623730185820535031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 727305663280495521426749 272739623730185820535031)
                ·
                  refine ⟨409109435595278730802547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272739623730185820535031 409109435595278730802547)
                  ·
                    refine ⟨613664153392918096203821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 409109435595278730802547 613664153392918096203821)
                    ·
                      refine ⟨230124057522344286076433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 613664153392918096203821 230124057522344286076433)
                      ·
                        rfl

theorem cell23_448165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_448165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448165 prefixEnd_448165 := by exact prefixLift 448165
  have htrace : WordTrace (prefixWord ++ tailWord_448165) baseStart_448165 baseEnd_448165 := by
    simpa [prefixWord, tailWord_448165, baseEnd_448165] using wordTrace_append hprefix tailTrace_448165
  have hstable : (prefixWord ++ tailWord_448165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448165).length < 2 ^ (prefixWord ++ tailWord_448165).sum := by decide
  have hdescent : baseEnd_448165 < baseStart_448165 := by decide
  rcases family_descends (prefixWord ++ tailWord_448165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448182 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_448182 : Nat := 118140960795 + 448182 * 2 ^ 59
def prefixEnd_448182 : Nat := 4983230072969 + 3 ^ 40 * 448182 * 2
def baseEnd_448182 : Nat := 230132786693470719563855

theorem tailTrace_448182 : CollatzResearch.WordTrace tailWord_448182 prefixEnd_448182 230132786693470719563855 := by
  unfold tailWord_448182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1021658778895039514798675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10897693641547088157852533 1021658778895039514798675)
  ·
    refine ⟨1532488168342559272198013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1021658778895039514798675 1532488168342559272198013)
    ·
      refine ⟨574683063128459727074255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1532488168342559272198013 574683063128459727074255)
      ·
        refine ⟨862024594692689590611383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574683063128459727074255 862024594692689590611383)
        ·
          refine ⟨1293036892039034385917075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862024594692689590611383 1293036892039034385917075)
          ·
            refine ⟨1939555338058551578875613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293036892039034385917075 1939555338058551578875613)
            ·
              refine ⟨727333251771956842078355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1939555338058551578875613 727333251771956842078355)
              ·
                refine ⟨1090999877657935263117533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727333251771956842078355 1090999877657935263117533)
                ·
                  refine ⟨409124954121725723669075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1090999877657935263117533 409124954121725723669075)
                  ·
                    refine ⟨613687431182588585503613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 409124954121725723669075 613687431182588585503613)
                    ·
                      refine ⟨230132786693470719563855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 613687431182588585503613 230132786693470719563855)
                      ·
                        rfl

theorem cell23_448182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_448182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448182 prefixEnd_448182 := by exact prefixLift 448182
  have htrace : WordTrace (prefixWord ++ tailWord_448182) baseStart_448182 baseEnd_448182 := by
    simpa [prefixWord, tailWord_448182, baseEnd_448182] using wordTrace_append hprefix tailTrace_448182
  have hstable : (prefixWord ++ tailWord_448182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448182).length < 2 ^ (prefixWord ++ tailWord_448182).sum := by decide
  have hdescent : baseEnd_448182 < baseStart_448182 := by decide
  rcases family_descends (prefixWord ++ tailWord_448182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448191 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 3]
def baseStart_448191 : Nat := 118140960795 + 448191 * 2 ^ 59
def prefixEnd_448191 : Nat := 4983230072969 + 3 ^ 40 * 448191 * 2
def baseEnd_448191 : Nat := 230137408019361184351313

theorem tailTrace_448191 : CollatzResearch.WordTrace tailWord_448191 prefixEnd_448191 230137408019361184351313 := by
  unfold tailWord_448191
  simp only [CollatzResearch.WordTrace]
  refine ⟨16346868719288026773856427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10897912479525351182570951 16346868719288026773856427)
  ·
    refine ⟨24520303078932040160784641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16346868719288026773856427 24520303078932040160784641)
    ·
      refine ⟨18390227309199030120588481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24520303078932040160784641 18390227309199030120588481)
      ·
        refine ⟨13792670481899272590441361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18390227309199030120588481 13792670481899272590441361)
        ·
          refine ⟨10344502861424454442831021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13792670481899272590441361 10344502861424454442831021)
          ·
            refine ⟨3879188573034170416061633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10344502861424454442831021 3879188573034170416061633)
            ·
              refine ⟨2909391429775627812046225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3879188573034170416061633 2909391429775627812046225)
              ·
                refine ⟨2182043572331720859034669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2909391429775627812046225 2182043572331720859034669)
                ·
                  refine ⟨818266339624395322138001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2182043572331720859034669 818266339624395322138001)
                  ·
                    refine ⟨613699754718296491603501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 818266339624395322138001 613699754718296491603501)
                    ·
                      refine ⟨230137408019361184351313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 613699754718296491603501 230137408019361184351313)
                      ·
                        rfl

theorem cell23_448191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_448191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448191 prefixEnd_448191 := by exact prefixLift 448191
  have htrace : WordTrace (prefixWord ++ tailWord_448191) baseStart_448191 baseEnd_448191 := by
    simpa [prefixWord, tailWord_448191, baseEnd_448191] using wordTrace_append hprefix tailTrace_448191
  have hstable : (prefixWord ++ tailWord_448191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448191).length < 2 ^ (prefixWord ++ tailWord_448191).sum := by decide
  have hdescent : baseEnd_448191 < baseStart_448191 := by decide
  rcases family_descends (prefixWord ++ tailWord_448191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448205 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_448205 : Nat := 118140960795 + 448205 * 2 ^ 59
def prefixEnd_448205 : Nat := 4983230072969 + 3 ^ 40 * 448205 * 2
def baseEnd_448205 : Nat := 230144596748524129576249

theorem tailTrace_448205 : CollatzResearch.WordTrace tailWord_448205 prefixEnd_448205 230144596748524129576249 := by
  unfold tailWord_448205
  simp only [CollatzResearch.WordTrace]
  refine ⟨16347379341237307164866069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10898252894158204776577379 16347379341237307164866069)
  ·
    refine ⟨766283406620498773353097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16347379341237307164866069 766283406620498773353097)
    ·
      refine ⟨574712554965374080014823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 766283406620498773353097 574712554965374080014823)
      ·
        refine ⟨862068832448061120022235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574712554965374080014823 862068832448061120022235)
        ·
          refine ⟨1293103248672091680033353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862068832448061120022235 1293103248672091680033353)
          ·
            refine ⟨969827436504068760025015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1293103248672091680033353 969827436504068760025015)
            ·
              refine ⟨1454741154756103140037523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969827436504068760025015 1454741154756103140037523)
              ·
                refine ⟨2182111732134154710056285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454741154756103140037523 2182111732134154710056285)
                ·
                  refine ⟨818291899550308016271107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2182111732134154710056285 818291899550308016271107)
                  ·
                    refine ⟨1227437849325462024406661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 818291899550308016271107 1227437849325462024406661)
                    ·
                      refine ⟨230144596748524129576249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1227437849325462024406661 230144596748524129576249)
                      ·
                        rfl

theorem cell23_448205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_448205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448205 prefixEnd_448205 := by exact prefixLift 448205
  have htrace : WordTrace (prefixWord ++ tailWord_448205) baseStart_448205 baseEnd_448205 := by
    simpa [prefixWord, tailWord_448205, baseEnd_448205] using wordTrace_append hprefix tailTrace_448205
  have hstable : (prefixWord ++ tailWord_448205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448205).length < 2 ^ (prefixWord ++ tailWord_448205).sum := by decide
  have hdescent : baseEnd_448205 < baseStart_448205 := by decide
  rcases family_descends (prefixWord ++ tailWord_448205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448225 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 1, 1, 5]
def baseStart_448225 : Nat := 118140960795 + 448225 * 2 ^ 59
def prefixEnd_448225 : Nat := 4983230072969 + 3 ^ 40 * 448225 * 2
def baseEnd_448225 : Nat := 230154866361614051326157

theorem tailTrace_448225 : CollatzResearch.WordTrace tailWord_448225 prefixEnd_448225 230154866361614051326157 := by
  unfold tailWord_448225
  simp only [CollatzResearch.WordTrace]
  refine ⟨16348108801164850580594129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10898739200776567053729419 16348108801164850580594129)
  ·
    refine ⟨12261081600873637935445597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16348108801164850580594129 12261081600873637935445597)
    ·
      refine ⟨4597905600327614225792099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12261081600873637935445597 4597905600327614225792099)
      ·
        refine ⟨6896858400491421338688149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4597905600327614225792099 6896858400491421338688149)
        ·
          refine ⟨323290237523035375251007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6896858400491421338688149 323290237523035375251007)
          ·
            refine ⟨484935356284553062876511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323290237523035375251007 484935356284553062876511)
            ·
              refine ⟨727403034426829594314767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484935356284553062876511 727403034426829594314767)
              ·
                refine ⟨1091104551640244391472151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727403034426829594314767 1091104551640244391472151)
                ·
                  refine ⟨1636656827460366587208227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091104551640244391472151 1636656827460366587208227)
                  ·
                    refine ⟨2454985241190549880812341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1636656827460366587208227 2454985241190549880812341)
                    ·
                      refine ⟨230154866361614051326157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2454985241190549880812341 230154866361614051326157)
                      ·
                        rfl

theorem cell23_448225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_448225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448225 prefixEnd_448225 := by exact prefixLift 448225
  have htrace : WordTrace (prefixWord ++ tailWord_448225) baseStart_448225 baseEnd_448225 := by
    simpa [prefixWord, tailWord_448225, baseEnd_448225] using wordTrace_append hprefix tailTrace_448225
  have hstable : (prefixWord ++ tailWord_448225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448225).length < 2 ^ (prefixWord ++ tailWord_448225).sum := by decide
  have hdescent : baseEnd_448225 < baseStart_448225 := by decide
  rcases family_descends (prefixWord ++ tailWord_448225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448282 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2]
def baseStart_448282 : Nat := 118140960795 + 448282 * 2 ^ 59
def prefixEnd_448282 : Nat := 4983230072969 + 3 ^ 40 * 448282 * 2
def baseEnd_448282 : Nat := 230184134758920328313395

theorem tailTrace_448282 : CollatzResearch.WordTrace tailWord_448282 prefixEnd_448282 230184134758920328313395 := by
  unfold tailWord_448282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4087546940489587328854775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10900125174638899543612733 4087546940489587328854775)
  ·
    refine ⟨6131320410734380993282163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4087546940489587328854775 6131320410734380993282163)
    ·
      refine ⟨9196980616101571489923245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6131320410734380993282163 9196980616101571489923245)
      ·
        refine ⟨3448867731038089308721217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9196980616101571489923245 3448867731038089308721217)
        ·
          refine ⟨2586650798278566981540913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3448867731038089308721217 2586650798278566981540913)
          ·
            refine ⟨1939988098708925236155685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2586650798278566981540913 1939988098708925236155685)
            ·
              refine ⟨363747768507923481779191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1939988098708925236155685 363747768507923481779191)
              ·
                refine ⟨545621652761885222668787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363747768507923481779191 545621652761885222668787)
                ·
                  refine ⟨818432479142827834003181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545621652761885222668787 818432479142827834003181)
                  ·
                    refine ⟨306912179678560437751193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 818432479142827834003181 306912179678560437751193)
                    ·
                      refine ⟨230184134758920328313395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 306912179678560437751193 230184134758920328313395)
                      ·
                        rfl

theorem cell23_448282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_448282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448282 prefixEnd_448282 := by exact prefixLift 448282
  have htrace : WordTrace (prefixWord ++ tailWord_448282) baseStart_448282 baseEnd_448282 := by
    simpa [prefixWord, tailWord_448282, baseEnd_448282] using wordTrace_append hprefix tailTrace_448282
  have hstable : (prefixWord ++ tailWord_448282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448282).length < 2 ^ (prefixWord ++ tailWord_448282).sum := by decide
  have hdescent : baseEnd_448282 < baseStart_448282 := by decide
  rcases family_descends (prefixWord ++ tailWord_448282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448291 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 4]
def baseStart_448291 : Nat := 118140960795 + 448291 * 2 ^ 59
def prefixEnd_448291 : Nat := 4983230072969 + 3 ^ 40 * 448291 * 2
def baseEnd_448291 : Nat := 230188756084810793100853

theorem tailTrace_448291 : CollatzResearch.WordTrace tailWord_448291 prefixEnd_448291 230188756084810793100853 := by
  unfold tailWord_448291
  simp only [CollatzResearch.WordTrace]
  refine ⟨16350516018925743852496727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10900344012617162568331151 16350516018925743852496727)
  ·
    refine ⟨24525774028388615778745091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16350516018925743852496727 24525774028388615778745091)
    ·
      refine ⟨36788661042582923668117637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24525774028388615778745091 36788661042582923668117637)
      ·
        refine ⟨6897873945484298187772057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36788661042582923668117637 6897873945484298187772057)
        ·
          refine ⟨5173405459113223640829043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6897873945484298187772057 5173405459113223640829043)
          ·
            refine ⟨7760108188669835461243565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173405459113223640829043 7760108188669835461243565)
            ·
              refine ⟨2910040570751188297966337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7760108188669835461243565 2910040570751188297966337)
              ·
                refine ⟨2182530428063391223474753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2910040570751188297966337 2182530428063391223474753)
                ·
                  refine ⟨1636897821047543417606065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2182530428063391223474753 1636897821047543417606065)
                  ·
                    refine ⟨1227673365785657563204549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1636897821047543417606065 1227673365785657563204549)
                    ·
                      refine ⟨230188756084810793100853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1227673365785657563204549 230188756084810793100853)
                      ·
                        rfl

theorem cell23_448291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_448291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448291 prefixEnd_448291 := by exact prefixLift 448291
  have htrace : WordTrace (prefixWord ++ tailWord_448291) baseStart_448291 baseEnd_448291 := by
    simpa [prefixWord, tailWord_448291, baseEnd_448291] using wordTrace_append hprefix tailTrace_448291
  have hstable : (prefixWord ++ tailWord_448291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448291).length < 2 ^ (prefixWord ++ tailWord_448291).sum := by decide
  have hdescent : baseEnd_448291 < baseStart_448291 := by decide
  rcases family_descends (prefixWord ++ tailWord_448291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448311 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 3]
def baseStart_448311 : Nat := 118140960795 + 448311 * 2 ^ 59
def prefixEnd_448311 : Nat := 4983230072969 + 3 ^ 40 * 448311 * 2
def baseEnd_448311 : Nat := 230199025697900714850761

theorem tailTrace_448311 : CollatzResearch.WordTrace tailWord_448311 prefixEnd_448311 230199025697900714850761 := by
  unfold tailWord_448311
  simp only [CollatzResearch.WordTrace]
  refine ⟨16351245478853287268224787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10900830319235524845483191 16351245478853287268224787)
  ·
    refine ⟨24526868218279930902337181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16351245478853287268224787 24526868218279930902337181)
    ·
      refine ⟨9197575581854974088376443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24526868218279930902337181 9197575581854974088376443)
      ·
        refine ⟨13796363372782461132564665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9197575581854974088376443 13796363372782461132564665)
        ·
          refine ⟨10347272529586845849423499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13796363372782461132564665 10347272529586845849423499)
          ·
            refine ⟨15520908794380268774135249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10347272529586845849423499 15520908794380268774135249)
            ·
              refine ⟨11640681595785201580601437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15520908794380268774135249 11640681595785201580601437)
              ·
                refine ⟨4365255598419450592725539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11640681595785201580601437 4365255598419450592725539)
                ·
                  refine ⟨6547883397629175889088309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365255598419450592725539 6547883397629175889088309)
                  ·
                    refine ⟨613864068527735239602029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6547883397629175889088309 613864068527735239602029)
                    ·
                      refine ⟨230199025697900714850761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 613864068527735239602029 230199025697900714850761)
                      ·
                        rfl

theorem cell23_448311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_448311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448311 prefixEnd_448311 := by exact prefixLift 448311
  have htrace : WordTrace (prefixWord ++ tailWord_448311) baseStart_448311 baseEnd_448311 := by
    simpa [prefixWord, tailWord_448311, baseEnd_448311] using wordTrace_append hprefix tailTrace_448311
  have hstable : (prefixWord ++ tailWord_448311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448311).length < 2 ^ (prefixWord ++ tailWord_448311).sum := by decide
  have hdescent : baseEnd_448311 < baseStart_448311 := by decide
  rcases family_descends (prefixWord ++ tailWord_448311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448318 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_448318 : Nat := 118140960795 + 448318 * 2 ^ 59
def prefixEnd_448318 : Nat := 4983230072969 + 3 ^ 40 * 448318 * 2
def baseEnd_448318 : Nat := 25578068895831354162581

theorem tailTrace_448318 : CollatzResearch.WordTrace tailWord_448318 prefixEnd_448318 25578068895831354162581 := by
  unfold tailWord_448318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043937598728490932966201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10901000526551951642486405 2043937598728490932966201)
  ·
    refine ⟨1532953199046368199724651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2043937598728490932966201 1532953199046368199724651)
    ·
      refine ⟨2299429798569552299586977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1532953199046368199724651 2299429798569552299586977)
      ·
        refine ⟨1724572348927164224690233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2299429798569552299586977 1724572348927164224690233)
        ·
          refine ⟨1293429261695373168517675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1724572348927164224690233 1293429261695373168517675)
          ·
            refine ⟨1940143892543059752776513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293429261695373168517675 1940143892543059752776513)
            ·
              refine ⟨1455107919407294814582385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1940143892543059752776513 1455107919407294814582385)
              ·
                refine ⟨1091330939555471110936789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455107919407294814582385 1091330939555471110936789)
                ·
                  refine ⟨25578068895831354162581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1091330939555471110936789 25578068895831354162581)
                  ·
                    rfl

theorem cell23_448318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_448318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448318 prefixEnd_448318 := by exact prefixLift 448318
  have htrace : WordTrace (prefixWord ++ tailWord_448318) baseStart_448318 baseEnd_448318 := by
    simpa [prefixWord, tailWord_448318, baseEnd_448318] using wordTrace_append hprefix tailTrace_448318
  have hstable : (prefixWord ++ tailWord_448318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448318).length < 2 ^ (prefixWord ++ tailWord_448318).sum := by decide
  have hdescent : baseEnd_448318 < baseStart_448318 := by decide
  rcases family_descends (prefixWord ++ tailWord_448318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448368 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 1, 6, 2]
def baseStart_448368 : Nat := 118140960795 + 448368 * 2 ^ 59
def prefixEnd_448368 : Nat := 4983230072969 + 3 ^ 40 * 448368 * 2
def baseEnd_448368 : Nat := 230228294095206991837999

theorem tailTrace_448368 : CollatzResearch.WordTrace tailWord_448368 prefixEnd_448368 230228294095206991837999 := by
  unfold tailWord_448368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8176662219823393001524879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10902216293097857335366505 8176662219823393001524879)
  ·
    refine ⟨12264993329735089502287319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8176662219823393001524879 12264993329735089502287319)
    ·
      refine ⟨18397489994602634253430979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12264993329735089502287319 18397489994602634253430979)
      ·
        refine ⟨27596234991903951380146469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18397489994602634253430979 27596234991903951380146469)
        ·
          refine ⟨5174294060981990883777463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27596234991903951380146469 5174294060981990883777463)
          ·
            refine ⟨7761441091472986325666195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174294060981990883777463 7761441091472986325666195)
            ·
              refine ⟨11642161637209479488499293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761441091472986325666195 11642161637209479488499293)
              ·
                refine ⟨4365810613953554808187235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11642161637209479488499293 4365810613953554808187235)
                ·
                  refine ⟨6548715920930332212280853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365810613953554808187235 6548715920930332212280853)
                  ·
                    refine ⟨306971058793609322450665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6548715920930332212280853 306971058793609322450665)
                    ·
                      refine ⟨230228294095206991837999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 306971058793609322450665 230228294095206991837999)
                      ·
                        rfl

theorem cell23_448368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 6, 2].length) (baseStart_448368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448368 prefixEnd_448368 := by exact prefixLift 448368
  have htrace : WordTrace (prefixWord ++ tailWord_448368) baseStart_448368 baseEnd_448368 := by
    simpa [prefixWord, tailWord_448368, baseEnd_448368] using wordTrace_append hprefix tailTrace_448368
  have hstable : (prefixWord ++ tailWord_448368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448368).length < 2 ^ (prefixWord ++ tailWord_448368).sum := by decide
  have hdescent : baseEnd_448368 < baseStart_448368 := by decide
  rcases family_descends (prefixWord ++ tailWord_448368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448378 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 3, 4]
def baseStart_448378 : Nat := 118140960795 + 448378 * 2 ^ 59
def prefixEnd_448378 : Nat := 4983230072969 + 3 ^ 40 * 448378 * 2
def baseEnd_448378 : Nat := 76744476300583984237651

theorem tailTrace_448378 : CollatzResearch.WordTrace tailWord_448378 prefixEnd_448378 76744476300583984237651 := by
  unfold tailWord_448378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4088422292402639427728447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10902459446407038473942525 4088422292402639427728447)
  ·
    refine ⟨6132633438603959141592671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4088422292402639427728447 6132633438603959141592671)
    ·
      refine ⟨9198950157905938712389007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6132633438603959141592671 9198950157905938712389007)
      ·
        refine ⟨13798425236858908068583511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9198950157905938712389007 13798425236858908068583511)
        ·
          refine ⟨20697637855288362102875267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13798425236858908068583511 20697637855288362102875267)
          ·
            refine ⟨31046456782932543154312901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20697637855288362102875267 31046456782932543154312901)
            ·
              refine ⟨5821210646799851841433669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31046456782932543154312901 5821210646799851841433669)
              ·
                refine ⟨1091476996274972220268813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5821210646799851841433669 1091476996274972220268813)
                ·
                  refine ⟨409303873603114582600805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091476996274972220268813 409303873603114582600805)
                  ·
                    refine ⟨76744476300583984237651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 409303873603114582600805 76744476300583984237651)
                    ·
                      rfl

theorem cell23_448378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_448378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448378 prefixEnd_448378 := by exact prefixLift 448378
  have htrace : WordTrace (prefixWord ++ tailWord_448378) baseStart_448378 baseEnd_448378 := by
    simpa [prefixWord, tailWord_448378, baseEnd_448378] using wordTrace_append hprefix tailTrace_448378
  have hstable : (prefixWord ++ tailWord_448378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448378).length < 2 ^ (prefixWord ++ tailWord_448378).sum := by decide
  have hdescent : baseEnd_448378 < baseStart_448378 := by decide
  rcases family_descends (prefixWord ++ tailWord_448378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448381 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_448381 : Nat := 118140960795 + 448381 * 2 ^ 59
def prefixEnd_448381 : Nat := 4983230072969 + 3 ^ 40 * 448381 * 2
def baseEnd_448381 : Nat := 230234969343715440975439

theorem tailTrace_448381 : CollatzResearch.WordTrace tailWord_448381 prefixEnd_448381 230234969343715440975439 := by
  unfold tailWord_448381
  simp only [CollatzResearch.WordTrace]
  refine ⟨16353798588599689223272997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10902532392399792815515331 16353798588599689223272997)
  ·
    refine ⟨3066337235362441729363687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16353798588599689223272997 3066337235362441729363687)
    ·
      refine ⟨4599505853043662594045531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3066337235362441729363687 4599505853043662594045531)
      ·
        refine ⟨6899258779565493891068297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4599505853043662594045531 6899258779565493891068297)
        ·
          refine ⟨5174444084674120418301223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6899258779565493891068297 5174444084674120418301223)
          ·
            refine ⟨7761666127011180627451835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174444084674120418301223 7761666127011180627451835)
            ·
              refine ⟨11642499190516770941177753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761666127011180627451835 11642499190516770941177753)
              ·
                refine ⟨8731874392887578205883315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11642499190516770941177753 8731874392887578205883315)
                ·
                  refine ⟨13097811589331367308824973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8731874392887578205883315 13097811589331367308824973)
                  ·
                    refine ⟨4911679345999262740809365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13097811589331367308824973 4911679345999262740809365)
                    ·
                      refine ⟨230234969343715440975439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4911679345999262740809365 230234969343715440975439)
                      ·
                        rfl

theorem cell23_448381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_448381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448381 prefixEnd_448381 := by exact prefixLift 448381
  have htrace : WordTrace (prefixWord ++ tailWord_448381) baseStart_448381 baseEnd_448381 := by
    simpa [prefixWord, tailWord_448381, baseEnd_448381] using wordTrace_append hprefix tailTrace_448381
  have hstable : (prefixWord ++ tailWord_448381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448381).length < 2 ^ (prefixWord ++ tailWord_448381).sum := by decide
  have hdescent : baseEnd_448381 < baseStart_448381 := by decide
  rcases family_descends (prefixWord ++ tailWord_448381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448382 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_448382 : Nat := 118140960795 + 448382 * 2 ^ 59
def prefixEnd_448382 : Nat := 4983230072969 + 3 ^ 40 * 448382 * 2
def baseEnd_448382 : Nat := 76745160941456645687645

theorem tailTrace_448382 : CollatzResearch.WordTrace tailWord_448382 prefixEnd_448382 76745160941456645687645 := by
  unfold tailWord_448382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2044229382699508299257425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10902556707730710929372933 2044229382699508299257425)
  ·
    refine ⟨1533172037024631224443069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2044229382699508299257425 1533172037024631224443069)
    ·
      refine ⟨574939513884236709166151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1533172037024631224443069 574939513884236709166151)
      ·
        refine ⟨862409270826355063749227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574939513884236709166151 862409270826355063749227)
        ·
          refine ⟨1293613906239532595623841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862409270826355063749227 1293613906239532595623841)
          ·
            refine ⟨970210429679649446717881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1293613906239532595623841 970210429679649446717881)
            ·
              refine ⟨727657822259737085038411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970210429679649446717881 727657822259737085038411)
              ·
                refine ⟨1091486733389605627557617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727657822259737085038411 1091486733389605627557617)
                ·
                  refine ⟨818615050042204220668213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1091486733389605627557617 818615050042204220668213)
                  ·
                    refine ⟨76745160941456645687645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 818615050042204220668213 76745160941456645687645)
                    ·
                      rfl

theorem cell23_448382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_448382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448382 prefixEnd_448382 := by exact prefixLift 448382
  have htrace : WordTrace (prefixWord ++ tailWord_448382) baseStart_448382 baseEnd_448382 := by
    simpa [prefixWord, tailWord_448382, baseEnd_448382] using wordTrace_append hprefix tailTrace_448382
  have hstable : (prefixWord ++ tailWord_448382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448382).length < 2 ^ (prefixWord ++ tailWord_448382).sum := by decide
  have hdescent : baseEnd_448382 < baseStart_448382 := by decide
  rcases family_descends (prefixWord ++ tailWord_448382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448388 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_448388 : Nat := 118140960795 + 448388 * 2 ^ 59
def prefixEnd_448388 : Nat := 4983230072969 + 3 ^ 40 * 448388 * 2
def baseEnd_448388 : Nat := 230238563708296913587907

theorem tailTrace_448388 : CollatzResearch.WordTrace tailWord_448388 prefixEnd_448388 230238563708296913587907 := by
  unfold tailWord_448388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8177026949787164709388909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10902702599716219612518545 8177026949787164709388909)
  ·
    refine ⟨3066385106170186766020841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8177026949787164709388909 3066385106170186766020841)
    ·
      refine ⟨2299788829627640074515631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3066385106170186766020841 2299788829627640074515631)
      ·
        refine ⟨3449683244441460111773447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299788829627640074515631 3449683244441460111773447)
        ·
          refine ⟨5174524866662190167660171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3449683244441460111773447 5174524866662190167660171)
          ·
            refine ⟨7761787299993285251490257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174524866662190167660171 7761787299993285251490257)
            ·
              refine ⟨5821340474994963938617693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7761787299993285251490257 5821340474994963938617693)
              ·
                refine ⟨2183002678123111476981635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5821340474994963938617693 2183002678123111476981635)
                ·
                  refine ⟨3274504017184667215472453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183002678123111476981635 3274504017184667215472453)
                  ·
                    refine ⟨613969503222125102901085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3274504017184667215472453 613969503222125102901085)
                    ·
                      refine ⟨230238563708296913587907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 613969503222125102901085 230238563708296913587907)
                      ·
                        rfl

theorem cell23_448388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_448388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448388 prefixEnd_448388 := by exact prefixLift 448388
  have htrace : WordTrace (prefixWord ++ tailWord_448388) baseStart_448388 baseEnd_448388 := by
    simpa [prefixWord, tailWord_448388, baseEnd_448388] using wordTrace_append hprefix tailTrace_448388
  have hstable : (prefixWord ++ tailWord_448388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448388).length < 2 ^ (prefixWord ++ tailWord_448388).sum := by decide
  have hdescent : baseEnd_448388 < baseStart_448388 := by decide
  rcases family_descends (prefixWord ++ tailWord_448388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448395 : List Nat := [1, 1, 1, 1, 4, 2, 1, 7, 1, 4]
def baseStart_448395 : Nat := 118140960795 + 448395 * 2 ^ 59
def prefixEnd_448395 : Nat := 4983230072969 + 3 ^ 40 * 448395 * 2
def baseEnd_448395 : Nat := 76747386024292795400125

theorem tailTrace_448395 : CollatzResearch.WordTrace tailWord_448395 prefixEnd_448395 76747386024292795400125 := by
  unfold tailWord_448395
  simp only [CollatzResearch.WordTrace]
  refine ⟨16354309210548969614282639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10902872807032646409521759 16354309210548969614282639)
  ·
    refine ⟨24531463815823454421423959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16354309210548969614282639 24531463815823454421423959)
    ·
      refine ⟨36797195723735181632135939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24531463815823454421423959 36797195723735181632135939)
      ·
        refine ⟨55195793585602772448203909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36797195723735181632135939 55195793585602772448203909)
        ·
          refine ⟨10349211297300519834038233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55195793585602772448203909 10349211297300519834038233)
          ·
            refine ⟨7761908472975389875528675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10349211297300519834038233 7761908472975389875528675)
            ·
              refine ⟨11642862709463084813293013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761908472975389875528675 11642862709463084813293013)
              ·
                refine ⟨272879594753041050311555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11642862709463084813293013 272879594753041050311555)
                ·
                  refine ⟨409319392129561575467333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272879594753041050311555 409319392129561575467333)
                  ·
                    refine ⟨76747386024292795400125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 409319392129561575467333 76747386024292795400125)
                    ·
                      rfl

theorem cell23_448395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 1, 4].length) (baseStart_448395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448395 prefixEnd_448395 := by exact prefixLift 448395
  have htrace : WordTrace (prefixWord ++ tailWord_448395) baseStart_448395 baseEnd_448395 := by
    simpa [prefixWord, tailWord_448395, baseEnd_448395] using wordTrace_append hprefix tailTrace_448395
  have hstable : (prefixWord ++ tailWord_448395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448395).length < 2 ^ (prefixWord ++ tailWord_448395).sum := by decide
  have hdescent : baseEnd_448395 < baseStart_448395 := by decide
  rcases family_descends (prefixWord ++ tailWord_448395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448431 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_448431 : Nat := 118140960795 + 448431 * 2 ^ 59
def prefixEnd_448431 : Nat := 4983230072969 + 3 ^ 40 * 448431 * 2
def baseEnd_448431 : Nat := 230260643376440245350209

theorem tailTrace_448431 : CollatzResearch.WordTrace tailWord_448431 prefixEnd_448431 230260643376440245350209 := by
  unfold tailWord_448431
  simp only [CollatzResearch.WordTrace]
  refine ⟨16355622238418547762593147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10903748158945698508395431 16355622238418547762593147)
  ·
    refine ⟨24533433357627821643889721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16355622238418547762593147 24533433357627821643889721)
    ·
      refine ⟨18400075018220866232917291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24533433357627821643889721 18400075018220866232917291)
      ·
        refine ⟨27600112527331299349375937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18400075018220866232917291 27600112527331299349375937)
        ·
          refine ⟨20700084395498474512031953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27600112527331299349375937 20700084395498474512031953)
          ·
            refine ⟨15525063296623855884023965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20700084395498474512031953 15525063296623855884023965)
            ·
              refine ⟨5821898736233945956508987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15525063296623855884023965 5821898736233945956508987)
              ·
                refine ⟨8732848104350918934763481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5821898736233945956508987 8732848104350918934763481)
                ·
                  refine ⟨6549636078263189201072611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8732848104350918934763481 6549636078263189201072611)
                  ·
                    refine ⟨9824454117394783801608917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6549636078263189201072611 9824454117394783801608917)
                    ·
                      refine ⟨230260643376440245350209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9824454117394783801608917 230260643376440245350209)
                      ·
                        rfl

theorem cell23_448431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_448431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448431 prefixEnd_448431 := by exact prefixLift 448431
  have htrace : WordTrace (prefixWord ++ tailWord_448431) baseStart_448431 baseEnd_448431 := by
    simpa [prefixWord, tailWord_448431, baseEnd_448431] using wordTrace_append hprefix tailTrace_448431
  have hstable : (prefixWord ++ tailWord_448431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448431).length < 2 ^ (prefixWord ++ tailWord_448431).sum := by decide
  have hdescent : baseEnd_448431 < baseStart_448431 := by decide
  rcases family_descends (prefixWord ++ tailWord_448431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448435 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 3, 1, 3]
def baseStart_448435 : Nat := 118140960795 + 448435 * 2 ^ 59
def prefixEnd_448435 : Nat := 4983230072969 + 3 ^ 40 * 448435 * 2
def baseEnd_448435 : Nat := 230262697299058229700191

theorem tailTrace_448435 : CollatzResearch.WordTrace tailWord_448435 prefixEnd_448435 230262697299058229700191 := by
  unfold tailWord_448435
  simp only [CollatzResearch.WordTrace]
  refine ⟨16355768130404056445738759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10903845420269370963825839 16355768130404056445738759)
  ·
    refine ⟨24533652195606084668608139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16355768130404056445738759 24533652195606084668608139)
    ·
      refine ⟨36800478293409127002912209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24533652195606084668608139 36800478293409127002912209)
      ·
        refine ⟨27600358720056845252184157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36800478293409127002912209 27600358720056845252184157)
        ·
          refine ⟨10350134520021316969569059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27600358720056845252184157 10350134520021316969569059)
          ·
            refine ⟨15525201780031975454353589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10350134520021316969569059 15525201780031975454353589)
            ·
              refine ⟨1455487666877997698845649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15525201780031975454353589 1455487666877997698845649)
              ·
                refine ⟨1091615750158498274134237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1455487666877997698845649 1091615750158498274134237)
                ·
                  refine ⟨409355906309436852800339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1091615750158498274134237 409355906309436852800339)
                  ·
                    refine ⟨614033859464155279200509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 409355906309436852800339 614033859464155279200509)
                    ·
                      refine ⟨230262697299058229700191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 614033859464155279200509 230262697299058229700191)
                      ·
                        rfl

theorem cell23_448435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 1, 3].length) (baseStart_448435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448435 prefixEnd_448435 := by exact prefixLift 448435
  have htrace : WordTrace (prefixWord ++ tailWord_448435) baseStart_448435 baseEnd_448435 := by
    simpa [prefixWord, tailWord_448435, baseEnd_448435] using wordTrace_append hprefix tailTrace_448435
  have hstable : (prefixWord ++ tailWord_448435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448435).length < 2 ^ (prefixWord ++ tailWord_448435).sum := by decide
  have hdescent : baseEnd_448435 < baseStart_448435 := by decide
  rcases family_descends (prefixWord ++ tailWord_448435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448436 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_448436 : Nat := 118140960795 + 448436 * 2 ^ 59
def prefixEnd_448436 : Nat := 4983230072969 + 3 ^ 40 * 448436 * 2
def baseEnd_448436 : Nat := 230263210779712725787687

theorem tailTrace_448436 : CollatzResearch.WordTrace tailWord_448436 prefixEnd_448436 230263210779712725787687 := by
  unfold tailWord_448436
  simp only [CollatzResearch.WordTrace]
  refine ⟨8177902301700216808262581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10903869735600289077683441 8177902301700216808262581)
  ·
    refine ⟨766678340784395325774617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8177902301700216808262581 766678340784395325774617)
    ·
      refine ⟨575008755588296494330963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 766678340784395325774617 575008755588296494330963)
      ·
        refine ⟨862513133382444741496445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575008755588296494330963 862513133382444741496445)
        ·
          refine ⟨323442425018416778061167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 862513133382444741496445 323442425018416778061167)
          ·
            refine ⟨485163637527625167091751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323442425018416778061167 485163637527625167091751)
            ·
              refine ⟨727745456291437750637627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485163637527625167091751 727745456291437750637627)
              ·
                refine ⟨1091618184437156625956441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727745456291437750637627 1091618184437156625956441)
                ·
                  refine ⟨818713638327867469467331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1091618184437156625956441 818713638327867469467331)
                  ·
                    refine ⟨1228070457491801204200997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 818713638327867469467331 1228070457491801204200997)
                    ·
                      refine ⟨230263210779712725787687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1228070457491801204200997 230263210779712725787687)
                      ·
                        rfl

theorem cell23_448436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_448436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448436 prefixEnd_448436 := by exact prefixLift 448436
  have htrace : WordTrace (prefixWord ++ tailWord_448436) baseStart_448436 baseEnd_448436 := by
    simpa [prefixWord, tailWord_448436, baseEnd_448436] using wordTrace_append hprefix tailTrace_448436
  have hstable : (prefixWord ++ tailWord_448436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448436).length < 2 ^ (prefixWord ++ tailWord_448436).sum := by decide
  have hdescent : baseEnd_448436 < baseStart_448436 := by decide
  rcases family_descends (prefixWord ++ tailWord_448436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448469 : List Nat := [1, 3, 2, 3, 2, 1, 2, 4, 1, 1, 3]
def baseStart_448469 : Nat := 118140960795 + 448469 * 2 ^ 59
def prefixEnd_448469 : Nat := 4983230072969 + 3 ^ 40 * 448469 * 2
def baseEnd_448469 : Nat := 230280155641311096675035

theorem tailTrace_448469 : CollatzResearch.WordTrace tailWord_448469 prefixEnd_448469 230280155641311096675035 := by
  unfold tailWord_448469
  simp only [CollatzResearch.WordTrace]
  refine ⟨16357008212280880252476461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10904672141520586834984307 16357008212280880252476461)
  ·
    refine ⟨6133878079605330094678673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16357008212280880252476461 6133878079605330094678673)
    ·
      refine ⟨4600408559703997571009005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6133878079605330094678673 4600408559703997571009005)
      ·
        refine ⟨1725153209888999089128377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4600408559703997571009005 1725153209888999089128377)
        ·
          refine ⟨1293864907416749316846283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1725153209888999089128377 1293864907416749316846283)
          ·
            refine ⟨1940797361125123975269425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293864907416749316846283 1940797361125123975269425)
            ·
              refine ⟨1455598020843842981452069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1940797361125123975269425 1455598020843842981452069)
              ·
                refine ⟨272924628908220559022263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1455598020843842981452069 272924628908220559022263)
                ·
                  refine ⟨409386943362330838533395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272924628908220559022263 409386943362330838533395)
                  ·
                    refine ⟨614080415043496257800093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 409386943362330838533395 614080415043496257800093)
                    ·
                      refine ⟨230280155641311096675035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 614080415043496257800093 230280155641311096675035)
                      ·
                        rfl

theorem cell23_448469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_448469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448469 prefixEnd_448469 := by exact prefixLift 448469
  have htrace : WordTrace (prefixWord ++ tailWord_448469) baseStart_448469 baseEnd_448469 := by
    simpa [prefixWord, tailWord_448469, baseEnd_448469] using wordTrace_append hprefix tailTrace_448469
  have hstable : (prefixWord ++ tailWord_448469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448469).length < 2 ^ (prefixWord ++ tailWord_448469).sum := by decide
  have hdescent : baseEnd_448469 < baseStart_448469 := by decide
  rcases family_descends (prefixWord ++ tailWord_448469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448476 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 6]
def baseStart_448476 : Nat := 118140960795 + 448476 * 2 ^ 59
def prefixEnd_448476 : Nat := 4983230072969 + 3 ^ 40 * 448476 * 2
def baseEnd_448476 : Nat := 25587083333988063254167

theorem tailTrace_448476 : CollatzResearch.WordTrace tailWord_448476 prefixEnd_448476 25587083333988063254167 := by
  unfold tailWord_448476
  simp only [CollatzResearch.WordTrace]
  refine ⟨8178631761627760223990641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10904842348837013631987521 8178631761627760223990641)
  ·
    refine ⟨6133973821220820167992981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8178631761627760223990641 6133973821220820167992981)
    ·
      refine ⟨287530022869725945374671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6133973821220820167992981 287530022869725945374671)
      ·
        refine ⟨431295034304588918062007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287530022869725945374671 431295034304588918062007)
        ·
          refine ⟨646942551456883377093011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431295034304588918062007 646942551456883377093011)
          ·
            refine ⟨970413827185325065639517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646942551456883377093011 970413827185325065639517)
            ·
              refine ⟨363905185194496899614819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 970413827185325065639517 363905185194496899614819)
              ·
                refine ⟨545857777791745349422229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363905185194496899614819 545857777791745349422229)
                ·
                  refine ⟨25587083333988063254167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 545857777791745349422229 25587083333988063254167)
                  ·
                    rfl

theorem cell23_448476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_448476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448476 prefixEnd_448476 := by exact prefixLift 448476
  have htrace : WordTrace (prefixWord ++ tailWord_448476) baseStart_448476 baseEnd_448476 := by
    simpa [prefixWord, tailWord_448476, baseEnd_448476] using wordTrace_append hprefix tailTrace_448476
  have hstable : (prefixWord ++ tailWord_448476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448476).length < 2 ^ (prefixWord ++ tailWord_448476).sum := by decide
  have hdescent : baseEnd_448476 < baseStart_448476 := by decide
  rcases family_descends (prefixWord ++ tailWord_448476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448582 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_448582 : Nat := 118140960795 + 448582 * 2 ^ 59
def prefixEnd_448582 : Nat := 4983230072969 + 3 ^ 40 * 448582 * 2
def baseEnd_448582 : Nat := 230338178955269154562015

theorem tailTrace_448582 : CollatzResearch.WordTrace tailWord_448582 prefixEnd_448582 230338178955269154562015 := by
  unfold tailWord_448582
  simp only [CollatzResearch.WordTrace]
  refine ⟨511285301902234392229375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10907419773914333700893333 511285301902234392229375)
  ·
    refine ⟨766927952853351588344063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 511285301902234392229375 766927952853351588344063)
    ·
      refine ⟨1150391929280027382516095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766927952853351588344063 1150391929280027382516095)
      ·
        refine ⟨1725587893920041073774143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150391929280027382516095 1725587893920041073774143)
        ·
          refine ⟨2588381840880061610661215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725587893920041073774143 2588381840880061610661215)
          ·
            refine ⟨3882572761320092415991823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588381840880061610661215 3882572761320092415991823)
            ·
              refine ⟨5823859141980138623987735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882572761320092415991823 5823859141980138623987735)
              ·
                refine ⟨8735788712970207935981603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5823859141980138623987735 8735788712970207935981603)
                ·
                  refine ⟨13103683069455311903972405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8735788712970207935981603 13103683069455311903972405)
                  ·
                    refine ⟨1228470287761435490997413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13103683069455311903972405 1228470287761435490997413)
                    ·
                      refine ⟨230338178955269154562015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1228470287761435490997413 230338178955269154562015)
                      ·
                        rfl

theorem cell23_448582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_448582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448582 prefixEnd_448582 := by exact prefixLift 448582
  have htrace : WordTrace (prefixWord ++ tailWord_448582) baseStart_448582 baseEnd_448582 := by
    simpa [prefixWord, tailWord_448582, baseEnd_448582] using wordTrace_append hprefix tailTrace_448582
  have hstable : (prefixWord ++ tailWord_448582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448582).length < 2 ^ (prefixWord ++ tailWord_448582).sum := by decide
  have hdescent : baseEnd_448582 < baseStart_448582 := by decide
  rcases family_descends (prefixWord ++ tailWord_448582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448599 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 2, 2, 2]
def baseStart_448599 : Nat := 118140960795 + 448599 * 2 ^ 59
def prefixEnd_448599 : Nat := 4983230072969 + 3 ^ 40 * 448599 * 2
def baseEnd_448599 : Nat := 230346908126395588049437

theorem tailTrace_448599 : CollatzResearch.WordTrace tailWord_448599 prefixEnd_448599 230346908126395588049437 := by
  unfold tailWord_448599
  simp only [CollatzResearch.WordTrace]
  refine ⟨16361749701809912454708851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10907833134539941636472567 16361749701809912454708851)
  ·
    refine ⟨24542624552714868682063277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16361749701809912454708851 24542624552714868682063277)
    ·
      refine ⟨9203484207268075755773729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24542624552714868682063277 9203484207268075755773729)
      ·
        refine ⟨6902613155451056816830297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9203484207268075755773729 6902613155451056816830297)
        ·
          refine ⟨5176959866588292612622723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6902613155451056816830297 5176959866588292612622723)
          ·
            refine ⟨7765439799882438918934085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176959866588292612622723 7765439799882438918934085)
            ·
              refine ⟨1456019962477957297300141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7765439799882438918934085 1456019962477957297300141)
              ·
                refine ⟨546007485929233986487553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1456019962477957297300141 546007485929233986487553)
                ·
                  refine ⟨409505614446925489865665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546007485929233986487553 409505614446925489865665)
                  ·
                    refine ⟨307129210835194117399249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 409505614446925489865665 307129210835194117399249)
                    ·
                      refine ⟨230346908126395588049437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 307129210835194117399249 230346908126395588049437)
                      ·
                        rfl

theorem cell23_448599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_448599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448599 prefixEnd_448599 := by exact prefixLift 448599
  have htrace : WordTrace (prefixWord ++ tailWord_448599) baseStart_448599 baseEnd_448599 := by
    simpa [prefixWord, tailWord_448599, baseEnd_448599] using wordTrace_append hprefix tailTrace_448599
  have hstable : (prefixWord ++ tailWord_448599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448599).length < 2 ^ (prefixWord ++ tailWord_448599).sum := by decide
  have hdescent : baseEnd_448599 < baseStart_448599 := by decide
  rcases family_descends (prefixWord ++ tailWord_448599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448615 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_448615 : Nat := 118140960795 + 448615 * 2 ^ 59
def prefixEnd_448615 : Nat := 4983230072969 + 3 ^ 40 * 448615 * 2
def baseEnd_448615 : Nat := 230355123816867525449363

theorem tailTrace_448615 : CollatzResearch.WordTrace tailWord_448615 prefixEnd_448615 230355123816867525449363 := by
  unfold tailWord_448615
  simp only [CollatzResearch.WordTrace]
  refine ⟨16362333269751947187291299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10908222179834631458194199 16362333269751947187291299)
  ·
    refine ⟨24543499904627920780936949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16362333269751947187291299 24543499904627920780936949)
    ·
      refine ⟨2300953116058867573212839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24543499904627920780936949 2300953116058867573212839)
      ·
        refine ⟨3451429674088301359819259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300953116058867573212839 3451429674088301359819259)
        ·
          refine ⟨5177144511132452039728889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451429674088301359819259 5177144511132452039728889)
          ·
            refine ⟨3882858383349339029796667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5177144511132452039728889 3882858383349339029796667)
            ·
              refine ⟨5824287575024008544695001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882858383349339029796667 5824287575024008544695001)
              ·
                refine ⟨4368215681268006408521251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5824287575024008544695001 4368215681268006408521251)
                ·
                  refine ⟨6552323521902009612781877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368215681268006408521251 6552323521902009612781877)
                  ·
                    refine ⟨614280330178313401198301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6552323521902009612781877 614280330178313401198301)
                    ·
                      refine ⟨230355123816867525449363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 614280330178313401198301 230355123816867525449363)
                      ·
                        rfl

theorem cell23_448615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_448615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448615 prefixEnd_448615 := by exact prefixLift 448615
  have htrace : WordTrace (prefixWord ++ tailWord_448615) baseStart_448615 baseEnd_448615 := by
    simpa [prefixWord, tailWord_448615, baseEnd_448615] using wordTrace_append hprefix tailTrace_448615
  have hstable : (prefixWord ++ tailWord_448615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448615).length < 2 ^ (prefixWord ++ tailWord_448615).sum := by decide
  have hdescent : baseEnd_448615 < baseStart_448615 := by decide
  rcases family_descends (prefixWord ++ tailWord_448615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448686 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_448686 : Nat := 118140960795 + 448686 * 2 ^ 59
def prefixEnd_448686 : Nat := 4983230072969 + 3 ^ 40 * 448686 * 2
def baseEnd_448686 : Nat := 76797193647778915887179

theorem tailTrace_448686 : CollatzResearch.WordTrace tailWord_448686 prefixEnd_448686 76797193647778915887179 := by
  unfold tailWord_448686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045615356561840789140739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10909948568329817542083941 2045615356561840789140739)
  ·
    refine ⟨3068423034842761183711109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2045615356561840789140739 3068423034842761183711109)
    ·
      refine ⟨575329319033017721945833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3068423034842761183711109 575329319033017721945833)
      ·
        refine ⟨431496989274763291459375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575329319033017721945833 431496989274763291459375)
        ·
          refine ⟨647245483912144937189063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431496989274763291459375 647245483912144937189063)
          ·
            refine ⟨970868225868217405783595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647245483912144937189063 970868225868217405783595)
            ·
              refine ⟨1456302338802326108675393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970868225868217405783595 1456302338802326108675393)
              ·
                refine ⟨1092226754101744581506545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456302338802326108675393 1092226754101744581506545)
                ·
                  refine ⟨819170065576308436129909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092226754101744581506545 819170065576308436129909)
                  ·
                    refine ⟨76797193647778915887179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 819170065576308436129909 76797193647778915887179)
                    ·
                      rfl

theorem cell23_448686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_448686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448686 prefixEnd_448686 := by exact prefixLift 448686
  have htrace : WordTrace (prefixWord ++ tailWord_448686) baseStart_448686 baseEnd_448686 := by
    simpa [prefixWord, tailWord_448686, baseEnd_448686] using wordTrace_append hprefix tailTrace_448686
  have hstable : (prefixWord ++ tailWord_448686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448686).length < 2 ^ (prefixWord ++ tailWord_448686).sum := by decide
  have hdescent : baseEnd_448686 < baseStart_448686 := by decide
  rcases family_descends (prefixWord ++ tailWord_448686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448689 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 4]
def baseStart_448689 : Nat := 118140960795 + 448689 * 2 ^ 59
def prefixEnd_448689 : Nat := 4983230072969 + 3 ^ 40 * 448689 * 2
def baseEnd_448689 : Nat := 230393121385300235924023

theorem tailTrace_448689 : CollatzResearch.WordTrace tailWord_448689 prefixEnd_448689 230393121385300235924023 := by
  unfold tailWord_448689
  simp only [CollatzResearch.WordTrace]
  refine ⟨16365032271483857825485121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10910021514322571883656747 16365032271483857825485121)
  ·
    refine ⟨12273774203612893369113841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16365032271483857825485121 12273774203612893369113841)
    ·
      refine ⟨9205330652709670026835381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12273774203612893369113841 9205330652709670026835381)
      ·
        refine ⟨862999748691531565015817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9205330652709670026835381 862999748691531565015817)
        ·
          refine ⟨647249811518648673761863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 862999748691531565015817 647249811518648673761863)
          ·
            refine ⟨970874717277973010642795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647249811518648673761863 970874717277973010642795)
            ·
              refine ⟨1456312075916959515964193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970874717277973010642795 1456312075916959515964193)
              ·
                refine ⟨1092234056937719636973145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1456312075916959515964193 1092234056937719636973145)
                ·
                  refine ⟨819175542703289727729859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092234056937719636973145 819175542703289727729859)
                  ·
                    refine ⟨1228763314054934591594789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 819175542703289727729859 1228763314054934591594789)
                    ·
                      refine ⟨230393121385300235924023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1228763314054934591594789 230393121385300235924023)
                      ·
                        rfl

theorem cell23_448689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_448689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448689 prefixEnd_448689 := by exact prefixLift 448689
  have htrace : WordTrace (prefixWord ++ tailWord_448689) baseStart_448689 baseEnd_448689 := by
    simpa [prefixWord, tailWord_448689, baseEnd_448689] using wordTrace_append hprefix tailTrace_448689
  have hstable : (prefixWord ++ tailWord_448689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448689).length < 2 ^ (prefixWord ++ tailWord_448689).sum := by decide
  have hdescent : baseEnd_448689 < baseStart_448689 := by decide
  rcases family_descends (prefixWord ++ tailWord_448689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448695 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 8]
def baseStart_448695 : Nat := 118140960795 + 448695 * 2 ^ 59
def prefixEnd_448695 : Nat := 4983230072969 + 3 ^ 40 * 448695 * 2
def baseEnd_448695 : Nat := 25599578029914134716555

theorem tailTrace_448695 : CollatzResearch.WordTrace tailWord_448695 prefixEnd_448695 25599578029914134716555 := by
  unfold tailWord_448695
  simp only [CollatzResearch.WordTrace]
  refine ⟨16365251109462120850203539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10910167406308080566802359 16365251109462120850203539)
  ·
    refine ⟨24547876664193181275305309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16365251109462120850203539 24547876664193181275305309)
    ·
      refine ⟨9205453749072442978239491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24547876664193181275305309 9205453749072442978239491)
      ·
        refine ⟨13808180623608664467359237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9205453749072442978239491 13808180623608664467359237)
        ·
          refine ⟨2589033866926624587629857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13808180623608664467359237 2589033866926624587629857)
          ·
            refine ⟨1941775400194968440722393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2589033866926624587629857 1941775400194968440722393)
            ·
              refine ⟨1456331550146226330541795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1941775400194968440722393 1456331550146226330541795)
              ·
                refine ⟨2184497325219339495812693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456331550146226330541795 2184497325219339495812693)
                ·
                  refine ⟨25599578029914134716555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2184497325219339495812693 25599578029914134716555)
                  ·
                    rfl

theorem cell23_448695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 8].length) (baseStart_448695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448695 prefixEnd_448695 := by exact prefixLift 448695
  have htrace : WordTrace (prefixWord ++ tailWord_448695) baseStart_448695 baseEnd_448695 := by
    simpa [prefixWord, tailWord_448695, baseEnd_448695] using wordTrace_append hprefix tailTrace_448695
  have hstable : (prefixWord ++ tailWord_448695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448695).length < 2 ^ (prefixWord ++ tailWord_448695).sum := by decide
  have hdescent : baseEnd_448695 < baseStart_448695 := by decide
  rcases family_descends (prefixWord ++ tailWord_448695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448726 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_448726 : Nat := 118140960795 + 448726 * 2 ^ 59
def prefixEnd_448726 : Nat := 4983230072969 + 3 ^ 40 * 448726 * 2
def baseEnd_448726 : Nat := 230412120169516591161353

theorem tailTrace_448726 : CollatzResearch.WordTrace tailWord_448726 prefixEnd_448726 230412120169516591161353 := by
  unfold tailWord_448726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022898860771863321536377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10910921181566542096388021 1022898860771863321536377)
  ·
    refine ⟨767174145578897491152283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1022898860771863321536377 767174145578897491152283)
    ·
      refine ⟨1150761218368346236728425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 767174145578897491152283 1150761218368346236728425)
      ·
        refine ⟨863070913776259677546319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1150761218368346236728425 863070913776259677546319)
        ·
          refine ⟨1294606370664389516319479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863070913776259677546319 1294606370664389516319479)
          ·
            refine ⟨1941909555996584274479219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294606370664389516319479 1941909555996584274479219)
            ·
              refine ⟨2912864333994876411718829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941909555996584274479219 2912864333994876411718829)
              ·
                refine ⟨1092324125248078654394561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2912864333994876411718829 1092324125248078654394561)
                ·
                  refine ⟨819243093936058990795921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092324125248078654394561 819243093936058990795921)
                  ·
                    refine ⟨614432320452044243096941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 819243093936058990795921 614432320452044243096941)
                    ·
                      refine ⟨230412120169516591161353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 614432320452044243096941 230412120169516591161353)
                      ·
                        rfl

theorem cell23_448726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_448726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448726 prefixEnd_448726 := by exact prefixLift 448726
  have htrace : WordTrace (prefixWord ++ tailWord_448726) baseStart_448726 baseEnd_448726 := by
    simpa [prefixWord, tailWord_448726, baseEnd_448726] using wordTrace_append hprefix tailTrace_448726
  have hstable : (prefixWord ++ tailWord_448726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448726).length < 2 ^ (prefixWord ++ tailWord_448726).sum := by decide
  have hdescent : baseEnd_448726 < baseStart_448726 := by decide
  rcases family_descends (prefixWord ++ tailWord_448726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448755 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 3, 6]
def baseStart_448755 : Nat := 118140960795 + 448755 * 2 ^ 59
def prefixEnd_448755 : Nat := 4983230072969 + 3 ^ 40 * 448755 * 2
def baseEnd_448755 : Nat := 76809003702832325899573

theorem tailTrace_448755 : CollatzResearch.WordTrace tailWord_448755 prefixEnd_448755 76809003702832325899573 := by
  unfold tailWord_448755
  simp only [CollatzResearch.WordTrace]
  refine ⟨16367439489244751097387719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10911626326163167398258479 16367439489244751097387719)
  ·
    refine ⟨24551159233867126646081579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16367439489244751097387719 24551159233867126646081579)
    ·
      refine ⟨36826738850800689969122369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24551159233867126646081579 36826738850800689969122369)
      ·
        refine ⟨27620054138100517476841777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36826738850800689969122369 27620054138100517476841777)
        ·
          refine ⟨20715040603575388107631333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27620054138100517476841777 20715040603575388107631333)
          ·
            refine ⟨3884070113170385270180875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20715040603575388107631333 3884070113170385270180875)
            ·
              refine ⟨5826105169755577905271313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884070113170385270180875 5826105169755577905271313)
              ·
                refine ⟨4369578877316683428953485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5826105169755577905271313 4369578877316683428953485)
                ·
                  refine ⟨1638592078993756285857557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4369578877316683428953485 1638592078993756285857557)
                  ·
                    refine ⟨76809003702832325899573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1638592078993756285857557 76809003702832325899573)
                    ·
                      rfl

theorem cell23_448755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 6].length) (baseStart_448755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448755 prefixEnd_448755 := by exact prefixLift 448755
  have htrace : WordTrace (prefixWord ++ tailWord_448755) baseStart_448755 baseEnd_448755 := by
    simpa [prefixWord, tailWord_448755, baseEnd_448755] using wordTrace_append hprefix tailTrace_448755
  have hstable : (prefixWord ++ tailWord_448755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448755).length < 2 ^ (prefixWord ++ tailWord_448755).sum := by decide
  have hdescent : baseEnd_448755 < baseStart_448755 := by decide
  rcases family_descends (prefixWord ++ tailWord_448755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448762 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_448762 : Nat := 118140960795 + 448762 * 2 ^ 59
def prefixEnd_448762 : Nat := 4983230072969 + 3 ^ 40 * 448762 * 2
def baseEnd_448762 : Nat := 230430605473078450311187

theorem tailTrace_448762 : CollatzResearch.WordTrace tailWord_448762 prefixEnd_448762 230430605473078450311187 := by
  unfold tailWord_448762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091923700054847823223135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10911796533479594195261693 4091923700054847823223135)
  ·
    refine ⟨6137885550082271734834703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4091923700054847823223135 6137885550082271734834703)
    ·
      refine ⟨9206828325123407602252055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6137885550082271734834703 9206828325123407602252055)
      ·
        refine ⟨13810242487685111403378083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9206828325123407602252055 13810242487685111403378083)
        ·
          refine ⟨20715363731527667105067125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13810242487685111403378083 20715363731527667105067125)
          ·
            refine ⟨1942065349830718791100043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20715363731527667105067125 1942065349830718791100043)
            ·
              refine ⟨2913098024746078186650065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942065349830718791100043 2913098024746078186650065)
              ·
                refine ⟨2184823518559558639987549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2913098024746078186650065 2184823518559558639987549)
                ·
                  refine ⟨819308819459834489995331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2184823518559558639987549 819308819459834489995331)
                  ·
                    refine ⟨1228963229189751734992997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 819308819459834489995331 1228963229189751734992997)
                    ·
                      refine ⟨230430605473078450311187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1228963229189751734992997 230430605473078450311187)
                      ·
                        rfl

theorem cell23_448762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_448762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448762 prefixEnd_448762 := by exact prefixLift 448762
  have htrace : WordTrace (prefixWord ++ tailWord_448762) baseStart_448762 baseEnd_448762 := by
    simpa [prefixWord, tailWord_448762, baseEnd_448762] using wordTrace_append hprefix tailTrace_448762
  have hstable : (prefixWord ++ tailWord_448762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448762).length < 2 ^ (prefixWord ++ tailWord_448762).sum := by decide
  have hdescent : baseEnd_448762 < baseStart_448762 := by decide
  rcases family_descends (prefixWord ++ tailWord_448762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448792 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_448792 : Nat := 118140960795 + 448792 * 2 ^ 59
def prefixEnd_448792 : Nat := 4983230072969 + 3 ^ 40 * 448792 * 2
def baseEnd_448792 : Nat := 230446009892713332936049

theorem tailTrace_448792 : CollatzResearch.WordTrace tailWord_448792 prefixEnd_448792 230446009892713332936049 := by
  unfold tailWord_448792
  simp only [CollatzResearch.WordTrace]
  refine ⟨8184394495055353208242315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10912525993407137610989753 8184394495055353208242315)
  ·
    refine ⟨12276591742583029812363473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8184394495055353208242315 12276591742583029812363473)
    ·
      refine ⟨9207443806937272359272605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12276591742583029812363473 9207443806937272359272605)
      ·
        refine ⟨3452791427601477134727227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9207443806937272359272605 3452791427601477134727227)
        ·
          refine ⟨5179187141402215702090841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452791427601477134727227 5179187141402215702090841)
          ·
            refine ⟨3884390356051661776568131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5179187141402215702090841 3884390356051661776568131)
            ·
              refine ⟨5826585534077492664852197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3884390356051661776568131 5826585534077492664852197)
              ·
                refine ⟨1092484787639529874659787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5826585534077492664852197 1092484787639529874659787)
                ·
                  refine ⟨1638727181459294811989681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092484787639529874659787 1638727181459294811989681)
                  ·
                    refine ⟨1229045386094471108992261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1638727181459294811989681 1229045386094471108992261)
                    ·
                      refine ⟨230446009892713332936049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1229045386094471108992261 230446009892713332936049)
                      ·
                        rfl

theorem cell23_448792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_448792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448792 prefixEnd_448792 := by exact prefixLift 448792
  have htrace : WordTrace (prefixWord ++ tailWord_448792) baseStart_448792 baseEnd_448792 := by
    simpa [prefixWord, tailWord_448792, baseEnd_448792] using wordTrace_append hprefix tailTrace_448792
  have hstable : (prefixWord ++ tailWord_448792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448792).length < 2 ^ (prefixWord ++ tailWord_448792).sum := by decide
  have hdescent : baseEnd_448792 < baseStart_448792 := by decide
  rcases family_descends (prefixWord ++ tailWord_448792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448802 : List Nat := [3, 3, 1, 1, 3, 2, 10]
def baseStart_448802 : Nat := 118140960795 + 448802 * 2 ^ 59
def prefixEnd_448802 : Nat := 4983230072969 + 3 ^ 40 * 448802 * 2
def baseEnd_448802 : Nat := 2845075860484670293963

theorem tailTrace_448802 : CollatzResearch.WordTrace tailWord_448802 prefixEnd_448802 2845075860484670293963 := by
  unfold tailWord_448802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092288430018619531087165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10912769146716318749565773 4092288430018619531087165)
  ·
    refine ⟨1534608161256982324157687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4092288430018619531087165 1534608161256982324157687)
    ·
      refine ⟨2301912241885473486236531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1534608161256982324157687 2301912241885473486236531)
      ·
        refine ⟨3452868362828210229354797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301912241885473486236531 3452868362828210229354797)
        ·
          refine ⟨1294825636060578836008049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3452868362828210229354797 1294825636060578836008049)
          ·
            refine ⟨971119227045434127006037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1294825636060578836008049 971119227045434127006037)
            ·
              refine ⟨2845075860484670293963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 971119227045434127006037 2845075860484670293963)
              ·
                rfl

theorem cell23_448802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 10].length) (baseStart_448802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448802 prefixEnd_448802 := by exact prefixLift 448802
  have htrace : WordTrace (prefixWord ++ tailWord_448802) baseStart_448802 baseEnd_448802 := by
    simpa [prefixWord, tailWord_448802, baseEnd_448802] using wordTrace_append hprefix tailTrace_448802
  have hstable : (prefixWord ++ tailWord_448802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448802).length < 2 ^ (prefixWord ++ tailWord_448802).sum := by decide
  have hdescent : baseEnd_448802 < baseStart_448802 := by decide
  rcases family_descends (prefixWord ++ tailWord_448802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448812 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 3]
def baseStart_448812 : Nat := 118140960795 + 448812 * 2 ^ 59
def prefixEnd_448812 : Nat := 4983230072969 + 3 ^ 40 * 448812 * 2
def baseEnd_448812 : Nat := 230456279505803254685957

theorem tailTrace_448812 : CollatzResearch.WordTrace tailWord_448812 prefixEnd_448812 230456279505803254685957 := by
  unfold tailWord_448812
  simp only [CollatzResearch.WordTrace]
  refine ⟨8184759225019124916106345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10913012300025499888141793 8184759225019124916106345)
  ·
    refine ⟨6138569418764343687079759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8184759225019124916106345 6138569418764343687079759)
    ·
      refine ⟨9207854128146515530619639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6138569418764343687079759 9207854128146515530619639)
      ·
        refine ⟨13811781192219773295929459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9207854128146515530619639 13811781192219773295929459)
        ·
          refine ⟨20717671788329659943894189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13811781192219773295929459 20717671788329659943894189)
          ·
            refine ⟨7769126920623622478960321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20717671788329659943894189 7769126920623622478960321)
            ·
              refine ⟨5826845190467716859220241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7769126920623622478960321 5826845190467716859220241)
              ·
                refine ⟨4370133892850787644415181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5826845190467716859220241 4370133892850787644415181)
                ·
                  refine ⟨1638800209819045366655693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4370133892850787644415181 1638800209819045366655693)
                  ·
                    refine ⟨614550078682142012495885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1638800209819045366655693 614550078682142012495885)
                    ·
                      refine ⟨230456279505803254685957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 614550078682142012495885 230456279505803254685957)
                      ·
                        rfl

theorem cell23_448812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_448812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448812 prefixEnd_448812 := by exact prefixLift 448812
  have htrace : WordTrace (prefixWord ++ tailWord_448812) baseStart_448812 baseEnd_448812 := by
    simpa [prefixWord, tailWord_448812, baseEnd_448812] using wordTrace_append hprefix tailTrace_448812
  have hstable : (prefixWord ++ tailWord_448812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448812).length < 2 ^ (prefixWord ++ tailWord_448812).sum := by decide
  have hdescent : baseEnd_448812 < baseStart_448812 := by decide
  rcases family_descends (prefixWord ++ tailWord_448812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448815 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 1, 9]
def baseStart_448815 : Nat := 118140960795 + 448815 * 2 ^ 59
def prefixEnd_448815 : Nat := 4983230072969 + 3 ^ 40 * 448815 * 2
def baseEnd_448815 : Nat := 76819273315922247649481

theorem tailTrace_448815 : CollatzResearch.WordTrace tailWord_448815 prefixEnd_448815 76819273315922247649481 := by
  unfold tailWord_448815
  simp only [CollatzResearch.WordTrace]
  refine ⟨16369627869027381344571899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10913085246018254229714599 16369627869027381344571899)
  ·
    refine ⟨24554441803541072016857849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16369627869027381344571899 24554441803541072016857849)
    ·
      refine ⟨18415831352655804012643387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24554441803541072016857849 18415831352655804012643387)
      ·
        refine ⟨27623747028983706018965081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18415831352655804012643387 27623747028983706018965081)
        ·
          refine ⟨20717810271737779514223811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27623747028983706018965081 20717810271737779514223811)
          ·
            refine ⟨31076715407606669271335717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20717810271737779514223811 31076715407606669271335717)
            ·
              refine ⟨5826884138926250488375447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31076715407606669271335717 5826884138926250488375447)
              ·
                refine ⟨8740326208389375732563171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826884138926250488375447 8740326208389375732563171)
                ·
                  refine ⟨13110489312584063598844757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8740326208389375732563171 13110489312584063598844757)
                  ·
                    refine ⟨76819273315922247649481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 13110489312584063598844757 76819273315922247649481)
                    ·
                      rfl

theorem cell23_448815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_448815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448815 prefixEnd_448815 := by exact prefixLift 448815
  have htrace : WordTrace (prefixWord ++ tailWord_448815) baseStart_448815 baseEnd_448815 := by
    simpa [prefixWord, tailWord_448815, baseEnd_448815] using wordTrace_append hprefix tailTrace_448815
  have hstable : (prefixWord ++ tailWord_448815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448815).length < 2 ^ (prefixWord ++ tailWord_448815).sum := by decide
  have hdescent : baseEnd_448815 < baseStart_448815 := by decide
  rcases family_descends (prefixWord ++ tailWord_448815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448833 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_448833 : Nat := 118140960795 + 448833 * 2 ^ 59
def prefixEnd_448833 : Nat := 4983230072969 + 3 ^ 40 * 448833 * 2
def baseEnd_448833 : Nat := 230467062599547672523361

theorem tailTrace_448833 : CollatzResearch.WordTrace tailWord_448833 prefixEnd_448833 230467062599547672523361 := by
  unfold tailWord_448833
  simp only [CollatzResearch.WordTrace]
  refine ⟨16370284382962170418727153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10913522921974780279151435 16370284382962170418727153)
  ·
    refine ⟨12277713287221627814045365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16370284382962170418727153 12277713287221627814045365)
    ·
      refine ⟨1151035620677027607566753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12277713287221627814045365 1151035620677027607566753)
      ·
        refine ⟨863276715507770705675065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1151035620677027607566753 863276715507770705675065)
        ·
          refine ⟨647457536630828029256299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863276715507770705675065 647457536630828029256299)
          ·
            refine ⟨971186304946242043884449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647457536630828029256299 971186304946242043884449)
            ·
              refine ⟨728389728709681532913337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971186304946242043884449 728389728709681532913337)
              ·
                refine ⟨546292296532261149685003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728389728709681532913337 546292296532261149685003)
                ·
                  refine ⟨819438444798391724527505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546292296532261149685003 819438444798391724527505)
                  ·
                    refine ⟨614578833598793793395629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 819438444798391724527505 614578833598793793395629)
                    ·
                      refine ⟨230467062599547672523361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 614578833598793793395629 230467062599547672523361)
                      ·
                        rfl

theorem cell23_448833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_448833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448833 prefixEnd_448833 := by exact prefixLift 448833
  have htrace : WordTrace (prefixWord ++ tailWord_448833) baseStart_448833 baseEnd_448833 := by
    simpa [prefixWord, tailWord_448833, baseEnd_448833] using wordTrace_append hprefix tailTrace_448833
  have hstable : (prefixWord ++ tailWord_448833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448833).length < 2 ^ (prefixWord ++ tailWord_448833).sum := by decide
  have hdescent : baseEnd_448833 < baseStart_448833 := by decide
  rcases family_descends (prefixWord ++ tailWord_448833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448920 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 2, 2, 2]
def baseStart_448920 : Nat := 118140960795 + 448920 * 2 ^ 59
def prefixEnd_448920 : Nat := 4983230072969 + 3 ^ 40 * 448920 * 2
def baseEnd_448920 : Nat := 230511735416488832135461

theorem tailTrace_448920 : CollatzResearch.WordTrace tailWord_448920 prefixEnd_448920 230511735416488832135461 := by
  unfold tailWord_448920
  simp only [CollatzResearch.WordTrace]
  refine ⟨8186728766823492138572107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10915638355764656184762809 8186728766823492138572107)
  ·
    refine ⟨12280093150235238207858161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8186728766823492138572107 12280093150235238207858161)
    ·
      refine ⟨9210069862676428655893621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12280093150235238207858161 9210069862676428655893621)
      ·
        refine ⟨863444049625915186490027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9210069862676428655893621 863444049625915186490027)
        ·
          refine ⟨1295166074438872779735041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863444049625915186490027 1295166074438872779735041)
          ·
            refine ⟨971374555829154584801281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1295166074438872779735041 971374555829154584801281)
            ·
              refine ⟨728530916871865938600961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971374555829154584801281 728530916871865938600961)
              ·
                refine ⟨546398187653899453950721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728530916871865938600961 546398187653899453950721)
                ·
                  refine ⟨409798640740424590463041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546398187653899453950721 409798640740424590463041)
                  ·
                    refine ⟨307348980555318442847281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 409798640740424590463041 307348980555318442847281)
                    ·
                      refine ⟨230511735416488832135461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 307348980555318442847281 230511735416488832135461)
                      ·
                        rfl

theorem cell23_448920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_448920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448920 prefixEnd_448920 := by exact prefixLift 448920
  have htrace : WordTrace (prefixWord ++ tailWord_448920) baseStart_448920 baseEnd_448920 := by
    simpa [prefixWord, tailWord_448920, baseEnd_448920] using wordTrace_append hprefix tailTrace_448920
  have hstable : (prefixWord ++ tailWord_448920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448920).length < 2 ^ (prefixWord ++ tailWord_448920).sum := by decide
  have hdescent : baseEnd_448920 < baseStart_448920 := by decide
  rcases family_descends (prefixWord ++ tailWord_448920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448936 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_448936 : Nat := 118140960795 + 448936 * 2 ^ 59
def prefixEnd_448936 : Nat := 4983230072969 + 3 ^ 40 * 448936 * 2
def baseEnd_448936 : Nat := 230519951106960769535387

theorem tailTrace_448936 : CollatzResearch.WordTrace tailWord_448936 prefixEnd_448936 230519951106960769535387 := by
  unfold tailWord_448936
  simp only [CollatzResearch.WordTrace]
  refine ⟨8187020550794509504863331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10916027401059346006484441 8187020550794509504863331)
  ·
    refine ⟨12280530826191764257294997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8187020550794509504863331 12280530826191764257294997)
    ·
      refine ⟨575649882477738949560703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12280530826191764257294997 575649882477738949560703)
      ·
        refine ⟨863474823716608424341055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575649882477738949560703 863474823716608424341055)
        ·
          refine ⟨1295212235574912636511583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863474823716608424341055 1295212235574912636511583)
          ·
            refine ⟨1942818353362368954767375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295212235574912636511583 1942818353362368954767375)
            ·
              refine ⟨2914227530043553432151063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942818353362368954767375 2914227530043553432151063)
              ·
                refine ⟨4371341295065330148226595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914227530043553432151063 4371341295065330148226595)
                ·
                  refine ⟨6557011942597995222339893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371341295065330148226595 6557011942597995222339893)
                  ·
                    refine ⟨614719869618562052094365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6557011942597995222339893 614719869618562052094365)
                    ·
                      refine ⟨230519951106960769535387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 614719869618562052094365 230519951106960769535387)
                      ·
                        rfl

theorem cell23_448936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_448936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448936 prefixEnd_448936 := by exact prefixLift 448936
  have htrace : WordTrace (prefixWord ++ tailWord_448936) baseStart_448936 baseEnd_448936 := by
    simpa [prefixWord, tailWord_448936, baseEnd_448936] using wordTrace_append hprefix tailTrace_448936
  have hstable : (prefixWord ++ tailWord_448936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448936).length < 2 ^ (prefixWord ++ tailWord_448936).sum := by decide
  have hdescent : baseEnd_448936 < baseStart_448936 := by decide
  rcases family_descends (prefixWord ++ tailWord_448936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448956 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 2, 5]
def baseStart_448956 : Nat := 118140960795 + 448956 * 2 ^ 59
def prefixEnd_448956 : Nat := 4983230072969 + 3 ^ 40 * 448956 * 2
def baseEnd_448956 : Nat := 76843406906683563761765

theorem tailTrace_448956 : CollatzResearch.WordTrace tailWord_448956 prefixEnd_448956 76843406906683563761765 := by
  unfold tailWord_448956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8187385280758281212727361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10916513707677708283636481 8187385280758281212727361)
  ·
    refine ⟨6140538960568710909545521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8187385280758281212727361 6140538960568710909545521)
    ·
      refine ⟨4605404220426533182159141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6140538960568710909545521 4605404220426533182159141)
      ·
        refine ⟨863513291329974971654839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4605404220426533182159141 863513291329974971654839)
        ·
          refine ⟨1295269936994962457482259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863513291329974971654839 1295269936994962457482259)
          ·
            refine ⟨1942904905492443686223389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295269936994962457482259 1942904905492443686223389)
            ·
              refine ⟨728589339559666382333771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1942904905492443686223389 728589339559666382333771)
              ·
                refine ⟨1092884009339499573500657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728589339559666382333771 1092884009339499573500657)
                ·
                  refine ⟨819663007004624680125493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1092884009339499573500657 819663007004624680125493)
                  ·
                    refine ⟨76843406906683563761765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 819663007004624680125493 76843406906683563761765)
                    ·
                      rfl

theorem cell23_448956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_448956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448956 prefixEnd_448956 := by exact prefixLift 448956
  have htrace : WordTrace (prefixWord ++ tailWord_448956) baseStart_448956 baseEnd_448956 := by
    simpa [prefixWord, tailWord_448956, baseEnd_448956] using wordTrace_append hprefix tailTrace_448956
  have hstable : (prefixWord ++ tailWord_448956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448956).length < 2 ^ (prefixWord ++ tailWord_448956).sum := by decide
  have hdescent : baseEnd_448956 < baseStart_448956 := by decide
  rcases family_descends (prefixWord ++ tailWord_448956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448986 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 3, 4]
def baseStart_448986 : Nat := 118140960795 + 448986 * 2 ^ 59
def prefixEnd_448986 : Nat := 4983230072969 + 3 ^ 40 * 448986 * 2
def baseEnd_448986 : Nat := 76848541713228524636719

theorem tailTrace_448986 : CollatzResearch.WordTrace tailWord_448986 prefixEnd_448986 76848541713228524636719 := by
  unfold tailWord_448986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4093966187851969387261703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10917243167605251699364541 4093966187851969387261703)
  ·
    refine ⟨6140949281777954080892555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4093966187851969387261703 6140949281777954080892555)
    ·
      refine ⟨9211423922666931121338833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6140949281777954080892555 9211423922666931121338833)
      ·
        refine ⟨6908567942000198341004125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9211423922666931121338833 6908567942000198341004125)
        ·
          refine ⟨2590712978250074377876547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6908567942000198341004125 2590712978250074377876547)
          ·
            refine ⟨3886069467375111566814821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590712978250074377876547 3886069467375111566814821)
            ·
              refine ⟨728638025132833418777779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3886069467375111566814821 728638025132833418777779)
              ·
                refine ⟨1092957037699250128166669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728638025132833418777779 1092957037699250128166669)
                ·
                  refine ⟨409858889137218798062501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092957037699250128166669 409858889137218798062501)
                  ·
                    refine ⟨76848541713228524636719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 409858889137218798062501 76848541713228524636719)
                    ·
                      rfl

theorem cell23_448986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_448986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448986 prefixEnd_448986 := by exact prefixLift 448986
  have htrace : WordTrace (prefixWord ++ tailWord_448986) baseStart_448986 baseEnd_448986 := by
    simpa [prefixWord, tailWord_448986, baseEnd_448986] using wordTrace_append hprefix tailTrace_448986
  have hstable : (prefixWord ++ tailWord_448986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448986).length < 2 ^ (prefixWord ++ tailWord_448986).sum := by decide
  have hdescent : baseEnd_448986 < baseStart_448986 := by decide
  rcases family_descends (prefixWord ++ tailWord_448986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448989 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_448989 : Nat := 118140960795 + 448989 * 2 ^ 59
def prefixEnd_448989 : Nat := 4983230072969 + 3 ^ 40 * 448989 * 2
def baseEnd_448989 : Nat := 230547165581649062172643

theorem tailTrace_448989 : CollatzResearch.WordTrace tailWord_448989 prefixEnd_448989 230547165581649062172643 := by
  unfold tailWord_448989
  simp only [CollatzResearch.WordTrace]
  refine ⟨16375974170397009061406021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10917316113598006040937347 16375974170397009061406021)
  ·
    refine ⟨3070495156949439199013629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16375974170397009061406021 3070495156949439199013629)
    ·
      refine ⟨1151435683856039699630111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3070495156949439199013629 1151435683856039699630111)
      ·
        refine ⟨1727153525784059549445167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151435683856039699630111 1727153525784059549445167)
        ·
          refine ⟨2590730288676089324167751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727153525784059549445167 2590730288676089324167751)
          ·
            refine ⟨3886095433014133986251627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590730288676089324167751 3886095433014133986251627)
            ·
              refine ⟨5829143149521200979377441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886095433014133986251627 5829143149521200979377441)
              ·
                refine ⟨4371857362140900734533081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5829143149521200979377441 4371857362140900734533081)
                ·
                  refine ⟨3278893021605675550899811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4371857362140900734533081 3278893021605675550899811)
                  ·
                    refine ⟨4918339532408513326349717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3278893021605675550899811 4918339532408513326349717)
                    ·
                      refine ⟨230547165581649062172643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4918339532408513326349717 230547165581649062172643)
                      ·
                        rfl

theorem cell23_448989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_448989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_448989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_448989 prefixEnd_448989 := by exact prefixLift 448989
  have htrace : WordTrace (prefixWord ++ tailWord_448989) baseStart_448989 baseEnd_448989 := by
    simpa [prefixWord, tailWord_448989, baseEnd_448989] using wordTrace_append hprefix tailTrace_448989
  have hstable : (prefixWord ++ tailWord_448989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448989).length < 2 ^ (prefixWord ++ tailWord_448989).sum := by decide
  have hdescent : baseEnd_448989 < baseStart_448989 := by decide
  rcases family_descends (prefixWord ++ tailWord_448989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449009 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 2, 5, 3]
def baseStart_449009 : Nat := 118140960795 + 449009 * 2 ^ 59
def prefixEnd_449009 : Nat := 4983230072969 + 3 ^ 40 * 449009 * 2
def baseEnd_449009 : Nat := 230557435194738983922551

theorem tailTrace_449009 : CollatzResearch.WordTrace tailWord_449009 prefixEnd_449009 230557435194738983922551 := by
  unfold tailWord_449009
  simp only [CollatzResearch.WordTrace]
  refine ⟨16376703630324552477134081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10917802420216368318089387 16376703630324552477134081)
  ·
    refine ⟨12282527722743414357850561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16376703630324552477134081 12282527722743414357850561)
    ·
      refine ⟨9211895792057560768387921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12282527722743414357850561 9211895792057560768387921)
      ·
        refine ⟨6908921844043170576290941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9211895792057560768387921 6908921844043170576290941)
        ·
          refine ⟨2590845691516188966109103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6908921844043170576290941 2590845691516188966109103)
          ·
            refine ⟨3886268537274283449163655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590845691516188966109103 3886268537274283449163655)
            ·
              refine ⟨5829402805911425173745483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886268537274283449163655 5829402805911425173745483)
              ·
                refine ⟨8744104208867137760618225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829402805911425173745483 8744104208867137760618225)
                ·
                  refine ⟨6558078156650353320463669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8744104208867137760618225 6558078156650353320463669)
                  ·
                    refine ⟨614819827185970623793469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6558078156650353320463669 614819827185970623793469)
                    ·
                      refine ⟨230557435194738983922551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 614819827185970623793469 230557435194738983922551)
                      ·
                        rfl

theorem cell23_449009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_449009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449009 prefixEnd_449009 := by exact prefixLift 449009
  have htrace : WordTrace (prefixWord ++ tailWord_449009) baseStart_449009 baseEnd_449009 := by
    simpa [prefixWord, tailWord_449009, baseEnd_449009] using wordTrace_append hprefix tailTrace_449009
  have hstable : (prefixWord ++ tailWord_449009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449009).length < 2 ^ (prefixWord ++ tailWord_449009).sum := by decide
  have hdescent : baseEnd_449009 < baseStart_449009 := by decide
  rcases family_descends (prefixWord ++ tailWord_449009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449037 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_449037 : Nat := 118140960795 + 449037 * 2 ^ 59
def prefixEnd_449037 : Nat := 4983230072969 + 3 ^ 40 * 449037 * 2
def baseEnd_449037 : Nat := 76857270884354958124141

theorem tailTrace_449037 : CollatzResearch.WordTrace tailWord_449037 prefixEnd_449037 76857270884354958124141 := by
  unfold tailWord_449037
  simp only [CollatzResearch.WordTrace]
  refine ⟨16377724874223113259153365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10918483249482075506102243 16377724874223113259153365)
  ·
    refine ⟨383852926739604217011407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16377724874223113259153365 383852926739604217011407)
    ·
      refine ⟨575779390109406325517111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383852926739604217011407 575779390109406325517111)
      ·
        refine ⟨863669085164109488275667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575779390109406325517111 863669085164109488275667)
        ·
          refine ⟨1295503627746164232413501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863669085164109488275667 1295503627746164232413501)
          ·
            refine ⟨485813860404811587155063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1295503627746164232413501 485813860404811587155063)
            ·
              refine ⟨728720790607217380732595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485813860404811587155063 728720790607217380732595)
              ·
                refine ⟨1093081185910826071098893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728720790607217380732595 1093081185910826071098893)
                ·
                  refine ⟨409905444716559776662085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093081185910826071098893 409905444716559776662085)
                  ·
                    refine ⟨76857270884354958124141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 409905444716559776662085 76857270884354958124141)
                    ·
                      rfl

theorem cell23_449037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_449037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449037 prefixEnd_449037 := by exact prefixLift 449037
  have htrace : WordTrace (prefixWord ++ tailWord_449037) baseStart_449037 baseEnd_449037 := by
    simpa [prefixWord, tailWord_449037, baseEnd_449037] using wordTrace_append hprefix tailTrace_449037
  have hstable : (prefixWord ++ tailWord_449037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449037).length < 2 ^ (prefixWord ++ tailWord_449037).sum := by decide
  have hdescent : baseEnd_449037 < baseStart_449037 := by decide
  rcases family_descends (prefixWord ++ tailWord_449037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449049 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 4]
def baseStart_449049 : Nat := 118140960795 + 449049 * 2 ^ 59
def prefixEnd_449049 : Nat := 4983230072969 + 3 ^ 40 * 449049 * 2
def baseEnd_449049 : Nat := 230577974420918827422367

theorem tailTrace_449049 : CollatzResearch.WordTrace tailWord_449049 prefixEnd_449049 230577974420918827422367 := by
  unfold tailWord_449049
  simp only [CollatzResearch.WordTrace]
  refine ⟨16378162550179639308590201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10918775033453092872393467 16378162550179639308590201)
  ·
    refine ⟨12283621912634729481442651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16378162550179639308590201 12283621912634729481442651)
    ·
      refine ⟨18425432868952094222163977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12283621912634729481442651 18425432868952094222163977)
      ·
        refine ⟨13819074651714070666622983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18425432868952094222163977 13819074651714070666622983)
        ·
          refine ⟨20728611977571105999934475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13819074651714070666622983 20728611977571105999934475)
          ·
            refine ⟨31092917966356658999901713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20728611977571105999934475 31092917966356658999901713)
            ·
              refine ⟨23319688474767494249926285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31092917966356658999901713 23319688474767494249926285)
              ·
                refine ⟨8744883178037810343722357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23319688474767494249926285 8744883178037810343722357)
                ·
                  refine ⟨819832797941044719723971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8744883178037810343722357 819832797941044719723971)
                  ·
                    refine ⟨1229749196911567079585957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 819832797941044719723971 1229749196911567079585957)
                    ·
                      refine ⟨230577974420918827422367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1229749196911567079585957 230577974420918827422367)
                      ·
                        rfl

theorem cell23_449049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_449049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449049 prefixEnd_449049 := by exact prefixLift 449049
  have htrace : WordTrace (prefixWord ++ tailWord_449049) baseStart_449049 baseEnd_449049 := by
    simpa [prefixWord, tailWord_449049, baseEnd_449049] using wordTrace_append hprefix tailTrace_449049
  have hstable : (prefixWord ++ tailWord_449049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449049).length < 2 ^ (prefixWord ++ tailWord_449049).sum := by decide
  have hdescent : baseEnd_449049 < baseStart_449049 := by decide
  rcases family_descends (prefixWord ++ tailWord_449049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449089 : List Nat := [1, 2, 5, 1, 1, 13]
def baseStart_449089 : Nat := 118140960795 + 449089 * 2 ^ 59
def prefixEnd_449089 : Nat := 4983230072969 + 3 ^ 40 * 449089 * 2
def baseEnd_449089 : Nat := 948965076737031567581

theorem tailTrace_449089 : CollatzResearch.WordTrace tailWord_449089 prefixEnd_449089 948965076737031567581 := by
  unfold tailWord_449089
  simp only [CollatzResearch.WordTrace]
  refine ⟨16379621470034726140046321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10919747646689817426697547 16379621470034726140046321)
  ·
    refine ⟨12284716102526044605034741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16379621470034726140046321 12284716102526044605034741)
    ·
      refine ⟨1151692134611816681722007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12284716102526044605034741 1151692134611816681722007)
      ·
        refine ⟨1727538201917725022583011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151692134611816681722007 1727538201917725022583011)
        ·
          refine ⟨2591307302876587533874517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727538201917725022583011 2591307302876587533874517)
          ·
            refine ⟨948965076737031567581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 2591307302876587533874517 948965076737031567581)
            ·
              rfl

theorem cell23_449089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 13].length) (baseStart_449089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449089 prefixEnd_449089 := by exact prefixLift 449089
  have htrace : WordTrace (prefixWord ++ tailWord_449089) baseStart_449089 baseEnd_449089 := by
    simpa [prefixWord, tailWord_449089, baseEnd_449089] using wordTrace_append hprefix tailTrace_449089
  have hstable : (prefixWord ++ tailWord_449089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449089).length < 2 ^ (prefixWord ++ tailWord_449089).sum := by decide
  have hdescent : baseEnd_449089 < baseStart_449089 := by decide
  rcases family_descends (prefixWord ++ tailWord_449089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449093 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 2, 4]
def baseStart_449093 : Nat := 118140960795 + 449093 * 2 ^ 59
def prefixEnd_449093 : Nat := 4983230072969 + 3 ^ 40 * 449093 * 2
def baseEnd_449093 : Nat := 76866855856572218424055

theorem tailTrace_449093 : CollatzResearch.WordTrace tailWord_449093 prefixEnd_449093 76866855856572218424055 := by
  unfold tailWord_449093
  simp only [CollatzResearch.WordTrace]
  refine ⟨16379767362020234823191933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10919844908013489882127955 16379767362020234823191933)
  ·
    refine ⟨6142412760757588058696975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16379767362020234823191933 6142412760757588058696975)
    ·
      refine ⟨9213619141136382088045463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6142412760757588058696975 9213619141136382088045463)
      ·
        refine ⟨13820428711704573132068195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9213619141136382088045463 13820428711704573132068195)
        ·
          refine ⟨20730643067556859698102293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13820428711704573132068195 20730643067556859698102293)
          ·
            refine ⟨971748893791727798348545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20730643067556859698102293 971748893791727798348545)
            ·
              refine ⟨728811670343795848761409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971748893791727798348545 728811670343795848761409)
              ·
                refine ⟨546608752757846886571057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728811670343795848761409 546608752757846886571057)
                ·
                  refine ⟨409956564568385164928293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546608752757846886571057 409956564568385164928293)
                  ·
                    refine ⟨76866855856572218424055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 409956564568385164928293 76866855856572218424055)
                    ·
                      rfl

theorem cell23_449093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_449093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449093 prefixEnd_449093 := by exact prefixLift 449093
  have htrace : WordTrace (prefixWord ++ tailWord_449093) baseStart_449093 baseEnd_449093 := by
    simpa [prefixWord, tailWord_449093, baseEnd_449093] using wordTrace_append hprefix tailTrace_449093
  have hstable : (prefixWord ++ tailWord_449093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449093).length < 2 ^ (prefixWord ++ tailWord_449093).sum := by decide
  have hdescent : baseEnd_449093 < baseStart_449093 := by decide
  rcases family_descends (prefixWord ++ tailWord_449093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449094 : List Nat := [6, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_449094 : Nat := 118140960795 + 449094 * 2 ^ 59
def prefixEnd_449094 : Nat := 4983230072969 + 3 ^ 40 * 449094 * 2
def baseEnd_449094 : Nat := 230601081050371151359661

theorem tailTrace_449094 : CollatzResearch.WordTrace tailWord_449094 prefixEnd_449094 230601081050371151359661 := by
  unfold tailWord_449094
  simp only [CollatzResearch.WordTrace]
  refine ⟨511868869844269124811823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10919869223344407995985557 511868869844269124811823)
  ·
    refine ⟨767803304766403687217735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 511868869844269124811823 767803304766403687217735)
    ·
      refine ⟨1151704957149605530826603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 767803304766403687217735 1151704957149605530826603)
      ·
        refine ⟨1727557435724408296239905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151704957149605530826603 1727557435724408296239905)
        ·
          refine ⟨1295668076793306222179929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1727557435724408296239905 1295668076793306222179929)
          ·
            refine ⟨971751057594979666634947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1295668076793306222179929 971751057594979666634947)
            ·
              refine ⟨1457626586392469499952421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971751057594979666634947 1457626586392469499952421)
              ·
                refine ⟨273304984948588031241079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1457626586392469499952421 273304984948588031241079)
                ·
                  refine ⟨409957477422882046861619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273304984948588031241079 409957477422882046861619)
                  ·
                    refine ⟨614936216134323070292429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 409957477422882046861619 614936216134323070292429)
                    ·
                      refine ⟨230601081050371151359661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 614936216134323070292429 230601081050371151359661)
                      ·
                        rfl

theorem cell23_449094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_449094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449094 prefixEnd_449094 := by exact prefixLift 449094
  have htrace : WordTrace (prefixWord ++ tailWord_449094) baseStart_449094 baseEnd_449094 := by
    simpa [prefixWord, tailWord_449094, baseEnd_449094] using wordTrace_append hprefix tailTrace_449094
  have hstable : (prefixWord ++ tailWord_449094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449094).length < 2 ^ (prefixWord ++ tailWord_449094).sum := by decide
  have hdescent : baseEnd_449094 < baseStart_449094 := by decide
  rcases family_descends (prefixWord ++ tailWord_449094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449109 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_449109 : Nat := 118140960795 + 449109 * 2 ^ 59
def prefixEnd_449109 : Nat := 4983230072969 + 3 ^ 40 * 449109 * 2
def baseEnd_449109 : Nat := 230608783260188592672091

theorem tailTrace_449109 : CollatzResearch.WordTrace tailWord_449109 prefixEnd_449109 230608783260188592672091 := by
  unfold tailWord_449109
  simp only [CollatzResearch.WordTrace]
  refine ⟨16380350929962269555774381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10920233953308179703849587 16380350929962269555774381)
  ·
    refine ⟨6142631598735851083415393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16380350929962269555774381 6142631598735851083415393)
    ·
      refine ⟨4606973699051888312561545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6142631598735851083415393 4606973699051888312561545)
      ·
        refine ⟨3455230274288916234421159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4606973699051888312561545 3455230274288916234421159)
        ·
          refine ⟨5182845411433374351631739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3455230274288916234421159 5182845411433374351631739)
          ·
            refine ⟨7774268117150061527447609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5182845411433374351631739 7774268117150061527447609)
            ·
              refine ⟨5830701087862546145585707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7774268117150061527447609 5830701087862546145585707)
              ·
                refine ⟨8746051631793819218378561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5830701087862546145585707 8746051631793819218378561)
                ·
                  refine ⟨6559538723845364413783921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8746051631793819218378561 6559538723845364413783921)
                  ·
                    refine ⟨4919654042884023310337941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6559538723845364413783921 4919654042884023310337941)
                    ·
                      refine ⟨230608783260188592672091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4919654042884023310337941 230608783260188592672091)
                      ·
                        rfl

theorem cell23_449109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_449109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449109 prefixEnd_449109 := by exact prefixLift 449109
  have htrace : WordTrace (prefixWord ++ tailWord_449109) baseStart_449109 baseEnd_449109 := by
    simpa [prefixWord, tailWord_449109, baseEnd_449109] using wordTrace_append hprefix tailTrace_449109
  have hstable : (prefixWord ++ tailWord_449109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449109).length < 2 ^ (prefixWord ++ tailWord_449109).sum := by decide
  have hdescent : baseEnd_449109 < baseStart_449109 := by decide
  rcases family_descends (prefixWord ++ tailWord_449109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449129 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_449129 : Nat := 118140960795 + 449129 * 2 ^ 59
def prefixEnd_449129 : Nat := 4983230072969 + 3 ^ 40 * 449129 * 2
def baseEnd_449129 : Nat := 230619052873278514421999

theorem tailTrace_449129 : CollatzResearch.WordTrace tailWord_449129 prefixEnd_449129 230619052873278514421999 := by
  unfold tailWord_449129
  simp only [CollatzResearch.WordTrace]
  refine ⟨16381080389889812971502441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10920720259926541981001627 16381080389889812971502441)
  ·
    refine ⟨12285810292417359728626831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16381080389889812971502441 12285810292417359728626831)
    ·
      refine ⟨18428715438626039592940247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12285810292417359728626831 18428715438626039592940247)
      ·
        refine ⟨27643073157939059389410371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18428715438626039592940247 27643073157939059389410371)
        ·
          refine ⟨41464609736908589084115557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27643073157939059389410371 41464609736908589084115557)
          ·
            refine ⟨7774614325670360453271667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41464609736908589084115557 7774614325670360453271667)
            ·
              refine ⟨11661921488505540679907501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7774614325670360453271667 11661921488505540679907501)
              ·
                refine ⟨4373220558189577754965313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11661921488505540679907501 4373220558189577754965313)
                ·
                  refine ⟨3279915418642183316223985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4373220558189577754965313 3279915418642183316223985)
                  ·
                    refine ⟨2459936563981637487167989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3279915418642183316223985 2459936563981637487167989)
                    ·
                      refine ⟨230619052873278514421999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2459936563981637487167989 230619052873278514421999)
                      ·
                        rfl

theorem cell23_449129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_449129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449129 prefixEnd_449129 := by exact prefixLift 449129
  have htrace : WordTrace (prefixWord ++ tailWord_449129) baseStart_449129 baseEnd_449129 := by
    simpa [prefixWord, tailWord_449129, baseEnd_449129] using wordTrace_append hprefix tailTrace_449129
  have hstable : (prefixWord ++ tailWord_449129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449129).length < 2 ^ (prefixWord ++ tailWord_449129).sum := by decide
  have hdescent : baseEnd_449129 < baseStart_449129 := by decide
  rcases family_descends (prefixWord ++ tailWord_449129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449133 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_449133 : Nat := 118140960795 + 449133 * 2 ^ 59
def prefixEnd_449133 : Nat := 4983230072969 + 3 ^ 40 * 449133 * 2
def baseEnd_449133 : Nat := 230621106795896498771981

theorem tailTrace_449133 : CollatzResearch.WordTrace tailWord_449133 prefixEnd_449133 230621106795896498771981 := by
  unfold tailWord_449133
  simp only [CollatzResearch.WordTrace]
  refine ⟨16381226281875321654648053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10920817521250214436432035 16381226281875321654648053)
  ·
    refine ⟨1535739963925811405123255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16381226281875321654648053 1535739963925811405123255)
    ·
      refine ⟨2303609945888717107684883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1535739963925811405123255 2303609945888717107684883)
      ·
        refine ⟨3455414918833075661527325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303609945888717107684883 3455414918833075661527325)
        ·
          refine ⟨1295780594562403373072747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3455414918833075661527325 1295780594562403373072747)
          ·
            refine ⟨1943670891843605059609121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295780594562403373072747 1943670891843605059609121)
            ·
              refine ⟨1457753168882703794706841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1943670891843605059609121 1457753168882703794706841)
              ·
                refine ⟨1093314876662027846030131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1457753168882703794706841 1093314876662027846030131)
                ·
                  refine ⟨1639972314993041769045197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093314876662027846030131 1639972314993041769045197)
                  ·
                    refine ⟨614989618122390663391949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1639972314993041769045197 614989618122390663391949)
                    ·
                      refine ⟨230621106795896498771981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 614989618122390663391949 230621106795896498771981)
                      ·
                        rfl

theorem cell23_449133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_449133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449133 prefixEnd_449133 := by exact prefixLift 449133
  have htrace : WordTrace (prefixWord ++ tailWord_449133) baseStart_449133 baseEnd_449133 := by
    simpa [prefixWord, tailWord_449133, baseEnd_449133] using wordTrace_append hprefix tailTrace_449133
  have hstable : (prefixWord ++ tailWord_449133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449133).length < 2 ^ (prefixWord ++ tailWord_449133).sum := by decide
  have hdescent : baseEnd_449133 < baseStart_449133 := by decide
  rcases family_descends (prefixWord ++ tailWord_449133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449134 : List Nat := [4, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_449134 : Nat := 118140960795 + 449134 * 2 ^ 59
def prefixEnd_449134 : Nat := 4983230072969 + 3 ^ 40 * 449134 * 2
def baseEnd_449134 : Nat := 230621620276550994859477

theorem tailTrace_449134 : CollatzResearch.WordTrace tailWord_449134 prefixEnd_449134 230621620276550994859477 := by
  unfold tailWord_449134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047657844358962353179307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10920841836581132550289637 2047657844358962353179307)
  ·
    refine ⟨3071486766538443529768961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2047657844358962353179307 3071486766538443529768961)
    ·
      refine ⟨2303615074903832647326721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3071486766538443529768961 2303615074903832647326721)
      ·
        refine ⟨1727711306177874485495041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2303615074903832647326721 1727711306177874485495041)
        ·
          refine ⟨1295783479633405864121281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1727711306177874485495041 1295783479633405864121281)
          ·
            refine ⟨971837609725054398090961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1295783479633405864121281 971837609725054398090961)
            ·
              refine ⟨728878207293790798568221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971837609725054398090961 728878207293790798568221)
              ·
                refine ⟨273329327735171549463083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 728878207293790798568221 273329327735171549463083)
                ·
                  refine ⟨409993991602757324194625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273329327735171549463083 409993991602757324194625)
                  ·
                    refine ⟨307495493702067993145969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 409993991602757324194625 307495493702067993145969)
                    ·
                      refine ⟨230621620276550994859477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 307495493702067993145969 230621620276550994859477)
                      ·
                        rfl

theorem cell23_449134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_449134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449134 prefixEnd_449134 := by exact prefixLift 449134
  have htrace : WordTrace (prefixWord ++ tailWord_449134) baseStart_449134 baseEnd_449134 := by
    simpa [prefixWord, tailWord_449134, baseEnd_449134] using wordTrace_append hprefix tailTrace_449134
  have hstable : (prefixWord ++ tailWord_449134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449134).length < 2 ^ (prefixWord ++ tailWord_449134).sum := by decide
  have hdescent : baseEnd_449134 < baseStart_449134 := by decide
  rcases family_descends (prefixWord ++ tailWord_449134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449139 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 4]
def baseStart_449139 : Nat := 118140960795 + 449139 * 2 ^ 59
def prefixEnd_449139 : Nat := 4983230072969 + 3 ^ 40 * 449139 * 2
def baseEnd_449139 : Nat := 230624187679823475296953

theorem tailTrace_449139 : CollatzResearch.WordTrace tailWord_449139 prefixEnd_449139 230624187679823475296953 := by
  unfold tailWord_449139
  simp only [CollatzResearch.WordTrace]
  refine ⟨16381445119853584679366471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10920963413235723119577647 16381445119853584679366471)
  ·
    refine ⟨24572167679780377019049707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16381445119853584679366471 24572167679780377019049707)
    ·
      refine ⟨36858251519670565528574561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24572167679780377019049707 36858251519670565528574561)
      ·
        refine ⟨27643688639752924146430921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36858251519670565528574561 27643688639752924146430921)
        ·
          refine ⟨20732766479814693109823191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27643688639752924146430921 20732766479814693109823191)
          ·
            refine ⟨31099149719722039664734787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20732766479814693109823191 31099149719722039664734787)
            ·
              refine ⟨46648724579583059497102181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31099149719722039664734787 46648724579583059497102181)
              ·
                refine ⟨8746635858671823655706659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46648724579583059497102181 8746635858671823655706659)
                ·
                  refine ⟨13119953788007735483559989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8746635858671823655706659 13119953788007735483559989)
                  ·
                    refine ⟨1229995667625725201583749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13119953788007735483559989 1229995667625725201583749)
                    ·
                      refine ⟨230624187679823475296953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1229995667625725201583749 230624187679823475296953)
                      ·
                        rfl

theorem cell23_449139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_449139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449139 prefixEnd_449139 := by exact prefixLift 449139
  have htrace : WordTrace (prefixWord ++ tailWord_449139) baseStart_449139 baseEnd_449139 := by
    simpa [prefixWord, tailWord_449139, baseEnd_449139] using wordTrace_append hprefix tailTrace_449139
  have hstable : (prefixWord ++ tailWord_449139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449139).length < 2 ^ (prefixWord ++ tailWord_449139).sum := by decide
  have hdescent : baseEnd_449139 < baseStart_449139 := by decide
  rcases family_descends (prefixWord ++ tailWord_449139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449166 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_449166 : Nat := 118140960795 + 449166 * 2 ^ 59
def prefixEnd_449166 : Nat := 4983230072969 + 3 ^ 40 * 449166 * 2
def baseEnd_449166 : Nat := 76879350552498289886443

theorem tailTrace_449166 : CollatzResearch.WordTrace tailWord_449166 prefixEnd_449166 76879350552498289886443 := by
  unfold tailWord_449166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047803736344471036324919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10921619927170512193732901 2047803736344471036324919)
  ·
    refine ⟨3071705604516706554487379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2047803736344471036324919 3071705604516706554487379)
    ·
      refine ⟨4607558406775059831731069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3071705604516706554487379 4607558406775059831731069)
      ·
        refine ⟨1727834402540647436899151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4607558406775059831731069 1727834402540647436899151)
        ·
          refine ⟨2591751603810971155348727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727834402540647436899151 2591751603810971155348727)
          ·
            refine ⟨3887627405716456733023091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591751603810971155348727 3887627405716456733023091)
            ·
              refine ⟨5831441108574685099534637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3887627405716456733023091 5831441108574685099534637)
              ·
                refine ⟨2186790415715506912325489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5831441108574685099534637 2186790415715506912325489)
                ·
                  refine ⟨1640092811786630184244117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2186790415715506912325489 1640092811786630184244117)
                  ·
                    refine ⟨76879350552498289886443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1640092811786630184244117 76879350552498289886443)
                    ·
                      rfl

theorem cell23_449166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_449166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449166 prefixEnd_449166 := by exact prefixLift 449166
  have htrace : WordTrace (prefixWord ++ tailWord_449166) baseStart_449166 baseEnd_449166 := by
    simpa [prefixWord, tailWord_449166, baseEnd_449166] using wordTrace_append hprefix tailTrace_449166
  have hstable : (prefixWord ++ tailWord_449166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449166).length < 2 ^ (prefixWord ++ tailWord_449166).sum := by decide
  have hdescent : baseEnd_449166 < baseStart_449166 := by decide
  rcases family_descends (prefixWord ++ tailWord_449166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449176 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_449176 : Nat := 118140960795 + 449176 * 2 ^ 59
def prefixEnd_449176 : Nat := 4983230072969 + 3 ^ 40 * 449176 * 2
def baseEnd_449176 : Nat := 230643186464039830534283

theorem tailTrace_449176 : CollatzResearch.WordTrace tailWord_449176 prefixEnd_449176 230643186464039830534283 := by
  unfold tailWord_449176
  simp only [CollatzResearch.WordTrace]
  refine ⟨8191397310359769999231691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10921863080479693332308921 8191397310359769999231691)
  ·
    refine ⟨12287095965539654998847537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8191397310359769999231691 12287095965539654998847537)
    ·
      refine ⟨9215321974154741249135653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12287095965539654998847537 9215321974154741249135653)
      ·
        refine ⟨1727872870154013984212935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9215321974154741249135653 1727872870154013984212935)
        ·
          refine ⟨2591809305231020976319403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1727872870154013984212935 2591809305231020976319403)
          ·
            refine ⟨3887713957846531464479105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591809305231020976319403 3887713957846531464479105)
            ·
              refine ⟨2915785468384898598359329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3887713957846531464479105 2915785468384898598359329)
              ·
                refine ⟨2186839101288673948769497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915785468384898598359329 2186839101288673948769497)
                ·
                  refine ⟨1640129325966505461577123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2186839101288673948769497 1640129325966505461577123)
                  ·
                    refine ⟨2460193988949758192365685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1640129325966505461577123 2460193988949758192365685)
                    ·
                      refine ⟨230643186464039830534283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2460193988949758192365685 230643186464039830534283)
                      ·
                        rfl

theorem cell23_449176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_449176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449176 prefixEnd_449176 := by exact prefixLift 449176
  have htrace : WordTrace (prefixWord ++ tailWord_449176) baseStart_449176 baseEnd_449176 := by
    simpa [prefixWord, tailWord_449176, baseEnd_449176] using wordTrace_append hprefix tailTrace_449176
  have hstable : (prefixWord ++ tailWord_449176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449176).length < 2 ^ (prefixWord ++ tailWord_449176).sum := by decide
  have hdescent : baseEnd_449176 < baseStart_449176 := by decide
  rcases family_descends (prefixWord ++ tailWord_449176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449213 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 7]
def baseStart_449213 : Nat := 118140960795 + 449213 * 2 ^ 59
def prefixEnd_449213 : Nat := 4983230072969 + 3 ^ 40 * 449213 * 2
def baseEnd_449213 : Nat := 25629131694250687307957

theorem tailTrace_449213 : CollatzResearch.WordTrace tailWord_449213 prefixEnd_449213 25629131694250687307957 := by
  unfold tailWord_449213
  simp only [CollatzResearch.WordTrace]
  refine ⟨16384144121585495317560293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10922762747723663545040195 16384144121585495317560293)
  ·
    refine ⟨3072027022797280372042555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16384144121585495317560293 3072027022797280372042555)
    ·
      refine ⟨4608040534195920558063833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3072027022797280372042555 4608040534195920558063833)
      ·
        refine ⟨3456030400646940418547875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4608040534195920558063833 3456030400646940418547875)
        ·
          refine ⟨5184045600970410627821813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3456030400646940418547875 5184045600970410627821813)
          ·
            refine ⟨486004275090975996358295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5184045600970410627821813 486004275090975996358295)
            ·
              refine ⟨729006412636463994537443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486004275090975996358295 729006412636463994537443)
              ·
                refine ⟨1093509618954695991806165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729006412636463994537443 1093509618954695991806165)
                ·
                  refine ⟨25629131694250687307957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1093509618954695991806165 25629131694250687307957)
                  ·
                    rfl

theorem cell23_449213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_449213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449213 prefixEnd_449213 := by exact prefixLift 449213
  have htrace : WordTrace (prefixWord ++ tailWord_449213) baseStart_449213 baseEnd_449213 := by
    simpa [prefixWord, tailWord_449213, baseEnd_449213] using wordTrace_append hprefix tailTrace_449213
  have hstable : (prefixWord ++ tailWord_449213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449213).length < 2 ^ (prefixWord ++ tailWord_449213).sum := by decide
  have hdescent : baseEnd_449213 < baseStart_449213 := by decide
  rcases family_descends (prefixWord ++ tailWord_449213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449224 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 2, 2, 2]
def baseStart_449224 : Nat := 118140960795 + 449224 * 2 ^ 59
def prefixEnd_449224 : Nat := 4983230072969 + 3 ^ 40 * 449224 * 2
def baseEnd_449224 : Nat := 230667833535455642734063

theorem tailTrace_449224 : CollatzResearch.WordTrace tailWord_449224 prefixEnd_449224 230667833535455642734063 := by
  unfold tailWord_449224
  simp only [CollatzResearch.WordTrace]
  refine ⟨8192272662272822098105363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10923030216363762797473817 8192272662272822098105363)
  ·
    refine ⟨12288408993409233147158045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8192272662272822098105363 12288408993409233147158045)
    ·
      refine ⟨4608153372528462430184267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12288408993409233147158045 4608153372528462430184267)
      ·
        refine ⟨6912230058792693645276401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4608153372528462430184267 6912230058792693645276401)
        ·
          refine ⟨5184172544094520233957301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6912230058792693645276401 5184172544094520233957301)
          ·
            refine ⟨486016176008861271933497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5184172544094520233957301 486016176008861271933497)
            ·
              refine ⟨364512132006645953950123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486016176008861271933497 364512132006645953950123)
              ·
                refine ⟨546768198009968930925185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364512132006645953950123 546768198009968930925185)
                ·
                  refine ⟨410076148507476698193889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546768198009968930925185 410076148507476698193889)
                  ·
                    refine ⟨307557111380607523645417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 410076148507476698193889 307557111380607523645417)
                    ·
                      refine ⟨230667833535455642734063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 307557111380607523645417 230667833535455642734063)
                      ·
                        rfl

theorem cell23_449224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_449224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449224 prefixEnd_449224 := by exact prefixLift 449224
  have htrace : WordTrace (prefixWord ++ tailWord_449224) baseStart_449224 baseEnd_449224 := by
    simpa [prefixWord, tailWord_449224, baseEnd_449224] using wordTrace_append hprefix tailTrace_449224
  have hstable : (prefixWord ++ tailWord_449224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449224).length < 2 ^ (prefixWord ++ tailWord_449224).sum := by decide
  have hdescent : baseEnd_449224 < baseStart_449224 := by decide
  rcases family_descends (prefixWord ++ tailWord_449224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449263 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 4]
def baseStart_449263 : Nat := 118140960795 + 449263 * 2 ^ 59
def prefixEnd_449263 : Nat := 4983230072969 + 3 ^ 40 * 449263 * 2
def baseEnd_449263 : Nat := 230687859280980990146383

theorem tailTrace_449263 : CollatzResearch.WordTrace tailWord_449263 prefixEnd_449263 230687859280980990146383 := by
  unfold tailWord_449263
  simp only [CollatzResearch.WordTrace]
  refine ⟨16385967771404353856880443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10923978514269569237920295 16385967771404353856880443)
  ·
    refine ⟨24578951657106530785320665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16385967771404353856880443 24578951657106530785320665)
    ·
      refine ⟨18434213742829898088990499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24578951657106530785320665 18434213742829898088990499)
      ·
        refine ⟨27651320614244847133485749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18434213742829898088990499 27651320614244847133485749)
        ·
          refine ⟨2592311307585454418764289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27651320614244847133485749 2592311307585454418764289)
          ·
            refine ⟨1944233480689090814073217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2592311307585454418764289 1944233480689090814073217)
            ·
              refine ⟨1458175110516818110554913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944233480689090814073217 1458175110516818110554913)
              ·
                refine ⟨1093631332887613582916185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1458175110516818110554913 1093631332887613582916185)
                ·
                  refine ⟨820223499665710187187139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1093631332887613582916185 820223499665710187187139)
                  ·
                    refine ⟨1230335249498565280780709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 820223499665710187187139 1230335249498565280780709)
                    ·
                      refine ⟨230687859280980990146383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1230335249498565280780709 230687859280980990146383)
                      ·
                        rfl

theorem cell23_449263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_449263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449263 prefixEnd_449263 := by exact prefixLift 449263
  have htrace : WordTrace (prefixWord ++ tailWord_449263) baseStart_449263 baseEnd_449263 := by
    simpa [prefixWord, tailWord_449263, baseEnd_449263] using wordTrace_append hprefix tailTrace_449263
  have hstable : (prefixWord ++ tailWord_449263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449263).length < 2 ^ (prefixWord ++ tailWord_449263).sum := by decide
  have hdescent : baseEnd_449263 < baseStart_449263 := by decide
  rcases family_descends (prefixWord ++ tailWord_449263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449323 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 3, 5, 2]
def baseStart_449323 : Nat := 118140960795 + 449323 * 2 ^ 59
def prefixEnd_449323 : Nat := 4983230072969 + 3 ^ 40 * 449323 * 2
def baseEnd_449323 : Nat := 230718668120250755396107

theorem tailTrace_449323 : CollatzResearch.WordTrace tailWord_449323 prefixEnd_449323 230718668120250755396107 := by
  unfold tailWord_449323
  simp only [CollatzResearch.WordTrace]
  refine ⟨16388156151186984104064623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10925437434124656069376415 16388156151186984104064623)
  ·
    refine ⟨24582234226780476156096935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16388156151186984104064623 24582234226780476156096935)
    ·
      refine ⟨36873351340170714234145403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24582234226780476156096935 36873351340170714234145403)
      ·
        refine ⟨55310027010256071351218105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36873351340170714234145403 55310027010256071351218105)
        ·
          refine ⟨41482520257692053513413579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55310027010256071351218105 41482520257692053513413579)
          ·
            refine ⟨62223780386538080270120369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41482520257692053513413579 62223780386538080270120369)
            ·
              refine ⟨46667835289903560202590277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62223780386538080270120369 46667835289903560202590277)
              ·
                refine ⟨8750219116856917537985677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46667835289903560202590277 8750219116856917537985677)
                ·
                  refine ⟨3281332168821344076744629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8750219116856917537985677 3281332168821344076744629)
                  ·
                    refine ⟨307624890827001007194809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3281332168821344076744629 307624890827001007194809)
                    ·
                      refine ⟨230718668120250755396107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 307624890827001007194809 230718668120250755396107)
                      ·
                        rfl

theorem cell23_449323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 5, 2].length) (baseStart_449323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449323 prefixEnd_449323 := by exact prefixLift 449323
  have htrace : WordTrace (prefixWord ++ tailWord_449323) baseStart_449323 baseEnd_449323 := by
    simpa [prefixWord, tailWord_449323, baseEnd_449323] using wordTrace_append hprefix tailTrace_449323
  have hstable : (prefixWord ++ tailWord_449323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449323).length < 2 ^ (prefixWord ++ tailWord_449323).sum := by decide
  have hdescent : baseEnd_449323 < baseStart_449323 := by decide
  rcases family_descends (prefixWord ++ tailWord_449323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449370 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4]
def baseStart_449370 : Nat := 118140960795 + 449370 * 2 ^ 59
def prefixEnd_449370 : Nat := 4983230072969 + 3 ^ 40 * 449370 * 2
def baseEnd_449370 : Nat := 230742801711012071508391

theorem tailTrace_449370 : CollatzResearch.WordTrace tailWord_449370 prefixEnd_449370 230742801711012071508391 := by
  unfold tailWord_449370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4097467595504177782756391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10926580254677807420683709 4097467595504177782756391)
  ·
    refine ⟨6146201393256266674134587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4097467595504177782756391 6146201393256266674134587)
    ·
      refine ⟨9219302089884400011201881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6146201393256266674134587 9219302089884400011201881)
      ·
        refine ⟨6914476567413300008401411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9219302089884400011201881 6914476567413300008401411)
        ·
          refine ⟨10371714851119950012602117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6914476567413300008401411 10371714851119950012602117)
          ·
            refine ⟨1944696534584990627362897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10371714851119950012602117 1944696534584990627362897)
            ·
              refine ⟨1458522400938742970522173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944696534584990627362897 1458522400938742970522173)
              ·
                refine ⟨546945900352028613945815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1458522400938742970522173 546945900352028613945815)
                ·
                  refine ⟨820418850528042920918723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546945900352028613945815 820418850528042920918723)
                  ·
                    refine ⟨1230628275792064381378085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 820418850528042920918723 1230628275792064381378085)
                    ·
                      refine ⟨230742801711012071508391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1230628275792064381378085 230742801711012071508391)
                      ·
                        rfl

theorem cell23_449370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_449370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449370 prefixEnd_449370 := by exact prefixLift 449370
  have htrace : WordTrace (prefixWord ++ tailWord_449370) baseStart_449370 baseEnd_449370 := by
    simpa [prefixWord, tailWord_449370, baseEnd_449370] using wordTrace_append hprefix tailTrace_449370
  have hstable : (prefixWord ++ tailWord_449370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449370).length < 2 ^ (prefixWord ++ tailWord_449370).sum := by decide
  have hdescent : baseEnd_449370 < baseStart_449370 := by decide
  rcases family_descends (prefixWord ++ tailWord_449370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449380 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_449380 : Nat := 118140960795 + 449380 * 2 ^ 59
def prefixEnd_449380 : Nat := 4983230072969 + 3 ^ 40 * 449380 * 2
def baseEnd_449380 : Nat := 76915978839185677461115

theorem tailTrace_449380 : CollatzResearch.WordTrace tailWord_449380 prefixEnd_449380 76915978839185677461115 := by
  unfold tailWord_449380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195117555990241419444797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10926823407986988559259729 8195117555990241419444797)
  ·
    refine ⟨3073169083496340532291799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8195117555990241419444797 3073169083496340532291799)
    ·
      refine ⟨4609753625244510798437699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3073169083496340532291799 4609753625244510798437699)
      ·
        refine ⟨6914630437866766197656549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4609753625244510798437699 6914630437866766197656549)
        ·
          refine ⟨1296493207100018662060603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6914630437866766197656549 1296493207100018662060603)
          ·
            refine ⟨1944739810650027993090905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296493207100018662060603 1944739810650027993090905)
            ·
              refine ⟨1458554857987520994818179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944739810650027993090905 1458554857987520994818179)
              ·
                refine ⟨2187832286981281492227269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458554857987520994818179 2187832286981281492227269)
                ·
                  refine ⟨410218553808990279792613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2187832286981281492227269 410218553808990279792613)
                  ·
                    refine ⟨76915978839185677461115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 410218553808990279792613 76915978839185677461115)
                    ·
                      rfl

theorem cell23_449380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_449380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449380 prefixEnd_449380 := by exact prefixLift 449380
  have htrace : WordTrace (prefixWord ++ tailWord_449380) baseStart_449380 baseEnd_449380 := by
    simpa [prefixWord, tailWord_449380, baseEnd_449380] using wordTrace_append hprefix tailTrace_449380
  have hstable : (prefixWord ++ tailWord_449380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449380).length < 2 ^ (prefixWord ++ tailWord_449380).sum := by decide
  have hdescent : baseEnd_449380 < baseStart_449380 := by decide
  rcases family_descends (prefixWord ++ tailWord_449380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449383 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_449383 : Nat := 118140960795 + 449383 * 2 ^ 59
def prefixEnd_449383 : Nat := 4983230072969 + 3 ^ 40 * 449383 * 2
def baseEnd_449383 : Nat := 230749476959520520645831

theorem tailTrace_449383 : CollatzResearch.WordTrace tailWord_449383 prefixEnd_449383 230749476959520520645831 := by
  unfold tailWord_449383
  simp only [CollatzResearch.WordTrace]
  refine ⟨16390344530969614351248803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10926896353979742900832535 16390344530969614351248803)
  ·
    refine ⟨24585516796454421526873205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16390344530969614351248803 24585516796454421526873205)
    ·
      refine ⟨2304892199667602018144363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24585516796454421526873205 2304892199667602018144363)
      ·
        refine ⟨3457338299501403027216545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2304892199667602018144363 3457338299501403027216545)
        ·
          refine ⟨2593003724626052270412409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3457338299501403027216545 2593003724626052270412409)
          ·
            refine ⟨1944752793469539202809307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2593003724626052270412409 1944752793469539202809307)
            ·
              refine ⟨2917129190204308804213961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944752793469539202809307 2917129190204308804213961)
              ·
                refine ⟨2187846892653231603160471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2917129190204308804213961 2187846892653231603160471)
                ·
                  refine ⟨3281770338979847404740707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187846892653231603160471 3281770338979847404740707)
                  ·
                    refine ⟨4922655508469771107111061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3281770338979847404740707 4922655508469771107111061)
                    ·
                      refine ⟨230749476959520520645831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4922655508469771107111061 230749476959520520645831)
                      ·
                        rfl

theorem cell23_449383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_449383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449383 prefixEnd_449383 := by exact prefixLift 449383
  have htrace : WordTrace (prefixWord ++ tailWord_449383) baseStart_449383 baseEnd_449383 := by
    simpa [prefixWord, tailWord_449383, baseEnd_449383] using wordTrace_append hprefix tailTrace_449383
  have hstable : (prefixWord ++ tailWord_449383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449383).length < 2 ^ (prefixWord ++ tailWord_449383).sum := by decide
  have hdescent : baseEnd_449383 < baseStart_449383 := by decide
  rcases family_descends (prefixWord ++ tailWord_449383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449387 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 3, 2, 2]
def baseStart_449387 : Nat := 118140960795 + 449387 * 2 ^ 59
def prefixEnd_449387 : Nat := 4983230072969 + 3 ^ 40 * 449387 * 2
def baseEnd_449387 : Nat := 230751530882138504995813

theorem tailTrace_449387 : CollatzResearch.WordTrace tailWord_449387 prefixEnd_449387 230751530882138504995813 := by
  unfold tailWord_449387
  simp only [CollatzResearch.WordTrace]
  refine ⟨16390490422955123034394415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10926993615303415356262943 16390490422955123034394415)
  ·
    refine ⟨24585735634432684551591623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16390490422955123034394415 24585735634432684551591623)
    ·
      refine ⟨36878603451649026827387435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24585735634432684551591623 36878603451649026827387435)
      ·
        refine ⟨55317905177473540241081153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36878603451649026827387435 55317905177473540241081153)
        ·
          refine ⟨41488428883105155180810865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55317905177473540241081153 41488428883105155180810865)
          ·
            refine ⟨31116321662328866385608149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41488428883105155180810865 31116321662328866385608149)
            ·
              refine ⟨729288788960832805912691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31116321662328866385608149 729288788960832805912691)
              ·
                refine ⟨1093933183441249208869037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729288788960832805912691 1093933183441249208869037)
                ·
                  refine ⟨410224943790468453325889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1093933183441249208869037 410224943790468453325889)
                  ·
                    refine ⟨307668707842851339994417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 410224943790468453325889 307668707842851339994417)
                    ·
                      refine ⟨230751530882138504995813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 307668707842851339994417 230751530882138504995813)
                      ·
                        rfl

theorem cell23_449387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 2, 2].length) (baseStart_449387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449387 prefixEnd_449387 := by exact prefixLift 449387
  have htrace : WordTrace (prefixWord ++ tailWord_449387) baseStart_449387 baseEnd_449387 := by
    simpa [prefixWord, tailWord_449387, baseEnd_449387] using wordTrace_append hprefix tailTrace_449387
  have hstable : (prefixWord ++ tailWord_449387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449387).length < 2 ^ (prefixWord ++ tailWord_449387).sum := by decide
  have hdescent : baseEnd_449387 < baseStart_449387 := by decide
  rcases family_descends (prefixWord ++ tailWord_449387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449393 : List Nat := [1, 2, 2, 2, 1, 5, 2, 8]
def baseStart_449393 : Nat := 118140960795 + 449393 * 2 ^ 59
def prefixEnd_449393 : Nat := 4983230072969 + 3 ^ 40 * 449393 * 2
def baseEnd_449393 : Nat := 8546467102446869685955

theorem tailTrace_449393 : CollatzResearch.WordTrace tailWord_449393 prefixEnd_449393 8546467102446869685955 := by
  unfold tailWord_449393
  simp only [CollatzResearch.WordTrace]
  refine ⟨16390709260933386059112833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10927139507288924039408555 16390709260933386059112833)
  ·
    refine ⟨12293031945700039544334625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16390709260933386059112833 12293031945700039544334625)
    ·
      refine ⟨9219773959275029658250969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12293031945700039544334625 9219773959275029658250969)
      ·
        refine ⟨6914830469456272243688227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9219773959275029658250969 6914830469456272243688227)
        ·
          refine ⟨10372245704184408365532341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6914830469456272243688227 10372245704184408365532341)
          ·
            refine ⟨972398034767288284268657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10372245704184408365532341 972398034767288284268657)
            ·
              refine ⟨729298526075466213201493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972398034767288284268657 729298526075466213201493)
              ·
                refine ⟨8546467102446869685955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 729298526075466213201493 8546467102446869685955)
                ·
                  rfl

theorem cell23_449393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 8].length) (baseStart_449393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449393 prefixEnd_449393 := by exact prefixLift 449393
  have htrace : WordTrace (prefixWord ++ tailWord_449393) baseStart_449393 baseEnd_449393 := by
    simpa [prefixWord, tailWord_449393, baseEnd_449393] using wordTrace_append hprefix tailTrace_449393
  have hstable : (prefixWord ++ tailWord_449393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449393).length < 2 ^ (prefixWord ++ tailWord_449393).sum := by decide
  have hdescent : baseEnd_449393 < baseStart_449393 := by decide
  rcases family_descends (prefixWord ++ tailWord_449393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449397 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 2, 4]
def baseStart_449397 : Nat := 118140960795 + 449397 * 2 ^ 59
def prefixEnd_449397 : Nat := 4983230072969 + 3 ^ 40 * 449397 * 2
def baseEnd_449397 : Nat := 76918888562894488623589

theorem tailTrace_449397 : CollatzResearch.WordTrace tailWord_449397 prefixEnd_449397 76918888562894488623589 := by
  unfold tailWord_449397
  simp only [CollatzResearch.WordTrace]
  refine ⟨16390855152918894742258445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10927236768612596494838963 16390855152918894742258445)
  ·
    refine ⟨6146570682344585528346917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16390855152918894742258445 6146570682344585528346917)
    ·
      refine ⟨1152482002939609786565047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6146570682344585528346917 1152482002939609786565047)
      ·
        refine ⟨1728723004409414679847571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152482002939609786565047 1728723004409414679847571)
        ·
          refine ⟨2593084506614122019771357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728723004409414679847571 2593084506614122019771357)
          ·
            refine ⟨972406689980295757414259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2593084506614122019771357 972406689980295757414259)
            ·
              refine ⟨1458610034970443636121389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972406689980295757414259 1458610034970443636121389)
              ·
                refine ⟨546978763113916363545521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1458610034970443636121389 546978763113916363545521)
                ·
                  refine ⟨410234072335437272659141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 546978763113916363545521 410234072335437272659141)
                  ·
                    refine ⟨76918888562894488623589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 410234072335437272659141 76918888562894488623589)
                    ·
                      rfl

theorem cell23_449397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_449397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449397 prefixEnd_449397 := by exact prefixLift 449397
  have htrace : WordTrace (prefixWord ++ tailWord_449397) baseStart_449397 baseEnd_449397 := by
    simpa [prefixWord, tailWord_449397, baseEnd_449397] using wordTrace_append hprefix tailTrace_449397
  have hstable : (prefixWord ++ tailWord_449397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449397).length < 2 ^ (prefixWord ++ tailWord_449397).sum := by decide
  have hdescent : baseEnd_449397 < baseStart_449397 := by decide
  rcases family_descends (prefixWord ++ tailWord_449397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449420 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 6, 1, 3]
def baseStart_449420 : Nat := 118140960795 + 449420 * 2 ^ 59
def prefixEnd_449420 : Nat := 4983230072969 + 3 ^ 40 * 449420 * 2
def baseEnd_449420 : Nat := 230768475743736875883161

theorem tailTrace_449420 : CollatzResearch.WordTrace tailWord_449420 prefixEnd_449420 230768475743736875883161 := by
  unfold tailWord_449420
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195847015917784835172857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10927796021223713113563809 8195847015917784835172857)
  ·
    refine ⟨6146885261938338626379643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8195847015917784835172857 6146885261938338626379643)
    ·
      refine ⟨9220327892907507939569465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6146885261938338626379643 9220327892907507939569465)
      ·
        refine ⟨6915245919680630954677099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9220327892907507939569465 6915245919680630954677099)
        ·
          refine ⟨10372868879520946432015649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915245919680630954677099 10372868879520946432015649)
          ·
            refine ⟨7779651659640709824011737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10372868879520946432015649 7779651659640709824011737)
            ·
              refine ⟨5834738744730532368008803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7779651659640709824011737 5834738744730532368008803)
              ·
                refine ⟨8752108117095798552013205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5834738744730532368008803 8752108117095798552013205)
                ·
                  refine ⟨410255067988865557125619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8752108117095798552013205 410255067988865557125619)
                  ·
                    refine ⟨615382601983298335688429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 410255067988865557125619 615382601983298335688429)
                    ·
                      refine ⟨230768475743736875883161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 615382601983298335688429 230768475743736875883161)
                      ·
                        rfl

theorem cell23_449420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_449420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449420 prefixEnd_449420 := by exact prefixLift 449420
  have htrace : WordTrace (prefixWord ++ tailWord_449420) baseStart_449420 baseEnd_449420 := by
    simpa [prefixWord, tailWord_449420, baseEnd_449420] using wordTrace_append hprefix tailTrace_449420
  have hstable : (prefixWord ++ tailWord_449420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449420).length < 2 ^ (prefixWord ++ tailWord_449420).sum := by decide
  have hdescent : baseEnd_449420 < baseStart_449420 := by decide
  rcases family_descends (prefixWord ++ tailWord_449420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449443 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 4]
def baseStart_449443 : Nat := 118140960795 + 449443 * 2 ^ 59
def prefixEnd_449443 : Nat := 4983230072969 + 3 ^ 40 * 449443 * 2
def baseEnd_449443 : Nat := 230780285798790285895555

theorem tailTrace_449443 : CollatzResearch.WordTrace tailWord_449443 prefixEnd_449443 230780285798790285895555 := by
  unfold tailWord_449443
  simp only [CollatzResearch.WordTrace]
  refine ⟨16392532910752244598432983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10928355273834829732288655 16392532910752244598432983)
  ·
    refine ⟨24588799366128366897649475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16392532910752244598432983 24588799366128366897649475)
    ·
      refine ⟨36883199049192550346474213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24588799366128366897649475 36883199049192550346474213)
      ·
        refine ⟨6915599821723603189963915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36883199049192550346474213 6915599821723603189963915)
        ·
          refine ⟨10373399732585404784945873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915599821723603189963915 10373399732585404784945873)
          ·
            refine ⟨7780049799439053588709405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10373399732585404784945873 7780049799439053588709405)
            ·
              refine ⟨2917518674789645095766027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7780049799439053588709405 2917518674789645095766027)
              ·
                refine ⟨4376278012184467643649041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2917518674789645095766027 4376278012184467643649041)
                ·
                  refine ⟨3282208509138350732736781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4376278012184467643649041 3282208509138350732736781)
                  ·
                    refine ⟨1230828190926881524776293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3282208509138350732736781 1230828190926881524776293)
                    ·
                      refine ⟨230780285798790285895555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1230828190926881524776293 230780285798790285895555)
                      ·
                        rfl

theorem cell23_449443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_449443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449443 prefixEnd_449443 := by exact prefixLift 449443
  have htrace : WordTrace (prefixWord ++ tailWord_449443) baseStart_449443 baseEnd_449443 := by
    simpa [prefixWord, tailWord_449443, baseEnd_449443] using wordTrace_append hprefix tailTrace_449443
  have hstable : (prefixWord ++ tailWord_449443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449443).length < 2 ^ (prefixWord ++ tailWord_449443).sum := by decide
  have hdescent : baseEnd_449443 < baseStart_449443 := by decide
  rcases family_descends (prefixWord ++ tailWord_449443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449463 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_449463 : Nat := 118140960795 + 449463 * 2 ^ 59
def prefixEnd_449463 : Nat := 4983230072969 + 3 ^ 40 * 449463 * 2
def baseEnd_449463 : Nat := 230790555411880207645463

theorem tailTrace_449463 : CollatzResearch.WordTrace tailWord_449463 prefixEnd_449463 230790555411880207645463 := by
  unfold tailWord_449463
  simp only [CollatzResearch.WordTrace]
  refine ⟨16393262370679788014161043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10928841580453192009440695 16393262370679788014161043)
  ·
    refine ⟨24589893556019682021241565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16393262370679788014161043 24589893556019682021241565)
    ·
      refine ⟨9221210083507380757965587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24589893556019682021241565 9221210083507380757965587)
      ·
        refine ⟨13831815125261071136948381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9221210083507380757965587 13831815125261071136948381)
        ·
          refine ⟨5186930671972901676355643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13831815125261071136948381 5186930671972901676355643)
          ·
            refine ⟨7780396007959352514533465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5186930671972901676355643 7780396007959352514533465)
            ·
              refine ⟨5835297005969514385900099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7780396007959352514533465 5835297005969514385900099)
              ·
                refine ⟨8752945508954271578850149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5835297005969514385900099 8752945508954271578850149)
                ·
                  refine ⟨1641177282928925921034403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8752945508954271578850149 1641177282928925921034403)
                  ·
                    refine ⟨2461765924393388881551605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1641177282928925921034403 2461765924393388881551605)
                    ·
                      refine ⟨230790555411880207645463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2461765924393388881551605 230790555411880207645463)
                      ·
                        rfl

theorem cell23_449463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_449463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449463 prefixEnd_449463 := by exact prefixLift 449463
  have htrace : WordTrace (prefixWord ++ tailWord_449463) baseStart_449463 baseEnd_449463 := by
    simpa [prefixWord, tailWord_449463, baseEnd_449463] using wordTrace_append hprefix tailTrace_449463
  have hstable : (prefixWord ++ tailWord_449463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449463).length < 2 ^ (prefixWord ++ tailWord_449463).sum := by decide
  have hdescent : baseEnd_449463 < baseStart_449463 := by decide
  rcases family_descends (prefixWord ++ tailWord_449463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449523 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 5]
def baseStart_449523 : Nat := 118140960795 + 449523 * 2 ^ 59
def prefixEnd_449523 : Nat := 4983230072969 + 3 ^ 40 * 449523 * 2
def baseEnd_449523 : Nat := 230821364251149972895187

theorem tailTrace_449523 : CollatzResearch.WordTrace tailWord_449523 prefixEnd_449523 230821364251149972895187 := by
  unfold tailWord_449523
  simp only [CollatzResearch.WordTrace]
  refine ⟨16395450750462418261345223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10930300500308278840896815 16395450750462418261345223)
  ·
    refine ⟨24593176125693627392017835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16395450750462418261345223 24593176125693627392017835)
    ·
      refine ⟨36889764188540441088026753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24593176125693627392017835 36889764188540441088026753)
      ·
        refine ⟨27667323141405330816020065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36889764188540441088026753 27667323141405330816020065)
        ·
          refine ⟨20750492356053998112015049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27667323141405330816020065 20750492356053998112015049)
          ·
            refine ⟨15562869267040498584011287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20750492356053998112015049 15562869267040498584011287)
            ·
              refine ⟨23344303900560747876016931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15562869267040498584011287 23344303900560747876016931)
              ·
                refine ⟨35016455850841121814025397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23344303900560747876016931 35016455850841121814025397)
                ·
                  refine ⟨3282792736016355170064881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35016455850841121814025397 3282792736016355170064881)
                  ·
                    refine ⟨2462094552012266377548661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3282792736016355170064881 2462094552012266377548661)
                    ·
                      refine ⟨230821364251149972895187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2462094552012266377548661 230821364251149972895187)
                      ·
                        rfl

theorem cell23_449523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_449523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449523 prefixEnd_449523 := by exact prefixLift 449523
  have htrace : WordTrace (prefixWord ++ tailWord_449523) baseStart_449523 baseEnd_449523 := by
    simpa [prefixWord, tailWord_449523, baseEnd_449523] using wordTrace_append hprefix tailTrace_449523
  have hstable : (prefixWord ++ tailWord_449523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449523).length < 2 ^ (prefixWord ++ tailWord_449523).sum := by decide
  have hdescent : baseEnd_449523 < baseStart_449523 := by decide
  rcases family_descends (prefixWord ++ tailWord_449523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449563 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 6]
def baseStart_449563 : Nat := 118140960795 + 449563 * 2 ^ 59
def prefixEnd_449563 : Nat := 4983230072969 + 3 ^ 40 * 449563 * 2
def baseEnd_449563 : Nat := 230841903477329816395003

theorem tailTrace_449563 : CollatzResearch.WordTrace tailWord_449563 prefixEnd_449563 230841903477329816395003 := by
  unfold tailWord_449563
  simp only [CollatzResearch.WordTrace]
  refine ⟨16396909670317505092801343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10931273113545003395200895 16396909670317505092801343)
  ·
    refine ⟨24595364505476257639202015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16396909670317505092801343 24595364505476257639202015)
    ·
      refine ⟨36893046758214386458803023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24595364505476257639202015 36893046758214386458803023)
      ·
        refine ⟨55339570137321579688204535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36893046758214386458803023 55339570137321579688204535)
        ·
          refine ⟨83009355205982369532306803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55339570137321579688204535 83009355205982369532306803)
          ·
            refine ⟨124514032808973554298460205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83009355205982369532306803 124514032808973554298460205)
            ·
              refine ⟨46692762303365082861922577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124514032808973554298460205 46692762303365082861922577)
              ·
                refine ⟨35019571727523812146441933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46692762303365082861922577 35019571727523812146441933)
                ·
                  refine ⟨13132339397821429554915725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35019571727523812146441933 13132339397821429554915725)
                  ·
                    refine ⟨4924627274183036083093397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13132339397821429554915725 4924627274183036083093397)
                    ·
                      refine ⟨230841903477329816395003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4924627274183036083093397 230841903477329816395003)
                      ·
                        rfl

theorem cell23_449563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_449563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449563 prefixEnd_449563 := by exact prefixLift 449563
  have htrace : WordTrace (prefixWord ++ tailWord_449563) baseStart_449563 baseEnd_449563 := by
    simpa [prefixWord, tailWord_449563, baseEnd_449563] using wordTrace_append hprefix tailTrace_449563
  have hstable : (prefixWord ++ tailWord_449563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449563).length < 2 ^ (prefixWord ++ tailWord_449563).sum := by decide
  have hdescent : baseEnd_449563 < baseStart_449563 := by decide
  rcases family_descends (prefixWord ++ tailWord_449563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449607 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 6]
def baseStart_449607 : Nat := 118140960795 + 449607 * 2 ^ 59
def prefixEnd_449607 : Nat := 4983230072969 + 3 ^ 40 * 449607 * 2
def baseEnd_449607 : Nat := 25651610736236404916089

theorem tailTrace_449607 : CollatzResearch.WordTrace tailWord_449607 prefixEnd_449607 25651610736236404916089 := by
  unfold tailWord_449607
  simp only [CollatzResearch.WordTrace]
  refine ⟨16398514482158100607403075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10932342988105400404935383 16398514482158100607403075)
  ·
    refine ⟨24597771723237150911104613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16398514482158100607403075 24597771723237150911104613)
    ·
      refine ⟨4612082198106965795832115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24597771723237150911104613 4612082198106965795832115)
      ·
        refine ⟨6918123297160448693748173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4612082198106965795832115 6918123297160448693748173)
        ·
          refine ⟨2594296236435168260155565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6918123297160448693748173 2594296236435168260155565)
          ·
            refine ⟨972861088663188097558337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2594296236435168260155565 972861088663188097558337)
            ·
              refine ⟨729645816497391073168753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972861088663188097558337 729645816497391073168753)
              ·
                refine ⟨547234362373043304876565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729645816497391073168753 547234362373043304876565)
                ·
                  refine ⟨25651610736236404916089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 547234362373043304876565 25651610736236404916089)
                  ·
                    rfl

theorem cell23_449607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 6].length) (baseStart_449607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449607 prefixEnd_449607 := by exact prefixLift 449607
  have htrace : WordTrace (prefixWord ++ tailWord_449607) baseStart_449607 baseEnd_449607 := by
    simpa [prefixWord, tailWord_449607, baseEnd_449607] using wordTrace_append hprefix tailTrace_449607
  have hstable : (prefixWord ++ tailWord_449607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449607).length < 2 ^ (prefixWord ++ tailWord_449607).sum := by decide
  have hdescent : baseEnd_449607 < baseStart_449607 := by decide
  rcases family_descends (prefixWord ++ tailWord_449607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449637 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 1, 5]
def baseStart_449637 : Nat := 118140960795 + 449637 * 2 ^ 59
def prefixEnd_449637 : Nat := 4983230072969 + 3 ^ 40 * 449637 * 2
def baseEnd_449637 : Nat := 76959967015254175623221

theorem tailTrace_449637 : CollatzResearch.WordTrace tailWord_449637 prefixEnd_449637 76959967015254175623221 := by
  unfold tailWord_449637
  simp only [CollatzResearch.WordTrace]
  refine ⟨16399608672049415730995165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10933072448032943820663443 16399608672049415730995165)
  ·
    refine ⟨6149853252018530899123187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16399608672049415730995165 6149853252018530899123187)
    ·
      refine ⟨9224779878027796348684781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6149853252018530899123187 9224779878027796348684781)
      ·
        refine ⟨3459292454260423630756793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9224779878027796348684781 3459292454260423630756793)
        ·
          refine ⟨2594469340695317723067595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3459292454260423630756793 2594469340695317723067595)
          ·
            refine ⟨3891704011042976584601393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594469340695317723067595 3891704011042976584601393)
            ·
              refine ⟨2918778008282232438451045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3891704011042976584601393 2918778008282232438451045)
              ·
                refine ⟨547270876552918582209571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2918778008282232438451045 547270876552918582209571)
                ·
                  refine ⟨820906314829377873314357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547270876552918582209571 820906314829377873314357)
                  ·
                    refine ⟨76959967015254175623221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 820906314829377873314357 76959967015254175623221)
                    ·
                      rfl

theorem cell23_449637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_449637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449637 prefixEnd_449637 := by exact prefixLift 449637
  have htrace : WordTrace (prefixWord ++ tailWord_449637) baseStart_449637 baseEnd_449637 := by
    simpa [prefixWord, tailWord_449637, baseEnd_449637] using wordTrace_append hprefix tailTrace_449637
  have hstable : (prefixWord ++ tailWord_449637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449637).length < 2 ^ (prefixWord ++ tailWord_449637).sum := by decide
  have hdescent : baseEnd_449637 < baseStart_449637 := by decide
  rcases family_descends (prefixWord ++ tailWord_449637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449654 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_449654 : Nat := 118140960795 + 449654 * 2 ^ 59
def prefixEnd_449654 : Nat := 4983230072969 + 3 ^ 40 * 449654 * 2
def baseEnd_449654 : Nat := 76962876738962986785695

theorem tailTrace_449654 : CollatzResearch.WordTrace tailWord_449654 prefixEnd_449654 76962876738962986785695 := by
  unfold tailWord_449654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025014294561739227147751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10933485808658551756242677 1025014294561739227147751)
  ·
    refine ⟨1537521441842608840721627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1025014294561739227147751 1537521441842608840721627)
    ·
      refine ⟨2306282162763913261082441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537521441842608840721627 2306282162763913261082441)
      ·
        refine ⟨1729711622072934945811831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2306282162763913261082441 1729711622072934945811831)
        ·
          refine ⟨2594567433109402418717747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1729711622072934945811831 2594567433109402418717747)
          ·
            refine ⟨3891851149664103628076621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594567433109402418717747 3891851149664103628076621)
            ·
              refine ⟨1459444181124038860528733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3891851149664103628076621 1459444181124038860528733)
              ·
                refine ⟨547291567921514572698275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1459444181124038860528733 547291567921514572698275)
                ·
                  refine ⟨820937351882271859047413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547291567921514572698275 820937351882271859047413)
                  ·
                    refine ⟨76962876738962986785695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 820937351882271859047413 76962876738962986785695)
                    ·
                      rfl

theorem cell23_449654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_449654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449654 prefixEnd_449654 := by exact prefixLift 449654
  have htrace : WordTrace (prefixWord ++ tailWord_449654) baseStart_449654 baseEnd_449654 := by
    simpa [prefixWord, tailWord_449654, baseEnd_449654] using wordTrace_append hprefix tailTrace_449654
  have hstable : (prefixWord ++ tailWord_449654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449654).length < 2 ^ (prefixWord ++ tailWord_449654).sum := by decide
  have hdescent : baseEnd_449654 < baseStart_449654 := by decide
  rcases family_descends (prefixWord ++ tailWord_449654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449667 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 4, 4]
def baseStart_449667 : Nat := 118140960795 + 449667 * 2 ^ 59
def prefixEnd_449667 : Nat := 4983230072969 + 3 ^ 40 * 449667 * 2
def baseEnd_449667 : Nat := 76965101821799136498175

theorem tailTrace_449667 : CollatzResearch.WordTrace tailWord_449667 prefixEnd_449667 76965101821799136498175 := by
  unfold tailWord_449667
  simp only [CollatzResearch.WordTrace]
  refine ⟨16400702861940730854587255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10933801907960487236391503 16400702861940730854587255)
  ·
    refine ⟨24601054292911096281880883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16400702861940730854587255 24601054292911096281880883)
    ·
      refine ⟨36901581439366644422821325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24601054292911096281880883 36901581439366644422821325)
      ·
        refine ⟨13838093039762491658557997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36901581439366644422821325 13838093039762491658557997)
        ·
          refine ⟨5189284889910934371959249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13838093039762491658557997 5189284889910934371959249)
          ·
            refine ⟨3891963667433200778969437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5189284889910934371959249 3891963667433200778969437)
            ·
              refine ⟨1459486375287450292113539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3891963667433200778969437 1459486375287450292113539)
              ·
                refine ⟨2189229562931175438170309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459486375287450292113539 2189229562931175438170309)
                ·
                  refine ⟨410480543049595394656933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2189229562931175438170309 410480543049595394656933)
                  ·
                    refine ⟨76965101821799136498175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 410480543049595394656933 76965101821799136498175)
                    ·
                      rfl

theorem cell23_449667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 4].length) (baseStart_449667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449667 prefixEnd_449667 := by exact prefixLift 449667
  have htrace : WordTrace (prefixWord ++ tailWord_449667) baseStart_449667 baseEnd_449667 := by
    simpa [prefixWord, tailWord_449667, baseEnd_449667] using wordTrace_append hprefix tailTrace_449667
  have hstable : (prefixWord ++ tailWord_449667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449667).length < 2 ^ (prefixWord ++ tailWord_449667).sum := by decide
  have hdescent : baseEnd_449667 < baseStart_449667 := by decide
  rcases family_descends (prefixWord ++ tailWord_449667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449687 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_449687 : Nat := 118140960795 + 449687 * 2 ^ 59
def prefixEnd_449687 : Nat := 4983230072969 + 3 ^ 40 * 449687 * 2
def baseEnd_449687 : Nat := 230905575078487331244433

theorem tailTrace_449687 : CollatzResearch.WordTrace tailWord_449687 prefixEnd_449687 230905575078487331244433 := by
  unfold tailWord_449687
  simp only [CollatzResearch.WordTrace]
  refine ⟨16401432321868274270315315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10934288214578849513543543 16401432321868274270315315)
  ·
    refine ⟨24602148482802411405472973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16401432321868274270315315 24602148482802411405472973)
    ·
      refine ⟨9225805681050904277052365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24602148482802411405472973 9225805681050904277052365)
      ·
        refine ⟨3459677130394089103894637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9225805681050904277052365 3459677130394089103894637)
        ·
          refine ⟨1297378923897783413960489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3459677130394089103894637 1297378923897783413960489)
          ·
            refine ⟨973034192923337560470367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297378923897783413960489 973034192923337560470367)
            ·
              refine ⟨1459551289385006340705551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973034192923337560470367 1459551289385006340705551)
              ·
                refine ⟨2189326934077509511058327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459551289385006340705551 2189326934077509511058327)
                ·
                  refine ⟨3283990401116264266587491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2189326934077509511058327 3283990401116264266587491)
                  ·
                    refine ⟨4925985601674396399881237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3283990401116264266587491 4925985601674396399881237)
                    ·
                      refine ⟨230905575078487331244433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4925985601674396399881237 230905575078487331244433)
                      ·
                        rfl

theorem cell23_449687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_449687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449687 prefixEnd_449687 := by exact prefixLift 449687
  have htrace : WordTrace (prefixWord ++ tailWord_449687) baseStart_449687 baseEnd_449687 := by
    simpa [prefixWord, tailWord_449687, baseEnd_449687] using wordTrace_append hprefix tailTrace_449687
  have hstable : (prefixWord ++ tailWord_449687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449687).length < 2 ^ (prefixWord ++ tailWord_449687).sum := by decide
  have hdescent : baseEnd_449687 < baseStart_449687 := by decide
  rcases family_descends (prefixWord ++ tailWord_449687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449751 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 1, 3, 2]
def baseStart_449751 : Nat := 118140960795 + 449751 * 2 ^ 59
def prefixEnd_449751 : Nat := 4983230072969 + 3 ^ 40 * 449751 * 2
def baseEnd_449751 : Nat := 230938437840375080844139

theorem tailTrace_449751 : CollatzResearch.WordTrace tailWord_449751 prefixEnd_449751 230938437840375080844139 := by
  unfold tailWord_449751
  simp only [CollatzResearch.WordTrace]
  refine ⟨16403766593636413200645107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10935844395757608800430071 16403766593636413200645107)
  ·
    refine ⟨24605649890454619800967661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16403766593636413200645107 24605649890454619800967661)
    ·
      refine ⟨9227118708920482425362873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24605649890454619800967661 9227118708920482425362873)
      ·
        refine ⟨6920339031690361819022155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9227118708920482425362873 6920339031690361819022155)
        ·
          refine ⟨10380508547535542728533233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6920339031690361819022155 10380508547535542728533233)
          ·
            refine ⟨7785381410651657046399925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10380508547535542728533233 7785381410651657046399925)
            ·
              refine ⟨729879507248592848099993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7785381410651657046399925 729879507248592848099993)
              ·
                refine ⟨547409630436444636074995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729879507248592848099993 547409630436444636074995)
                ·
                  refine ⟨821114445654666954112493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547409630436444636074995 821114445654666954112493)
                  ·
                    refine ⟨307917917120500107792185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821114445654666954112493 307917917120500107792185)
                    ·
                      refine ⟨230938437840375080844139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 307917917120500107792185 230938437840375080844139)
                      ·
                        rfl

theorem cell23_449751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_449751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449751 prefixEnd_449751 := by exact prefixLift 449751
  have htrace : WordTrace (prefixWord ++ tailWord_449751) baseStart_449751 baseEnd_449751 := by
    simpa [prefixWord, tailWord_449751, baseEnd_449751] using wordTrace_append hprefix tailTrace_449751
  have hstable : (prefixWord ++ tailWord_449751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449751).length < 2 ^ (prefixWord ++ tailWord_449751).sum := by decide
  have hdescent : baseEnd_449751 < baseStart_449751 := by decide
  rcases family_descends (prefixWord ++ tailWord_449751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449764 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 3, 4, 2]
def baseStart_449764 : Nat := 118140960795 + 449764 * 2 ^ 59
def prefixEnd_449764 : Nat := 4983230072969 + 3 ^ 40 * 449764 * 2
def baseEnd_449764 : Nat := 230945113088883529981579

theorem tailTrace_449764 : CollatzResearch.WordTrace tailWord_449764 prefixEnd_449764 230945113088883529981579 := by
  unfold tailWord_449764
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202120371294658210434173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10936160495059544280578897 8202120371294658210434173)
  ·
    refine ⟨3075795139235496828912815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8202120371294658210434173 3075795139235496828912815)
    ·
      refine ⟨4613692708853245243369223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3075795139235496828912815 4613692708853245243369223)
      ·
        refine ⟨6920539063279867865053835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613692708853245243369223 6920539063279867865053835)
        ·
          refine ⟨10380808594919801797580753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6920539063279867865053835 10380808594919801797580753)
          ·
            refine ⟨7785606446189851348185565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10380808594919801797580753 7785606446189851348185565)
            ·
              refine ⟨2919602417321194255569587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7785606446189851348185565 2919602417321194255569587)
              ·
                refine ⟨4379403625981791383354381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2919602417321194255569587 4379403625981791383354381)
                ·
                  refine ⟨1642276359743171768757893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4379403625981791383354381 1642276359743171768757893)
                  ·
                    refine ⟨307926817451844706642105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1642276359743171768757893 307926817451844706642105)
                    ·
                      refine ⟨230945113088883529981579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 307926817451844706642105 230945113088883529981579)
                      ·
                        rfl

theorem cell23_449764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_449764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449764 prefixEnd_449764 := by exact prefixLift 449764
  have htrace : WordTrace (prefixWord ++ tailWord_449764) baseStart_449764 baseEnd_449764 := by
    simpa [prefixWord, tailWord_449764, baseEnd_449764] using wordTrace_append hprefix tailTrace_449764
  have hstable : (prefixWord ++ tailWord_449764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449764).length < 2 ^ (prefixWord ++ tailWord_449764).sum := by decide
  have hdescent : baseEnd_449764 < baseStart_449764 := by decide
  rcases family_descends (prefixWord ++ tailWord_449764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449768 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_449768 : Nat := 118140960795 + 449768 * 2 ^ 59
def prefixEnd_449768 : Nat := 4983230072969 + 3 ^ 40 * 449768 * 2
def baseEnd_449768 : Nat := 230947167011501514331561

theorem tailTrace_449768 : CollatzResearch.WordTrace tailWord_449768 prefixEnd_449768 230947167011501514331561 := by
  unfold tailWord_449768
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202193317287412552006979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10936257756383216736009305 8202193317287412552006979)
  ·
    refine ⟨12303289975931118828010469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8202193317287412552006979 12303289975931118828010469)
    ·
      refine ⟨2306866870487084780251963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12303289975931118828010469 2306866870487084780251963)
      ·
        refine ⟨3460300305730627170377945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306866870487084780251963 3460300305730627170377945)
        ·
          refine ⟨2595225229297970377783459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3460300305730627170377945 2595225229297970377783459)
          ·
            refine ⟨3892837843946955566675189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595225229297970377783459 3892837843946955566675189)
            ·
              refine ⟨364953547870027084375799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3892837843946955566675189 364953547870027084375799)
              ·
                refine ⟨547430321805040626563699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364953547870027084375799 547430321805040626563699)
                ·
                  refine ⟨821145482707560939845549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547430321805040626563699 821145482707560939845549)
                  ·
                    refine ⟨307929556015335352442081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821145482707560939845549 307929556015335352442081)
                    ·
                      refine ⟨230947167011501514331561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 307929556015335352442081 230947167011501514331561)
                      ·
                        rfl

theorem cell23_449768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_449768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449768 prefixEnd_449768 := by exact prefixLift 449768
  have htrace : WordTrace (prefixWord ++ tailWord_449768) baseStart_449768 baseEnd_449768 := by
    simpa [prefixWord, tailWord_449768, baseEnd_449768] using wordTrace_append hprefix tailTrace_449768
  have hstable : (prefixWord ++ tailWord_449768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449768).length < 2 ^ (prefixWord ++ tailWord_449768).sum := by decide
  have hdescent : baseEnd_449768 < baseStart_449768 := by decide
  rcases family_descends (prefixWord ++ tailWord_449768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449777 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_449777 : Nat := 118140960795 + 449777 * 2 ^ 59
def prefixEnd_449777 : Nat := 4983230072969 + 3 ^ 40 * 449777 * 2
def baseEnd_449777 : Nat := 230951788337391979119019

theorem tailTrace_449777 : CollatzResearch.WordTrace tailWord_449777 prefixEnd_449777 230951788337391979119019 := by
  unfold tailWord_449777
  simp only [CollatzResearch.WordTrace]
  refine ⟨16404714891542219641091585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10936476594361479760727723 16404714891542219641091585)
  ·
    refine ⟨12303536168656664730818689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16404714891542219641091585 12303536168656664730818689)
    ·
      refine ⟨9227652126492498548114017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12303536168656664730818689 9227652126492498548114017)
      ·
        refine ⟨6920739094869373911085513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9227652126492498548114017 6920739094869373911085513)
        ·
          refine ⟨5190554321152030433314135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6920739094869373911085513 5190554321152030433314135)
          ·
            refine ⟨7785831481728045649971203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190554321152030433314135 7785831481728045649971203)
            ·
              refine ⟨11678747222592068474956805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785831481728045649971203 11678747222592068474956805)
              ·
                refine ⟨2189765104236012839054401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11678747222592068474956805 2189765104236012839054401)
                ·
                  refine ⟨1642323828177009629290801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2189765104236012839054401 1642323828177009629290801)
                  ·
                    refine ⟨1231742871132757221968101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1642323828177009629290801 1231742871132757221968101)
                    ·
                      refine ⟨230951788337391979119019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1231742871132757221968101 230951788337391979119019)
                      ·
                        rfl

theorem cell23_449777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_449777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449777 prefixEnd_449777 := by exact prefixLift 449777
  have htrace : WordTrace (prefixWord ++ tailWord_449777) baseStart_449777 baseEnd_449777 := by
    simpa [prefixWord, tailWord_449777, baseEnd_449777] using wordTrace_append hprefix tailTrace_449777
  have hstable : (prefixWord ++ tailWord_449777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449777).length < 2 ^ (prefixWord ++ tailWord_449777).sum := by decide
  have hdescent : baseEnd_449777 < baseStart_449777 := by decide
  rcases family_descends (prefixWord ++ tailWord_449777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449821 : List Nat := [1, 4, 2, 3, 1, 1, 1, 5, 5]
def baseStart_449821 : Nat := 118140960795 + 449821 * 2 ^ 59
def prefixEnd_449821 : Nat := 4983230072969 + 3 ^ 40 * 449821 * 2
def baseEnd_449821 : Nat := 25663820165132200774313

theorem tailTrace_449821 : CollatzResearch.WordTrace tailWord_449821 prefixEnd_449821 25663820165132200774313 := by
  unfold tailWord_449821
  simp only [CollatzResearch.WordTrace]
  refine ⟨16406319703382815155693317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10937546468921876770462211 16406319703382815155693317)
  ·
    refine ⟨3076184944384277841692497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16406319703382815155693317 3076184944384277841692497)
    ·
      refine ⟨2307138708288208381269373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3076184944384277841692497 2307138708288208381269373)
      ·
        refine ⟨865177015608078142976015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2307138708288208381269373 865177015608078142976015)
        ·
          refine ⟨1297765523412117214464023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865177015608078142976015 1297765523412117214464023)
          ·
            refine ⟨1946648285118175821696035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297765523412117214464023 1946648285118175821696035)
            ·
              refine ⟨2919972427677263732544053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1946648285118175821696035 2919972427677263732544053)
              ·
                refine ⟨273747415094743474926005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2919972427677263732544053 273747415094743474926005)
                ·
                  refine ⟨25663820165132200774313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273747415094743474926005 25663820165132200774313)
                  ·
                    rfl

theorem cell23_449821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_449821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449821 prefixEnd_449821 := by exact prefixLift 449821
  have htrace : WordTrace (prefixWord ++ tailWord_449821) baseStart_449821 baseEnd_449821 := by
    simpa [prefixWord, tailWord_449821, baseEnd_449821] using wordTrace_append hprefix tailTrace_449821
  have hstable : (prefixWord ++ tailWord_449821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449821).length < 2 ^ (prefixWord ++ tailWord_449821).sum := by decide
  have hdescent : baseEnd_449821 < baseStart_449821 := by decide
  rcases family_descends (prefixWord ++ tailWord_449821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449844 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_449844 : Nat := 118140960795 + 449844 * 2 ^ 59
def prefixEnd_449844 : Nat := 4983230072969 + 3 ^ 40 * 449844 * 2
def baseEnd_449844 : Nat := 230986191541243216981211

theorem tailTrace_449844 : CollatzResearch.WordTrace tailWord_449844 prefixEnd_449844 230986191541243216981211 := by
  unfold tailWord_449844
  simp only [CollatzResearch.WordTrace]
  refine ⟨8203579291149745041890293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10938105721532993389187057 8203579291149745041890293)
  ·
    refine ⟨769085558545288597677215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8203579291149745041890293 769085558545288597677215)
    ·
      refine ⟨1153628337817932896515823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 769085558545288597677215 1153628337817932896515823)
      ·
        refine ⟨1730442506726899344773735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153628337817932896515823 1730442506726899344773735)
        ·
          refine ⟨2595663760090349017160603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730442506726899344773735 2595663760090349017160603)
          ·
            refine ⟨3893495640135523525740905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595663760090349017160603 3893495640135523525740905)
            ·
              refine ⟨2920121730101642644305679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3893495640135523525740905 2920121730101642644305679)
              ·
                refine ⟨4380182595152463966458519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920121730101642644305679 4380182595152463966458519)
                ·
                  refine ⟨6570273892728695949687779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380182595152463966458519 6570273892728695949687779)
                  ·
                    refine ⟨9855410839093043924531669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6570273892728695949687779 9855410839093043924531669)
                    ·
                      refine ⟨230986191541243216981211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9855410839093043924531669 230986191541243216981211)
                      ·
                        rfl

theorem cell23_449844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_449844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449844 prefixEnd_449844 := by exact prefixLift 449844
  have htrace : WordTrace (prefixWord ++ tailWord_449844) baseStart_449844 baseEnd_449844 := by
    simpa [prefixWord, tailWord_449844, baseEnd_449844] using wordTrace_append hprefix tailTrace_449844
  have hstable : (prefixWord ++ tailWord_449844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449844).length < 2 ^ (prefixWord ++ tailWord_449844).sum := by decide
  have hdescent : baseEnd_449844 < baseStart_449844 := by decide
  rcases family_descends (prefixWord ++ tailWord_449844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449854 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_449854 : Nat := 118140960795 + 449854 * 2 ^ 59
def prefixEnd_449854 : Nat := 4983230072969 + 3 ^ 40 * 449854 * 2
def baseEnd_449854 : Nat := 230991326347788177856165

theorem tailTrace_449854 : CollatzResearch.WordTrace tailWord_449854 prefixEnd_449854 230991326347788177856165 := by
  unfold tailWord_449854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050940414032907723955577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10938348874842174527763077 2050940414032907723955577)
  ·
    refine ⟨1538205310524680792966683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2050940414032907723955577 1538205310524680792966683)
    ·
      refine ⟨2307307965787021189450025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1538205310524680792966683 2307307965787021189450025)
      ·
        refine ⟨1730480974340265892087519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2307307965787021189450025 1730480974340265892087519)
        ·
          refine ⟨2595721461510398838131279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730480974340265892087519 2595721461510398838131279)
          ·
            refine ⟨3893582192265598257196919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2595721461510398838131279 3893582192265598257196919)
            ·
              refine ⟨5840373288398397385795379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3893582192265598257196919 5840373288398397385795379)
              ·
                refine ⟨8760559932597596078693069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5840373288398397385795379 8760559932597596078693069)
                ·
                  refine ⟨3285209974724098529509901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8760559932597596078693069 3285209974724098529509901)
                  ·
                    refine ⟨1231953740521536948566213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3285209974724098529509901 1231953740521536948566213)
                    ·
                      refine ⟨230991326347788177856165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1231953740521536948566213 230991326347788177856165)
                      ·
                        rfl

theorem cell23_449854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_449854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449854 prefixEnd_449854 := by exact prefixLift 449854
  have htrace : WordTrace (prefixWord ++ tailWord_449854) baseStart_449854 baseEnd_449854 := by
    simpa [prefixWord, tailWord_449854, baseEnd_449854] using wordTrace_append hprefix tailTrace_449854
  have hstable : (prefixWord ++ tailWord_449854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449854).length < 2 ^ (prefixWord ++ tailWord_449854).sum := by decide
  have hdescent : baseEnd_449854 < baseStart_449854 := by decide
  rcases family_descends (prefixWord ++ tailWord_449854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449885 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_449885 : Nat := 118140960795 + 449885 * 2 ^ 59
def prefixEnd_449885 : Nat := 4983230072969 + 3 ^ 40 * 449885 * 2
def baseEnd_449885 : Nat := 77002414749359185522841

theorem tailTrace_449885 : CollatzResearch.WordTrace tailWord_449885 prefixEnd_449885 77002414749359185522841 := by
  unfold tailWord_449885
  simp only [CollatzResearch.WordTrace]
  refine ⟨16408653975150954086023109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10939102650100636057348739 16408653975150954086023109)
  ·
    refine ⟨3076622620340803891129333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16408653975150954086023109 3076622620340803891129333)
    ·
      refine ⟨288433370656950364793375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3076622620340803891129333 288433370656950364793375)
      ·
        refine ⟨432650055985425547190063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288433370656950364793375 432650055985425547190063)
        ·
          refine ⟨648975083978138320785095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432650055985425547190063 648975083978138320785095)
          ·
            refine ⟨973462625967207481177643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648975083978138320785095 973462625967207481177643)
            ·
              refine ⟨1460193938950811221766465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973462625967207481177643 1460193938950811221766465)
              ·
                refine ⟨1095145454213108416324849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460193938950811221766465 1095145454213108416324849)
                ·
                  refine ⟨821359090659831312243637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095145454213108416324849 821359090659831312243637)
                  ·
                    refine ⟨77002414749359185522841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 821359090659831312243637 77002414749359185522841)
                    ·
                      rfl

theorem cell23_449885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_449885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449885 prefixEnd_449885 := by exact prefixLift 449885
  have htrace : WordTrace (prefixWord ++ tailWord_449885) baseStart_449885 baseEnd_449885 := by
    simpa [prefixWord, tailWord_449885, baseEnd_449885] using wordTrace_append hprefix tailTrace_449885
  have hstable : (prefixWord ++ tailWord_449885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449885).length < 2 ^ (prefixWord ++ tailWord_449885).sum := by decide
  have hdescent : baseEnd_449885 < baseStart_449885 := by decide
  rcases family_descends (prefixWord ++ tailWord_449885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449891 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 3]
def baseStart_449891 : Nat := 118140960795 + 449891 * 2 ^ 59
def prefixEnd_449891 : Nat := 4983230072969 + 3 ^ 40 * 449891 * 2
def baseEnd_449891 : Nat := 231010325132004533093495

theorem tailTrace_449891 : CollatzResearch.WordTrace tailWord_449891 prefixEnd_449891 231010325132004533093495 := by
  unfold tailWord_449891
  simp only [CollatzResearch.WordTrace]
  refine ⟨16408872813129217110741527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10939248542086144740494351 16408872813129217110741527)
  ·
    refine ⟨24613309219693825666112291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16408872813129217110741527 24613309219693825666112291)
    ·
      refine ⟨36919963829540738499168437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24613309219693825666112291 36919963829540738499168437)
      ·
        refine ⟨3461246609019444234297041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36919963829540738499168437 3461246609019444234297041)
        ·
          refine ⟨2595934956764583175722781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3461246609019444234297041 2595934956764583175722781)
          ·
            refine ⟨973475608786718690896043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2595934956764583175722781 973475608786718690896043)
            ·
              refine ⟨1460213413180078036344065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973475608786718690896043 1460213413180078036344065)
              ·
                refine ⟨1095160059885058527258049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460213413180078036344065 1095160059885058527258049)
                ·
                  refine ⟨821370044913793895443537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1095160059885058527258049 821370044913793895443537)
                  ·
                    refine ⟨616027533685345421582653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 821370044913793895443537 616027533685345421582653)
                    ·
                      refine ⟨231010325132004533093495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 616027533685345421582653 231010325132004533093495)
                      ·
                        rfl

theorem cell23_449891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_449891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449891 prefixEnd_449891 := by exact prefixLift 449891
  have htrace : WordTrace (prefixWord ++ tailWord_449891) baseStart_449891 baseEnd_449891 := by
    simpa [prefixWord, tailWord_449891, baseEnd_449891] using wordTrace_append hprefix tailTrace_449891
  have hstable : (prefixWord ++ tailWord_449891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449891).length < 2 ^ (prefixWord ++ tailWord_449891).sum := by decide
  have hdescent : baseEnd_449891 < baseStart_449891 := by decide
  rcases family_descends (prefixWord ++ tailWord_449891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449897 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_449897 : Nat := 118140960795 + 449897 * 2 ^ 59
def prefixEnd_449897 : Nat := 4983230072969 + 3 ^ 40 * 449897 * 2
def baseEnd_449897 : Nat := 231013406015931509618467

theorem tailTrace_449897 : CollatzResearch.WordTrace tailWord_449897 prefixEnd_449897 231013406015931509618467 := by
  unfold tailWord_449897
  simp only [CollatzResearch.WordTrace]
  refine ⟨16409091651107480135459945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10939394434071653423639963 16409091651107480135459945)
  ·
    refine ⟨12306818738330610101594959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16409091651107480135459945 12306818738330610101594959)
    ·
      refine ⟨18460228107495915152392439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12306818738330610101594959 18460228107495915152392439)
      ·
        refine ⟨27690342161243872728588659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18460228107495915152392439 27690342161243872728588659)
        ·
          refine ⟨41535513241865809092882989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27690342161243872728588659 41535513241865809092882989)
          ·
            refine ⟨15575817465699678409831121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41535513241865809092882989 15575817465699678409831121)
            ·
              refine ⟨11681863099274758807373341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15575817465699678409831121 11681863099274758807373341)
              ·
                refine ⟨4380698662228034552765003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11681863099274758807373341 4380698662228034552765003)
                ·
                  refine ⟨6571047993342051829147505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4380698662228034552765003 6571047993342051829147505)
                  ·
                    refine ⟨4928285995006538871860629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6571047993342051829147505 4928285995006538871860629)
                    ·
                      refine ⟨231013406015931509618467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4928285995006538871860629 231013406015931509618467)
                      ·
                        rfl

theorem cell23_449897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_449897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449897 prefixEnd_449897 := by exact prefixLift 449897
  have htrace : WordTrace (prefixWord ++ tailWord_449897) baseStart_449897 baseEnd_449897 := by
    simpa [prefixWord, tailWord_449897, baseEnd_449897] using wordTrace_append hprefix tailTrace_449897
  have hstable : (prefixWord ++ tailWord_449897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449897).length < 2 ^ (prefixWord ++ tailWord_449897).sum := by decide
  have hdescent : baseEnd_449897 < baseStart_449897 := by decide
  rcases family_descends (prefixWord ++ tailWord_449897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449964 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_449964 : Nat := 118140960795 + 449964 * 2 ^ 59
def prefixEnd_449964 : Nat := 4983230072969 + 3 ^ 40 * 449964 * 2
def baseEnd_449964 : Nat := 231047809219782747480659

theorem tailTrace_449964 : CollatzResearch.WordTrace tailWord_449964 prefixEnd_449964 231047809219782747480659 := by
  unfold tailWord_449964
  simp only [CollatzResearch.WordTrace]
  refine ⟨8205767670932375289074473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10941023561243167052099297 8205767670932375289074473)
  ·
    refine ⟨6154325753199281466805855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8205767670932375289074473 6154325753199281466805855)
    ·
      refine ⟨9231488629798922200208783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6154325753199281466805855 9231488629798922200208783)
      ·
        refine ⟨13847232944698383300313175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9231488629798922200208783 13847232944698383300313175)
        ·
          refine ⟨20770849417047574950469763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13847232944698383300313175 20770849417047574950469763)
          ·
            refine ⟨31156274125571362425704645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20770849417047574950469763 31156274125571362425704645)
            ·
              refine ⟨5841801398544630454819621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31156274125571362425704645 5841801398544630454819621)
              ·
                refine ⟨1095337762227118210278679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5841801398544630454819621 1095337762227118210278679)
                ·
                  refine ⟨1643006643340677315418019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095337762227118210278679 1643006643340677315418019)
                  ·
                    refine ⟨2464509965011015973127029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1643006643340677315418019 2464509965011015973127029)
                    ·
                      refine ⟨231047809219782747480659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2464509965011015973127029 231047809219782747480659)
                      ·
                        rfl

theorem cell23_449964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_449964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449964 prefixEnd_449964 := by exact prefixLift 449964
  have htrace : WordTrace (prefixWord ++ tailWord_449964) baseStart_449964 baseEnd_449964 := by
    simpa [prefixWord, tailWord_449964, baseEnd_449964] using wordTrace_append hprefix tailTrace_449964
  have hstable : (prefixWord ++ tailWord_449964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449964).length < 2 ^ (prefixWord ++ tailWord_449964).sum := by decide
  have hdescent : baseEnd_449964 < baseStart_449964 := by decide
  rcases family_descends (prefixWord ++ tailWord_449964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449981 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_449981 : Nat := 118140960795 + 449981 * 2 ^ 59
def prefixEnd_449981 : Nat := 4983230072969 + 3 ^ 40 * 449981 * 2
def baseEnd_449981 : Nat := 231056538390909180968081

theorem tailTrace_449981 : CollatzResearch.WordTrace tailWord_449981 prefixEnd_449981 231056538390909180968081 := by
  unfold tailWord_449981
  simp only [CollatzResearch.WordTrace]
  refine ⟨16412155382803162481517797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10941436921868774987678531 16412155382803162481517797)
  ·
    refine ⟨3077279134275592965284587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16412155382803162481517797 3077279134275592965284587)
    ·
      refine ⟨4615918701413389447926881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3077279134275592965284587 4615918701413389447926881)
      ·
        refine ⟨3461939026060042085945161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4615918701413389447926881 3461939026060042085945161)
        ·
          refine ⟨2596454269545031564458871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3461939026060042085945161 2596454269545031564458871)
          ·
            refine ⟨3894681404317547346688307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596454269545031564458871 3894681404317547346688307)
            ·
              refine ⟨5842022106476321020032461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3894681404317547346688307 5842022106476321020032461)
              ·
                refine ⟨2190758289928620382512173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5842022106476321020032461 2190758289928620382512173)
                ·
                  refine ⟨821534358723232643442065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2190758289928620382512173 821534358723232643442065)
                  ·
                    refine ⟨616150769042424482581549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 821534358723232643442065 616150769042424482581549)
                    ·
                      refine ⟨231056538390909180968081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 616150769042424482581549 231056538390909180968081)
                      ·
                        rfl

theorem cell23_449981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_449981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449981 prefixEnd_449981 := by exact prefixLift 449981
  have htrace : WordTrace (prefixWord ++ tailWord_449981) baseStart_449981 baseEnd_449981 := by
    simpa [prefixWord, tailWord_449981, baseEnd_449981] using wordTrace_append hprefix tailTrace_449981
  have hstable : (prefixWord ++ tailWord_449981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449981).length < 2 ^ (prefixWord ++ tailWord_449981).sum := by decide
  have hdescent : baseEnd_449981 < baseStart_449981 := by decide
  rcases family_descends (prefixWord ++ tailWord_449981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_449995 : List Nat := [1, 1, 1, 1, 3, 3, 3, 5, 1, 2, 2]
def baseStart_449995 : Nat := 118140960795 + 449995 * 2 ^ 59
def prefixEnd_449995 : Nat := 4983230072969 + 3 ^ 40 * 449995 * 2
def baseEnd_449995 : Nat := 231063727120072126193017

theorem tailTrace_449995 : CollatzResearch.WordTrace tailWord_449995 prefixEnd_449995 231063727120072126193017 := by
  unfold tailWord_449995
  simp only [CollatzResearch.WordTrace]
  refine ⟨16412666004752442872527439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10941777336501628581684959 16412666004752442872527439)
  ·
    refine ⟨24618999007128664308791159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16412666004752442872527439 24618999007128664308791159)
    ·
      refine ⟨36928498510692996463186739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24618999007128664308791159 36928498510692996463186739)
      ·
        refine ⟨55392747766039494694780109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36928498510692996463186739 55392747766039494694780109)
        ·
          refine ⟨20772280412264810510542541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55392747766039494694780109 20772280412264810510542541)
          ·
            refine ⟨7789605154599303941453453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20772280412264810510542541 7789605154599303941453453)
            ·
              refine ⟨2921101932974738978045045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7789605154599303941453453 2921101932974738978045045)
              ·
                refine ⟨273853306216381779191723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2921101932974738978045045 273853306216381779191723)
                ·
                  refine ⟨410779959324572668787585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273853306216381779191723 410779959324572668787585)
                  ·
                    refine ⟨308084969493429501590689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 410779959324572668787585 308084969493429501590689)
                    ·
                      refine ⟨231063727120072126193017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 308084969493429501590689 231063727120072126193017)
                      ·
                        rfl

theorem cell23_449995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 1, 2, 2].length) (baseStart_449995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_449995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_449995 prefixEnd_449995 := by exact prefixLift 449995
  have htrace : WordTrace (prefixWord ++ tailWord_449995) baseStart_449995 baseEnd_449995 := by
    simpa [prefixWord, tailWord_449995, baseEnd_449995] using wordTrace_append hprefix tailTrace_449995
  have hstable : (prefixWord ++ tailWord_449995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_449995).length < 2 ^ (prefixWord ++ tailWord_449995).sum := by decide
  have hdescent : baseEnd_449995 < baseStart_449995 := by decide
  rcases family_descends (prefixWord ++ tailWord_449995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450044 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_450044 : Nat := 118140960795 + 450044 * 2 ^ 59
def prefixEnd_450044 : Nat := 4983230072969 + 3 ^ 40 * 450044 * 2
def baseEnd_450044 : Nat := 77029629224047478160097

theorem tailTrace_450044 : CollatzResearch.WordTrace tailWord_450044 prefixEnd_450044 77029629224047478160097 := by
  unfold tailWord_450044
  simp only [CollatzResearch.WordTrace]
  refine ⟨8207226590787462120530593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10942968787716616160707457 8207226590787462120530593)
  ·
    refine ⟨6155419943090596590397945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8207226590787462120530593 6155419943090596590397945)
    ·
      refine ⟨4616564957317947442798459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6155419943090596590397945 4616564957317947442798459)
      ·
        refine ⟨6924847435976921164197689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4616564957317947442798459 6924847435976921164197689)
        ·
          refine ⟨5193635576982690873148267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6924847435976921164197689 5193635576982690873148267)
          ·
            refine ⟨7790453365474036309722401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5193635576982690873148267 7790453365474036309722401)
            ·
              refine ⟨5842840024105527232291801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7790453365474036309722401 5842840024105527232291801)
              ·
                refine ⟨4382130018079145424218851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5842840024105527232291801 4382130018079145424218851)
                ·
                  refine ⟨6573195027118718136328277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4382130018079145424218851 6573195027118718136328277)
                  ·
                    refine ⟨77029629224047478160097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6573195027118718136328277 77029629224047478160097)
                    ·
                      rfl

theorem cell23_450044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_450044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450044 prefixEnd_450044 := by exact prefixLift 450044
  have htrace : WordTrace (prefixWord ++ tailWord_450044) baseStart_450044 baseEnd_450044 := by
    simpa [prefixWord, tailWord_450044, baseEnd_450044] using wordTrace_append hprefix tailTrace_450044
  have hstable : (prefixWord ++ tailWord_450044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450044).length < 2 ^ (prefixWord ++ tailWord_450044).sum := by decide
  have hdescent : baseEnd_450044 < baseStart_450044 := by decide
  rcases family_descends (prefixWord ++ tailWord_450044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450055 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 1, 3, 2]
def baseStart_450055 : Nat := 118140960795 + 450055 * 2 ^ 59
def prefixEnd_450055 : Nat := 4983230072969 + 3 ^ 40 * 450055 * 2
def baseEnd_450055 : Nat := 231094535959341891442741

theorem tailTrace_450055 : CollatzResearch.WordTrace tailWord_450055 prefixEnd_450055 231094535959341891442741 := by
  unfold tailWord_450055
  simp only [CollatzResearch.WordTrace]
  refine ⟨16414854384535073119711619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10943236256356715413141079 16414854384535073119711619)
  ·
    refine ⟨24622281576802609679567429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16414854384535073119711619 24622281576802609679567429)
    ·
      refine ⟨4616677795650489314918893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24622281576802609679567429 4616677795650489314918893)
      ·
        refine ⟨1731254173368933493094585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4616677795650489314918893 1731254173368933493094585)
        ·
          refine ⟨1298440630026700119820939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1731254173368933493094585 1298440630026700119820939)
          ·
            refine ⟨1947660945040050179731409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298440630026700119820939 1947660945040050179731409)
            ·
              refine ⟨1460745708780037634798557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947660945040050179731409 1460745708780037634798557)
              ·
                refine ⟨547779640792514113049459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1460745708780037634798557 547779640792514113049459)
                ·
                  refine ⟨821669461188771169574189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 547779640792514113049459 821669461188771169574189)
                  ·
                    refine ⟨308126047945789188590321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 821669461188771169574189 308126047945789188590321)
                    ·
                      refine ⟨231094535959341891442741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 308126047945789188590321 231094535959341891442741)
                      ·
                        rfl

theorem cell23_450055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_450055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450055 prefixEnd_450055 := by exact prefixLift 450055
  have htrace : WordTrace (prefixWord ++ tailWord_450055) baseStart_450055 baseEnd_450055 := by
    simpa [prefixWord, tailWord_450055, baseEnd_450055] using wordTrace_append hprefix tailTrace_450055
  have hstable : (prefixWord ++ tailWord_450055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450055).length < 2 ^ (prefixWord ++ tailWord_450055).sum := by decide
  have hdescent : baseEnd_450055 < baseStart_450055 := by decide
  rcases family_descends (prefixWord ++ tailWord_450055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450102 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_450102 : Nat := 118140960795 + 450102 * 2 ^ 59
def prefixEnd_450102 : Nat := 4983230072969 + 3 ^ 40 * 450102 * 2
def baseEnd_450102 : Nat := 231118669550103207555025

theorem tailTrace_450102 : CollatzResearch.WordTrace tailWord_450102 prefixEnd_450102 231118669550103207555025 := by
  unfold tailWord_450102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1026035538460300009167035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10944379076909866764448373 1026035538460300009167035)
  ·
    refine ⟨1539053307690450013750553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1026035538460300009167035 1539053307690450013750553)
    ·
      refine ⟨1154289980767837510312915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1539053307690450013750553 1154289980767837510312915)
      ·
        refine ⟨1731434971151756265469373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154289980767837510312915 1731434971151756265469373)
        ·
          refine ⟨649288114181908599551015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1731434971151756265469373 649288114181908599551015)
          ·
            refine ⟨973932171272862899326523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649288114181908599551015 973932171272862899326523)
            ·
              refine ⟨1460898256909294348989785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973932171272862899326523 1460898256909294348989785)
              ·
                refine ⟨1095673692681970761742339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460898256909294348989785 1095673692681970761742339)
                ·
                  refine ⟨1643510539022956142613509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1095673692681970761742339 1643510539022956142613509)
                  ·
                    refine ⟨308158226066804276740033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1643510539022956142613509 308158226066804276740033)
                    ·
                      refine ⟨231118669550103207555025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 308158226066804276740033 231118669550103207555025)
                      ·
                        rfl

theorem cell23_450102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_450102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450102 prefixEnd_450102 := by exact prefixLift 450102
  have htrace : WordTrace (prefixWord ++ tailWord_450102) baseStart_450102 baseEnd_450102 := by
    simpa [prefixWord, tailWord_450102, baseEnd_450102] using wordTrace_append hprefix tailTrace_450102
  have hstable : (prefixWord ++ tailWord_450102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450102).length < 2 ^ (prefixWord ++ tailWord_450102).sum := by decide
  have hdescent : baseEnd_450102 < baseStart_450102 := by decide
  rcases family_descends (prefixWord ++ tailWord_450102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450181 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 8]
def baseStart_450181 : Nat := 118140960795 + 450181 * 2 ^ 59
def prefixEnd_450181 : Nat := 4983230072969 + 3 ^ 40 * 450181 * 2
def baseEnd_450181 : Nat := 25684359391312044274129

theorem tailTrace_450181 : CollatzResearch.WordTrace tailWord_450181 prefixEnd_450181 25684359391312044274129 := by
  unfold tailWord_450181
  simp only [CollatzResearch.WordTrace]
  refine ⟨16419449982078596638798397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10946299988052397759198931 16419449982078596638798397)
  ·
    refine ⟨6157293743279473739549399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16419449982078596638798397 6157293743279473739549399)
    ·
      refine ⟨9235940614919210609324099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6157293743279473739549399 9235940614919210609324099)
      ·
        refine ⟨13853910922378815913986149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9235940614919210609324099 13853910922378815913986149)
        ·
          refine ⟨2597608297946027983872403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13853910922378815913986149 2597608297946027983872403)
          ·
            refine ⟨3896412446919041975808605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597608297946027983872403 3896412446919041975808605)
            ·
              refine ⟨1461154667594640740928227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3896412446919041975808605 1461154667594640740928227)
              ·
                refine ⟨2191732001391961111392341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461154667594640740928227 2191732001391961111392341)
                ·
                  refine ⟨25684359391312044274129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2191732001391961111392341 25684359391312044274129)
                  ·
                    rfl

theorem cell23_450181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_450181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450181 prefixEnd_450181 := by exact prefixLift 450181
  have htrace : WordTrace (prefixWord ++ tailWord_450181) baseStart_450181 baseEnd_450181 := by
    simpa [prefixWord, tailWord_450181, baseEnd_450181] using wordTrace_append hprefix tailTrace_450181
  have hstable : (prefixWord ++ tailWord_450181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450181).length < 2 ^ (prefixWord ++ tailWord_450181).sum := by decide
  have hdescent : baseEnd_450181 < baseStart_450181 := by decide
  rcases family_descends (prefixWord ++ tailWord_450181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450185 : List Nat := [1, 2, 1, 1, 4, 1, 4, 4, 1, 4]
def baseStart_450185 : Nat := 118140960795 + 450185 * 2 ^ 59
def prefixEnd_450185 : Nat := 4983230072969 + 3 ^ 40 * 450185 * 2
def baseEnd_450185 : Nat := 77053762814808794272381

theorem tailTrace_450185 : CollatzResearch.WordTrace tailWord_450185 prefixEnd_450185 77053762814808794272381 := by
  unfold tailWord_450185
  simp only [CollatzResearch.WordTrace]
  refine ⟨16419595874064105321944009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10946397249376070214629339 16419595874064105321944009)
  ·
    refine ⟨12314696905548078991458007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16419595874064105321944009 12314696905548078991458007)
    ·
      refine ⟨18472045358322118487187011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12314696905548078991458007 18472045358322118487187011)
      ·
        refine ⟨27708068037483177730780517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18472045358322118487187011 27708068037483177730780517)
        ·
          refine ⟨5195262757028095824521347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27708068037483177730780517 5195262757028095824521347)
          ·
            refine ⟨7792894135542143736782021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5195262757028095824521347 7792894135542143736782021)
            ·
              refine ⟨1461167650414151950646629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7792894135542143736782021 1461167650414151950646629)
              ·
                refine ⟨273968934452653490746243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1461167650414151950646629 273968934452653490746243)
                ·
                  refine ⟨410953401678980236119365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273968934452653490746243 410953401678980236119365)
                  ·
                    refine ⟨77053762814808794272381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 410953401678980236119365 77053762814808794272381)
                    ·
                      rfl

theorem cell23_450185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 1, 4].length) (baseStart_450185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450185 prefixEnd_450185 := by exact prefixLift 450185
  have htrace : WordTrace (prefixWord ++ tailWord_450185) baseStart_450185 baseEnd_450185 := by
    simpa [prefixWord, tailWord_450185, baseEnd_450185] using wordTrace_append hprefix tailTrace_450185
  have hstable : (prefixWord ++ tailWord_450185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450185).length < 2 ^ (prefixWord ++ tailWord_450185).sum := by decide
  have hdescent : baseEnd_450185 < baseStart_450185 := by decide
  rcases family_descends (prefixWord ++ tailWord_450185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450191 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 3]
def baseStart_450191 : Nat := 118140960795 + 450191 * 2 ^ 59
def prefixEnd_450191 : Nat := 4983230072969 + 3 ^ 40 * 450191 * 2
def baseEnd_450191 : Nat := 231164369328353359342115

theorem tailTrace_450191 : CollatzResearch.WordTrace tailWord_450191 prefixEnd_450191 231164369328353359342115 := by
  unfold tailWord_450191
  simp only [CollatzResearch.WordTrace]
  refine ⟨16419814712042368346662427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10946543141361578897774951 16419814712042368346662427)
  ·
    refine ⟨24629722068063552519993641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16419814712042368346662427 24629722068063552519993641)
    ·
      refine ⟨18472291551047664389995231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24629722068063552519993641 18472291551047664389995231)
      ·
        refine ⟨27708437326571496584992847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18472291551047664389995231 27708437326571496584992847)
        ·
          refine ⟨41562655989857244877489271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27708437326571496584992847 41562655989857244877489271)
          ·
            refine ⟨62343983984785867316233907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41562655989857244877489271 62343983984785867316233907)
            ·
              refine ⟨93515975977178800974350861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62343983984785867316233907 93515975977178800974350861)
              ·
                refine ⟨35068490991442050365381573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93515975977178800974350861 35068490991442050365381573)
                ·
                  refine ⟨6575342060895384443509045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35068490991442050365381573 6575342060895384443509045)
                  ·
                    refine ⟨616438318208942291578973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6575342060895384443509045 616438318208942291578973)
                    ·
                      refine ⟨231164369328353359342115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 616438318208942291578973 231164369328353359342115)
                      ·
                        rfl

theorem cell23_450191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 3].length) (baseStart_450191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450191 prefixEnd_450191 := by exact prefixLift 450191
  have htrace : WordTrace (prefixWord ++ tailWord_450191) baseStart_450191 baseEnd_450191 := by
    simpa [prefixWord, tailWord_450191, baseEnd_450191] using wordTrace_append hprefix tailTrace_450191
  have hstable : (prefixWord ++ tailWord_450191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450191).length < 2 ^ (prefixWord ++ tailWord_450191).sum := by decide
  have hdescent : baseEnd_450191 < baseStart_450191 := by decide
  rcases family_descends (prefixWord ++ tailWord_450191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450248 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_450248 : Nat := 118140960795 + 450248 * 2 ^ 59
def prefixEnd_450248 : Nat := 4983230072969 + 3 ^ 40 * 450248 * 2
def baseEnd_450248 : Nat := 231193637725659636329353

theorem tailTrace_450248 : CollatzResearch.WordTrace tailWord_450248 prefixEnd_450248 231193637725659636329353 := by
  unfold tailWord_450248
  simp only [CollatzResearch.WordTrace]
  refine ⟨8210946836417933540743699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10947929115223911387658265 8210946836417933540743699)
  ·
    refine ⟨12316420254626900311115549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8210946836417933540743699 12316420254626900311115549)
    ·
      refine ⟨4618657595485087616668331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12316420254626900311115549 4618657595485087616668331)
      ·
        refine ⟨6927986393227631425002497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618657595485087616668331 6927986393227631425002497)
        ·
          refine ⟨5195989794920723568751873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6927986393227631425002497 5195989794920723568751873)
          ·
            refine ⟨3896992346190542676563905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5195989794920723568751873 3896992346190542676563905)
            ·
              refine ⟨2922744259642907007422929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3896992346190542676563905 2922744259642907007422929)
              ·
                refine ⟨2192058194732180255567197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2922744259642907007422929 2192058194732180255567197)
                ·
                  refine ⟨822021823024567595837699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2192058194732180255567197 822021823024567595837699)
                  ·
                    refine ⟨1233032734536851393756549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 822021823024567595837699 1233032734536851393756549)
                    ·
                      refine ⟨231193637725659636329353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1233032734536851393756549 231193637725659636329353)
                      ·
                        rfl

theorem cell23_450248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_450248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450248 prefixEnd_450248 := by exact prefixLift 450248
  have htrace : WordTrace (prefixWord ++ tailWord_450248) baseStart_450248 baseEnd_450248 := by
    simpa [prefixWord, tailWord_450248, baseEnd_450248] using wordTrace_append hprefix tailTrace_450248
  have hstable : (prefixWord ++ tailWord_450248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450248).length < 2 ^ (prefixWord ++ tailWord_450248).sum := by decide
  have hdescent : baseEnd_450248 < baseStart_450248 := by decide
  rcases family_descends (prefixWord ++ tailWord_450248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450265 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 4]
def baseStart_450265 : Nat := 118140960795 + 450265 * 2 ^ 59
def prefixEnd_450265 : Nat := 4983230072969 + 3 ^ 40 * 450265 * 2
def baseEnd_450265 : Nat := 231202366896786069816775

theorem tailTrace_450265 : CollatzResearch.WordTrace tailWord_450265 prefixEnd_450265 231202366896786069816775 := by
  unfold tailWord_450265
  simp only [CollatzResearch.WordTrace]
  refine ⟨16422513713774278984856249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10948342475849519323237499 16422513713774278984856249)
  ·
    refine ⟨12316885285330709238642187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16422513713774278984856249 12316885285330709238642187)
    ·
      refine ⟨18475327927996063857963281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12316885285330709238642187 18475327927996063857963281)
      ·
        refine ⟨13856495945997047893472461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18475327927996063857963281 13856495945997047893472461)
        ·
          refine ⟨5196185979748892960052173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13856495945997047893472461 5196185979748892960052173)
          ·
            refine ⟨1948569742405834860019565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5196185979748892960052173 1948569742405834860019565)
            ·
              refine ⟨730713653402188072507337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1948569742405834860019565 730713653402188072507337)
              ·
                refine ⟨548035240051641054380503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730713653402188072507337 548035240051641054380503)
                ·
                  refine ⟨822052860077461581570755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548035240051641054380503 822052860077461581570755)
                  ·
                    refine ⟨1233079290116192372356133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 822052860077461581570755 1233079290116192372356133)
                    ·
                      refine ⟨231202366896786069816775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1233079290116192372356133 231202366896786069816775)
                      ·
                        rfl

theorem cell23_450265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_450265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450265 prefixEnd_450265 := by exact prefixLift 450265
  have htrace : WordTrace (prefixWord ++ tailWord_450265) baseStart_450265 baseEnd_450265 := by
    simpa [prefixWord, tailWord_450265, baseEnd_450265] using wordTrace_append hprefix tailTrace_450265
  have hstable : (prefixWord ++ tailWord_450265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450265).length < 2 ^ (prefixWord ++ tailWord_450265).sum := by decide
  have hdescent : baseEnd_450265 < baseStart_450265 := by decide
  rcases family_descends (prefixWord ++ tailWord_450265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450271 : List Nat := [1, 1, 2, 3, 2, 2, 1, 11]
def baseStart_450271 : Nat := 118140960795 + 450271 * 2 ^ 59
def prefixEnd_450271 : Nat := 4983230072969 + 3 ^ 40 * 450271 * 2
def baseEnd_450271 : Nat := 8563164732619001716361

theorem tailTrace_450271 : CollatzResearch.WordTrace tailWord_450271 prefixEnd_450271 8563164732619001716361 := by
  unfold tailWord_450271
  simp only [CollatzResearch.WordTrace]
  refine ⟨16422732551752542009574667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10948488367835028006383111 16422732551752542009574667)
  ·
    refine ⟨24634098827628813014362001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16422732551752542009574667 24634098827628813014362001)
    ·
      refine ⟨18475574120721609760771501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24634098827628813014362001 18475574120721609760771501)
      ·
        refine ⟨6928340295270603660289313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18475574120721609760771501 6928340295270603660289313)
        ·
          refine ⟨5196255221452952745216985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6928340295270603660289313 5196255221452952745216985)
          ·
            refine ⟨3897191416089714558912739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5196255221452952745216985 3897191416089714558912739)
            ·
              refine ⟨5845787124134571838369109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3897191416089714558912739 5845787124134571838369109)
              ·
                refine ⟨8563164732619001716361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 5845787124134571838369109 8563164732619001716361)
                ·
                  rfl

theorem cell23_450271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 11].length) (baseStart_450271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450271 prefixEnd_450271 := by exact prefixLift 450271
  have htrace : WordTrace (prefixWord ++ tailWord_450271) baseStart_450271 baseEnd_450271 := by
    simpa [prefixWord, tailWord_450271, baseEnd_450271] using wordTrace_append hprefix tailTrace_450271
  have hstable : (prefixWord ++ tailWord_450271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450271).length < 2 ^ (prefixWord ++ tailWord_450271).sum := by decide
  have hdescent : baseEnd_450271 < baseStart_450271 := by decide
  rcases family_descends (prefixWord ++ tailWord_450271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450275 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 1, 6]
def baseStart_450275 : Nat := 118140960795 + 450275 * 2 ^ 59
def prefixEnd_450275 : Nat := 4983230072969 + 3 ^ 40 * 450275 * 2
def baseEnd_450275 : Nat := 77069167234443676897243

theorem tailTrace_450275 : CollatzResearch.WordTrace tailWord_450275 prefixEnd_450275 77069167234443676897243 := by
  unfold tailWord_450275
  simp only [CollatzResearch.WordTrace]
  refine ⟨16422878443738050692720279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10948585629158700461813519 16422878443738050692720279)
  ·
    refine ⟨24634317665607076039080419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16422878443738050692720279 24634317665607076039080419)
    ·
      refine ⟨36951476498410614058620629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24634317665607076039080419 36951476498410614058620629)
      ·
        refine ⟨866050230431498766998921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 36951476498410614058620629 866050230431498766998921)
        ·
          refine ⟨649537672823624075249191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866050230431498766998921 649537672823624075249191)
          ·
            refine ⟨974306509235436112873787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649537672823624075249191 974306509235436112873787)
            ·
              refine ⟨1461459763853154169310681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974306509235436112873787 1461459763853154169310681)
              ·
                refine ⟨1096094822889865626983011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461459763853154169310681 1096094822889865626983011)
                ·
                  refine ⟨1644142234334798440474517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096094822889865626983011 1644142234334798440474517)
                  ·
                    refine ⟨77069167234443676897243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1644142234334798440474517 77069167234443676897243)
                    ·
                      rfl

theorem cell23_450275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 6].length) (baseStart_450275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450275 prefixEnd_450275 := by exact prefixLift 450275
  have htrace : WordTrace (prefixWord ++ tailWord_450275) baseStart_450275 baseEnd_450275 := by
    simpa [prefixWord, tailWord_450275, baseEnd_450275] using wordTrace_append hprefix tailTrace_450275
  have hstable : (prefixWord ++ tailWord_450275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450275).length < 2 ^ (prefixWord ++ tailWord_450275).sum := by decide
  have hdescent : baseEnd_450275 < baseStart_450275 := by decide
  rcases family_descends (prefixWord ++ tailWord_450275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450279 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 1, 5]
def baseStart_450279 : Nat := 118140960795 + 450279 * 2 ^ 59
def prefixEnd_450279 : Nat := 4983230072969 + 3 ^ 40 * 450279 * 2
def baseEnd_450279 : Nat := 77069851875316338347237

theorem tailTrace_450279 : CollatzResearch.WordTrace tailWord_450279 prefixEnd_450279 77069851875316338347237 := by
  unfold tailWord_450279
  simp only [CollatzResearch.WordTrace]
  refine ⟨16423024335723559375865891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10948682890482372917243927 16423024335723559375865891)
  ·
    refine ⟨24634536503585339063798837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16423024335723559375865891 24634536503585339063798837)
    ·
      refine ⟨2309487797211125537231141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24634536503585339063798837 2309487797211125537231141)
      ·
        refine ⟨433028961977086038230839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2309487797211125537231141 433028961977086038230839)
        ·
          refine ⟨649543442965629057346259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433028961977086038230839 649543442965629057346259)
          ·
            refine ⟨974315164448443586019389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649543442965629057346259 974315164448443586019389)
            ·
              refine ⟨365368186668166344757271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 974315164448443586019389 365368186668166344757271)
              ·
                refine ⟨548052280002249517135907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365368186668166344757271 548052280002249517135907)
                ·
                  refine ⟨822078420003374275703861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548052280002249517135907 822078420003374275703861)
                  ·
                    refine ⟨77069851875316338347237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 822078420003374275703861 77069851875316338347237)
                    ·
                      rfl

theorem cell23_450279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_450279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450279 prefixEnd_450279 := by exact prefixLift 450279
  have htrace : WordTrace (prefixWord ++ tailWord_450279) baseStart_450279 baseEnd_450279 := by
    simpa [prefixWord, tailWord_450279, baseEnd_450279] using wordTrace_append hprefix tailTrace_450279
  have hstable : (prefixWord ++ tailWord_450279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450279).length < 2 ^ (prefixWord ++ tailWord_450279).sum := by decide
  have hdescent : baseEnd_450279 < baseStart_450279 := by decide
  rcases family_descends (prefixWord ++ tailWord_450279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450285 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_450285 : Nat := 118140960795 + 450285 * 2 ^ 59
def prefixEnd_450285 : Nat := 4983230072969 + 3 ^ 40 * 450285 * 2
def baseEnd_450285 : Nat := 231212636509875991566683

theorem tailTrace_450285 : CollatzResearch.WordTrace tailWord_450285 prefixEnd_450285 231212636509875991566683 := by
  unfold tailWord_450285
  simp only [CollatzResearch.WordTrace]
  refine ⟨16423243173701822400584309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10948828782467881600389539 16423243173701822400584309)
  ·
    refine ⟨1539679047534545850054779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16423243173701822400584309 1539679047534545850054779)
    ·
      refine ⟨2309518571301818775082169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1539679047534545850054779 2309518571301818775082169)
      ·
        refine ⟨1732138928476364081311627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2309518571301818775082169 1732138928476364081311627)
        ·
          refine ⟨2598208392714546121967441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1732138928476364081311627 2598208392714546121967441)
          ·
            refine ⟨1948656294535909591475581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2598208392714546121967441 1948656294535909591475581)
            ·
              refine ⟨730746110450966096803343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1948656294535909591475581 730746110450966096803343)
              ·
                refine ⟨1096119165676449145205015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730746110450966096803343 1096119165676449145205015)
                ·
                  refine ⟨1644178748514673717807523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096119165676449145205015 1644178748514673717807523)
                  ·
                    refine ⟨2466268122772010576711285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1644178748514673717807523 2466268122772010576711285)
                    ·
                      refine ⟨231212636509875991566683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2466268122772010576711285 231212636509875991566683)
                      ·
                        rfl

theorem cell23_450285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_450285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450285 prefixEnd_450285 := by exact prefixLift 450285
  have htrace : WordTrace (prefixWord ++ tailWord_450285) baseStart_450285 baseEnd_450285 := by
    simpa [prefixWord, tailWord_450285, baseEnd_450285] using wordTrace_append hprefix tailTrace_450285
  have hstable : (prefixWord ++ tailWord_450285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450285).length < 2 ^ (prefixWord ++ tailWord_450285).sum := by decide
  have hdescent : baseEnd_450285 < baseStart_450285 := by decide
  rcases family_descends (prefixWord ++ tailWord_450285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450298 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3]
def baseStart_450298 : Nat := 118140960795 + 450298 * 2 ^ 59
def prefixEnd_450298 : Nat := 4983230072969 + 3 ^ 40 * 450298 * 2
def baseEnd_450298 : Nat := 231219311758384440704123

theorem tailTrace_450298 : CollatzResearch.WordTrace tailWord_450298 prefixEnd_450298 231219311758384440704123 := by
  unfold tailWord_450298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4105929330663681405201887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10949144881769817080538365 4105929330663681405201887)
  ·
    refine ⟨6158893995995522107802831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4105929330663681405201887 6158893995995522107802831)
    ·
      refine ⟨9238340993993283161704247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6158893995995522107802831 9238340993993283161704247)
      ·
        refine ⟨13857511490989924742556371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9238340993993283161704247 13857511490989924742556371)
        ·
          refine ⟨20786267236484887113834557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13857511490989924742556371 20786267236484887113834557)
          ·
            refine ⟨7794850213681832667687959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20786267236484887113834557 7794850213681832667687959)
            ·
              refine ⟨11692275320522749001531939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7794850213681832667687959 11692275320522749001531939)
              ·
                refine ⟨17538412980784123502297909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11692275320522749001531939 17538412980784123502297909)
                ·
                  refine ⟨1644226216948511578340429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17538412980784123502297909 1644226216948511578340429)
                  ·
                    refine ⟨616584831355691841877661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1644226216948511578340429 616584831355691841877661)
                    ·
                      refine ⟨231219311758384440704123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 616584831355691841877661 231219311758384440704123)
                      ·
                        rfl

theorem cell23_450298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_450298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450298 prefixEnd_450298 := by exact prefixLift 450298
  have htrace : WordTrace (prefixWord ++ tailWord_450298) baseStart_450298 baseEnd_450298 := by
    simpa [prefixWord, tailWord_450298, baseEnd_450298] using wordTrace_append hprefix tailTrace_450298
  have hstable : (prefixWord ++ tailWord_450298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450298).length < 2 ^ (prefixWord ++ tailWord_450298).sum := by decide
  have hdescent : baseEnd_450298 < baseStart_450298 := by decide
  rcases family_descends (prefixWord ++ tailWord_450298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450310 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_450310 : Nat := 118140960795 + 450310 * 2 ^ 59
def prefixEnd_450310 : Nat := 4983230072969 + 3 ^ 40 * 450310 * 2
def baseEnd_450310 : Nat := 231225473526238393754069

theorem tailTrace_450310 : CollatzResearch.WordTrace tailWord_450310 prefixEnd_450310 231225473526238393754069 := by
  unfold tailWord_450310
  simp only [CollatzResearch.WordTrace]
  refine ⟨513254843706601614695137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10949436665740834446829589 513254843706601614695137)
  ·
    refine ⟨384941132779951211021353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 513254843706601614695137 384941132779951211021353)
    ·
      refine ⟨288705849584963408266015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384941132779951211021353 288705849584963408266015)
      ·
        refine ⟨433058774377445112399023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288705849584963408266015 433058774377445112399023)
        ·
          refine ⟨649588161566167668598535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433058774377445112399023 649588161566167668598535)
          ·
            refine ⟨974382242349251502897803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649588161566167668598535 974382242349251502897803)
            ·
              refine ⟨1461573363523877254346705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974382242349251502897803 1461573363523877254346705)
              ·
                refine ⟨1096180022642907940760029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461573363523877254346705 1096180022642907940760029)
                ·
                  refine ⟨411067508491090477785011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096180022642907940760029 411067508491090477785011)
                  ·
                    refine ⟨616601262736635716677517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 411067508491090477785011 616601262736635716677517)
                    ·
                      refine ⟨231225473526238393754069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 616601262736635716677517 231225473526238393754069)
                      ·
                        rfl

theorem cell23_450310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_450310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450310 prefixEnd_450310 := by exact prefixLift 450310
  have htrace : WordTrace (prefixWord ++ tailWord_450310) baseStart_450310 baseEnd_450310 := by
    simpa [prefixWord, tailWord_450310, baseEnd_450310] using wordTrace_append hprefix tailTrace_450310
  have hstable : (prefixWord ++ tailWord_450310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450310).length < 2 ^ (prefixWord ++ tailWord_450310).sum := by decide
  have hdescent : baseEnd_450310 < baseStart_450310 := by decide
  rcases family_descends (prefixWord ++ tailWord_450310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450322 : List Nat := [3, 2, 4, 1, 1, 2, 3, 7]
def baseStart_450322 : Nat := 118140960795 + 450322 * 2 ^ 59
def prefixEnd_450322 : Nat := 4983230072969 + 3 ^ 40 * 450322 * 2
def baseEnd_450322 : Nat := 8564134640521938770519

theorem tailTrace_450322 : CollatzResearch.WordTrace tailWord_450322 prefixEnd_450322 8564134640521938770519 := by
  unfold tailWord_450322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106148168641944429920305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10949728449711851813120813 4106148168641944429920305)
  ·
    refine ⟨3079611126481458322440229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4106148168641944429920305 3079611126481458322440229)
    ·
      refine ⟨577427086215273435457543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3079611126481458322440229 577427086215273435457543)
      ·
        refine ⟨866140629322910153186315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577427086215273435457543 866140629322910153186315)
        ·
          refine ⟨1299210943984365229779473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866140629322910153186315 1299210943984365229779473)
          ·
            refine ⟨974408207988273922334605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1299210943984365229779473 974408207988273922334605)
            ·
              refine ⟨365403077995602720875477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 974408207988273922334605 365403077995602720875477)
              ·
                refine ⟨8564134640521938770519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 365403077995602720875477 8564134640521938770519)
                ·
                  rfl

theorem cell23_450322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 7].length) (baseStart_450322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450322 prefixEnd_450322 := by exact prefixLift 450322
  have htrace : WordTrace (prefixWord ++ tailWord_450322) baseStart_450322 baseEnd_450322 := by
    simpa [prefixWord, tailWord_450322, baseEnd_450322] using wordTrace_append hprefix tailTrace_450322
  have hstable : (prefixWord ++ tailWord_450322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450322).length < 2 ^ (prefixWord ++ tailWord_450322).sum := by decide
  have hdescent : baseEnd_450322 < baseStart_450322 := by decide
  rcases family_descends (prefixWord ++ tailWord_450322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450348 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_450348 : Nat := 118140960795 + 450348 * 2 ^ 59
def prefixEnd_450348 : Nat := 4983230072969 + 3 ^ 40 * 450348 * 2
def baseEnd_450348 : Nat := 77081661930369748359631

theorem tailTrace_450348 : CollatzResearch.WordTrace tailWord_450348 prefixEnd_450348 77081661930369748359631 := by
  unfold tailWord_450348
  simp only [CollatzResearch.WordTrace]
  refine ⟨8212770486236792080063849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10950360648315722773418465 8212770486236792080063849)
  ·
    refine ⟨6159577864677594060047887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8212770486236792080063849 6159577864677594060047887)
    ·
      refine ⟨9239366797016391090071831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6159577864677594060047887 9239366797016391090071831)
      ·
        refine ⟨13859050195524586635107747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9239366797016391090071831 13859050195524586635107747)
        ·
          refine ⟨20788575293286879952661621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13859050195524586635107747 20788575293286879952661621)
          ·
            refine ⟨1948928933745644995562027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20788575293286879952661621 1948928933745644995562027)
            ·
              refine ⟨2923393400618467493343041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948928933745644995562027 2923393400618467493343041)
              ·
                refine ⟨2192545050463850620007281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923393400618467493343041 2192545050463850620007281)
                ·
                  refine ⟨1644408787847887965005461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2192545050463850620007281 1644408787847887965005461)
                  ·
                    refine ⟨77081661930369748359631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1644408787847887965005461 77081661930369748359631)
                    ·
                      rfl

theorem cell23_450348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_450348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450348 prefixEnd_450348 := by exact prefixLift 450348
  have htrace : WordTrace (prefixWord ++ tailWord_450348) baseStart_450348 baseEnd_450348 := by
    simpa [prefixWord, tailWord_450348, baseEnd_450348] using wordTrace_append hprefix tailTrace_450348
  have hstable : (prefixWord ++ tailWord_450348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450348).length < 2 ^ (prefixWord ++ tailWord_450348).sum := by decide
  have hdescent : baseEnd_450348 < baseStart_450348 := by decide
  rcases family_descends (prefixWord ++ tailWord_450348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450365 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_450365 : Nat := 118140960795 + 450365 * 2 ^ 59
def prefixEnd_450365 : Nat := 4983230072969 + 3 ^ 40 * 450365 * 2
def baseEnd_450365 : Nat := 77084571654078559522105

theorem tailTrace_450365 : CollatzResearch.WordTrace tailWord_450365 prefixEnd_450365 77084571654078559522105 := by
  unfold tailWord_450365
  simp only [CollatzResearch.WordTrace]
  refine ⟨16426161013411996063496549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10950774008941330708997699 16426161013411996063496549)
  ·
    refine ⟨3079905190014749261905603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16426161013411996063496549 3079905190014749261905603)
    ·
      refine ⟨4619857785022123892858405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3079905190014749261905603 4619857785022123892858405)
      ·
        refine ⟨866223334691648229910951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4619857785022123892858405 866223334691648229910951)
        ·
          refine ⟨1299335002037472344866427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866223334691648229910951 1299335002037472344866427)
          ·
            refine ⟨1949002503056208517299641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299335002037472344866427 1949002503056208517299641)
            ·
              refine ⟨1461751877292156387974731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1949002503056208517299641 1461751877292156387974731)
              ·
                refine ⟨2192627815938234581962097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1461751877292156387974731 2192627815938234581962097)
                ·
                  refine ⟨1644470861953675936471573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2192627815938234581962097 1644470861953675936471573)
                  ·
                    refine ⟨77084571654078559522105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1644470861953675936471573 77084571654078559522105)
                    ·
                      rfl

theorem cell23_450365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_450365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450365 prefixEnd_450365 := by exact prefixLift 450365
  have htrace : WordTrace (prefixWord ++ tailWord_450365) baseStart_450365 baseEnd_450365 := by
    simpa [prefixWord, tailWord_450365, baseEnd_450365] using wordTrace_append hprefix tailTrace_450365
  have hstable : (prefixWord ++ tailWord_450365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450365).length < 2 ^ (prefixWord ++ tailWord_450365).sum := by decide
  have hdescent : baseEnd_450365 < baseStart_450365 := by decide
  rcases family_descends (prefixWord ++ tailWord_450365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450366 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_450366 : Nat := 118140960795 + 450366 * 2 ^ 59
def prefixEnd_450366 : Nat := 4983230072969 + 3 ^ 40 * 450366 * 2
def baseEnd_450366 : Nat := 231254228442890174653811

theorem tailTrace_450366 : CollatzResearch.WordTrace tailWord_450366 prefixEnd_450366 231254228442890174653811 := by
  unfold tailWord_450366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2053274685801046654285369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10950798324272248822855301 2053274685801046654285369)
  ·
    refine ⟨1539956014350784990714027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2053274685801046654285369 1539956014350784990714027)
    ·
      refine ⟨2309934021526177486071041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1539956014350784990714027 2309934021526177486071041)
      ·
        refine ⟨1732450516144633114553281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2309934021526177486071041 1732450516144633114553281)
        ·
          refine ⟨1299337887108474835914961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1732450516144633114553281 1299337887108474835914961)
          ·
            refine ⟨974503415331356126936221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1299337887108474835914961 974503415331356126936221)
            ·
              refine ⟨365438780749258547601083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 974503415331356126936221 365438780749258547601083)
              ·
                refine ⟨548158171123887821401625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365438780749258547601083 548158171123887821401625)
                ·
                  refine ⟨411118628342915866051219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548158171123887821401625 411118628342915866051219)
                  ·
                    refine ⟨616677942514373799076829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 411118628342915866051219 616677942514373799076829)
                    ·
                      refine ⟨231254228442890174653811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 616677942514373799076829 231254228442890174653811)
                      ·
                        rfl

theorem cell23_450366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_450366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450366 prefixEnd_450366 := by exact prefixLift 450366
  have htrace : WordTrace (prefixWord ++ tailWord_450366) baseStart_450366 baseEnd_450366 := by
    simpa [prefixWord, tailWord_450366, baseEnd_450366] using wordTrace_append hprefix tailTrace_450366
  have hstable : (prefixWord ++ tailWord_450366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450366).length < 2 ^ (prefixWord ++ tailWord_450366).sum := by decide
  have hdescent : baseEnd_450366 < baseStart_450366 := by decide
  rcases family_descends (prefixWord ++ tailWord_450366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450378 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 7]
def baseStart_450378 : Nat := 118140960795 + 450378 * 2 ^ 59
def prefixEnd_450378 : Nat := 4983230072969 + 3 ^ 40 * 450378 * 2
def baseEnd_450378 : Nat := 25695598912304903078195

theorem tailTrace_450378 : CollatzResearch.WordTrace tailWord_450378 prefixEnd_450378 25695598912304903078195 := by
  unfold tailWord_450378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106658790591224820929947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10951090108243266189146525 4106658790591224820929947)
  ·
    refine ⟨6159988185886837231394921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4106658790591224820929947 6159988185886837231394921)
    ·
      refine ⟨4619991139415127923546191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6159988185886837231394921 4619991139415127923546191)
      ·
        refine ⟨6929986709122691885319287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4619991139415127923546191 6929986709122691885319287)
        ·
          refine ⟨10394980063684037827978931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6929986709122691885319287 10394980063684037827978931)
          ·
            refine ⟨15592470095526056741968397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10394980063684037827978931 15592470095526056741968397)
            ·
              refine ⟨5847176285822271278238149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15592470095526056741968397 5847176285822271278238149)
              ·
                refine ⟨1096345553591675864669653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5847176285822271278238149 1096345553591675864669653)
                ·
                  refine ⟨25695598912304903078195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1096345553591675864669653 25695598912304903078195)
                  ·
                    rfl

theorem cell23_450378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_450378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450378 prefixEnd_450378 := by exact prefixLift 450378
  have htrace : WordTrace (prefixWord ++ tailWord_450378) baseStart_450378 baseEnd_450378 := by
    simpa [prefixWord, tailWord_450378, baseEnd_450378] using wordTrace_append hprefix tailTrace_450378
  have hstable : (prefixWord ++ tailWord_450378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450378).length < 2 ^ (prefixWord ++ tailWord_450378).sum := by decide
  have hdescent : baseEnd_450378 < baseStart_450378 := by decide
  rcases family_descends (prefixWord ++ tailWord_450378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450448 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_450448 : Nat := 118140960795 + 450448 * 2 ^ 59
def prefixEnd_450448 : Nat := 4983230072969 + 3 ^ 40 * 450448 * 2
def baseEnd_450448 : Nat := 231296333856558853828433

theorem tailTrace_450448 : CollatzResearch.WordTrace tailWord_450448 prefixEnd_450448 231296333856558853828433 := by
  unfold tailWord_450448
  simp only [CollatzResearch.WordTrace]
  refine ⟨8214594136055650619383999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10952792181407534159178665 8214594136055650619383999)
  ·
    refine ⟨12321891204083475929075999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8214594136055650619383999 12321891204083475929075999)
    ·
      refine ⟨18482836806125213893613999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12321891204083475929075999 18482836806125213893613999)
      ·
        refine ⟨27724255209187820840420999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18482836806125213893613999 27724255209187820840420999)
        ·
          refine ⟨41586382813781731260631499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27724255209187820840420999 41586382813781731260631499)
          ·
            refine ⟨62379574220672596890947249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41586382813781731260631499 62379574220672596890947249)
            ·
              refine ⟨46784680665504447668210437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62379574220672596890947249 46784680665504447668210437)
              ·
                refine ⟨8772127624782083937789457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46784680665504447668210437 8772127624782083937789457)
                ·
                  refine ⟨6579095718586562953342093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8772127624782083937789457 6579095718586562953342093)
                  ·
                    refine ⟨2467160894469961107503285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6579095718586562953342093 2467160894469961107503285)
                    ·
                      refine ⟨231296333856558853828433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2467160894469961107503285 231296333856558853828433)
                      ·
                        rfl

theorem cell23_450448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_450448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450448 prefixEnd_450448 := by exact prefixLift 450448
  have htrace : WordTrace (prefixWord ++ tailWord_450448) baseStart_450448 baseEnd_450448 := by
    simpa [prefixWord, tailWord_450448, baseEnd_450448] using wordTrace_append hprefix tailTrace_450448
  have hstable : (prefixWord ++ tailWord_450448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450448).length < 2 ^ (prefixWord ++ tailWord_450448).sum := by decide
  have hdescent : baseEnd_450448 < baseStart_450448 := by decide
  rcases family_descends (prefixWord ++ tailWord_450448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450552 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 1, 1, 4]
def baseStart_450552 : Nat := 118140960795 + 450552 * 2 ^ 59
def prefixEnd_450552 : Nat := 4983230072969 + 3 ^ 40 * 450552 * 2
def baseEnd_450552 : Nat := 231349735844626446927955

theorem tailTrace_450552 : CollatzResearch.WordTrace tailWord_450552 prefixEnd_450552 231349735844626446927955 := by
  unfold tailWord_450552
  simp only [CollatzResearch.WordTrace]
  refine ⟨8216490731867263500276955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10955320975823018000369273 8216490731867263500276955)
  ·
    refine ⟨12324736097800895250415433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8216490731867263500276955 12324736097800895250415433)
    ·
      refine ⟨9243552073350671437811575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12324736097800895250415433 9243552073350671437811575)
      ·
        refine ⟨13865328110026007156717363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9243552073350671437811575 13865328110026007156717363)
        ·
          refine ⟨20797992165039010735076045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13865328110026007156717363 20797992165039010735076045)
          ·
            refine ⟨7799247061889629025653517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20797992165039010735076045 7799247061889629025653517)
            ·
              refine ⟨2924717648208610884620069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7799247061889629025653517 2924717648208610884620069)
              ·
                refine ⟨548384559039114540866263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2924717648208610884620069 548384559039114540866263)
                ·
                  refine ⟨822576838558671811299395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548384559039114540866263 822576838558671811299395)
                  ·
                    refine ⟨1233865257838007716949093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 822576838558671811299395 1233865257838007716949093)
                    ·
                      refine ⟨231349735844626446927955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1233865257838007716949093 231349735844626446927955)
                      ·
                        rfl

theorem cell23_450552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_450552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450552 prefixEnd_450552 := by exact prefixLift 450552
  have htrace : WordTrace (prefixWord ++ tailWord_450552) baseStart_450552 baseEnd_450552 := by
    simpa [prefixWord, tailWord_450552, baseEnd_450552] using wordTrace_append hprefix tailTrace_450552
  have hstable : (prefixWord ++ tailWord_450552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450552).length < 2 ^ (prefixWord ++ tailWord_450552).sum := by decide
  have hdescent : baseEnd_450552 < baseStart_450552 := by decide
  rcases family_descends (prefixWord ++ tailWord_450552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450572 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 1, 1, 5]
def baseStart_450572 : Nat := 118140960795 + 450572 * 2 ^ 59
def prefixEnd_450572 : Nat := 4983230072969 + 3 ^ 40 * 450572 * 2
def baseEnd_450572 : Nat := 231360005457716368677863

theorem tailTrace_450572 : CollatzResearch.WordTrace tailWord_450572 prefixEnd_450572 231360005457716368677863 := by
  unfold tailWord_450572
  simp only [CollatzResearch.WordTrace]
  refine ⟨8216855461831035208140985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10955807282441380277521313 8216855461831035208140985)
  ·
    refine ⟨6162641596373276406105739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8216855461831035208140985 6162641596373276406105739)
    ·
      refine ⟨9243962394559914609158609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6162641596373276406105739 9243962394559914609158609)
      ·
        refine ⟨6932971795919935956868957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9243962394559914609158609 6932971795919935956868957)
        ·
          refine ⟨2599864423469975983825859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6932971795919935956868957 2599864423469975983825859)
          ·
            refine ⟨3899796635204963975738789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599864423469975983825859 3899796635204963975738789)
            ·
              refine ⟨731211869100930745451023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3899796635204963975738789 731211869100930745451023)
              ·
                refine ⟨1096817803651396118176535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731211869100930745451023 1096817803651396118176535)
                ·
                  refine ⟨1645226705477094177264803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1096817803651396118176535 1645226705477094177264803)
                  ·
                    refine ⟨2467840058215641265897205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1645226705477094177264803 2467840058215641265897205)
                    ·
                      refine ⟨231360005457716368677863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2467840058215641265897205 231360005457716368677863)
                      ·
                        rfl

theorem cell23_450572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_450572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450572 prefixEnd_450572 := by exact prefixLift 450572
  have htrace : WordTrace (prefixWord ++ tailWord_450572) baseStart_450572 baseEnd_450572 := by
    simpa [prefixWord, tailWord_450572, baseEnd_450572] using wordTrace_append hprefix tailTrace_450572
  have hstable : (prefixWord ++ tailWord_450572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450572).length < 2 ^ (prefixWord ++ tailWord_450572).sum := by decide
  have hdescent : baseEnd_450572 < baseStart_450572 := by decide
  rcases family_descends (prefixWord ++ tailWord_450572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450580 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_450580 : Nat := 118140960795 + 450580 * 2 ^ 59
def prefixEnd_450580 : Nat := 4983230072969 + 3 ^ 40 * 450580 * 2
def baseEnd_450580 : Nat := 231364113302952337377827

theorem tailTrace_450580 : CollatzResearch.WordTrace tailWord_450580 prefixEnd_450580 231364113302952337377827 := by
  unfold tailWord_450580
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217001353816543891286597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10956001805088725188382129 8217001353816543891286597)
  ·
    refine ⟨1540687753840601979616237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8217001353816543891286597 1540687753840601979616237)
    ·
      refine ⟨577757907690225742356089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1540687753840601979616237 577757907690225742356089)
      ·
        refine ⟨433318430767669306767067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577757907690225742356089 433318430767669306767067)
        ·
          refine ⟨649977646151503960150601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433318430767669306767067 649977646151503960150601)
          ·
            refine ⟨487483234613627970112951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649977646151503960150601 487483234613627970112951)
            ·
              refine ⟨731224851920441955169427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487483234613627970112951 731224851920441955169427)
              ·
                refine ⟨1096837277880662932754141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731224851920441955169427 1096837277880662932754141)
                ·
                  refine ⟨411313979205248599782803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096837277880662932754141 411313979205248599782803)
                  ·
                    refine ⟨616970968807872899674205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 411313979205248599782803 616970968807872899674205)
                    ·
                      refine ⟨231364113302952337377827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 616970968807872899674205 231364113302952337377827)
                      ·
                        rfl

theorem cell23_450580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_450580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450580 prefixEnd_450580 := by exact prefixLift 450580
  have htrace : WordTrace (prefixWord ++ tailWord_450580) baseStart_450580 baseEnd_450580 := by
    simpa [prefixWord, tailWord_450580, baseEnd_450580] using wordTrace_append hprefix tailTrace_450580
  have hstable : (prefixWord ++ tailWord_450580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450580).length < 2 ^ (prefixWord ++ tailWord_450580).sum := by decide
  have hdescent : baseEnd_450580 < baseStart_450580 := by decide
  rcases family_descends (prefixWord ++ tailWord_450580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450586 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2]
def baseStart_450586 : Nat := 118140960795 + 450586 * 2 ^ 59
def prefixEnd_450586 : Nat := 4983230072969 + 3 ^ 40 * 450586 * 2
def baseEnd_450586 : Nat := 231367194186879313902799

theorem tailTrace_450586 : CollatzResearch.WordTrace tailWord_450586 prefixEnd_450586 231367194186879313902799 := by
  unfold tailWord_450586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4108555386402837701822903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10956147697074233871527741 4108555386402837701822903)
  ·
    refine ⟨6162833079604256552734355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4108555386402837701822903 6162833079604256552734355)
    ·
      refine ⟨9244249619406384829101533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6162833079604256552734355 9244249619406384829101533)
      ·
        refine ⟨3466593607277394310913075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9244249619406384829101533 3466593607277394310913075)
        ·
          refine ⟨5199890410916091466369613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3466593607277394310913075 5199890410916091466369613)
          ·
            refine ⟨1949958904093534299888605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5199890410916091466369613 1949958904093534299888605)
            ·
              refine ⟨731234589035075362458227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1949958904093534299888605 731234589035075362458227)
              ·
                refine ⟨1096851883552613043687341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731234589035075362458227 1096851883552613043687341)
                ·
                  refine ⟨411319456332229891382753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1096851883552613043687341 411319456332229891382753)
                  ·
                    refine ⟨308489592249172418537065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 411319456332229891382753 308489592249172418537065)
                    ·
                      refine ⟨231367194186879313902799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 308489592249172418537065 231367194186879313902799)
                      ·
                        rfl

theorem cell23_450586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_450586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450586 prefixEnd_450586 := by exact prefixLift 450586
  have htrace : WordTrace (prefixWord ++ tailWord_450586) baseStart_450586 baseEnd_450586 := by
    simpa [prefixWord, tailWord_450586, baseEnd_450586] using wordTrace_append hprefix tailTrace_450586
  have hstable : (prefixWord ++ tailWord_450586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450586).length < 2 ^ (prefixWord ++ tailWord_450586).sum := by decide
  have hdescent : baseEnd_450586 < baseStart_450586 := by decide
  rcases family_descends (prefixWord ++ tailWord_450586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450595 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 6]
def baseStart_450595 : Nat := 118140960795 + 450595 * 2 ^ 59
def prefixEnd_450595 : Nat := 4983230072969 + 3 ^ 40 * 450595 * 2
def baseEnd_450595 : Nat := 231371815512769778690257

theorem tailTrace_450595 : CollatzResearch.WordTrace tailWord_450595 prefixEnd_450595 231371815512769778690257 := by
  unfold tailWord_450595
  simp only [CollatzResearch.WordTrace]
  refine ⟨16434549802578745344369239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10956366535052496896246159 16434549802578745344369239)
  ·
    refine ⟨24651824703868118016553859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16434549802578745344369239 24651824703868118016553859)
    ·
      refine ⟨36977737055802177024830789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24651824703868118016553859 36977737055802177024830789)
      ·
        refine ⟨6933325697962908192155773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36977737055802177024830789 6933325697962908192155773)
        ·
          refine ⟨2599997136736090572058415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6933325697962908192155773 2599997136736090572058415)
          ·
            refine ⟨3899995705104135858087623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599997136736090572058415 3899995705104135858087623)
            ·
              refine ⟨5849993557656203787131435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3899995705104135858087623 5849993557656203787131435)
              ·
                refine ⟨8774990336484305680697153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5849993557656203787131435 8774990336484305680697153)
                ·
                  refine ⟨6581242752363229260522865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8774990336484305680697153 6581242752363229260522865)
                  ·
                    refine ⟨4935932064272421945392149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6581242752363229260522865 4935932064272421945392149)
                    ·
                      refine ⟨231371815512769778690257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4935932064272421945392149 231371815512769778690257)
                      ·
                        rfl

theorem cell23_450595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_450595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450595 prefixEnd_450595 := by exact prefixLift 450595
  have htrace : WordTrace (prefixWord ++ tailWord_450595) baseStart_450595 baseEnd_450595 := by
    simpa [prefixWord, tailWord_450595, baseEnd_450595] using wordTrace_append hprefix tailTrace_450595
  have hstable : (prefixWord ++ tailWord_450595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450595).length < 2 ^ (prefixWord ++ tailWord_450595).sum := by decide
  have hdescent : baseEnd_450595 < baseStart_450595 := by decide
  rcases family_descends (prefixWord ++ tailWord_450595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450596 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_450596 : Nat := 118140960795 + 450596 * 2 ^ 59
def prefixEnd_450596 : Nat := 4983230072969 + 3 ^ 40 * 450596 * 2
def baseEnd_450596 : Nat := 77124109664474758259251

theorem tailTrace_450596 : CollatzResearch.WordTrace tailWord_450596 prefixEnd_450596 77124109664474758259251 := by
  unfold tailWord_450596
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217293137787561257577821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10956390850383415010103761 8217293137787561257577821)
  ·
    refine ⟨3081484926670335471591683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8217293137787561257577821 3081484926670335471591683)
    ·
      refine ⟨4622227390005503207387525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3081484926670335471591683 4622227390005503207387525)
      ·
        refine ⟨866667635626031851385161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4622227390005503207387525 866667635626031851385161)
        ·
          refine ⟨650000726719523888538871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866667635626031851385161 650000726719523888538871)
          ·
            refine ⟨975001090079285832808307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650000726719523888538871 975001090079285832808307)
            ·
              refine ⟨1462501635118928749212461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975001090079285832808307 1462501635118928749212461)
              ·
                refine ⟨548438113169598280954673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1462501635118928749212461 548438113169598280954673)
                ·
                  refine ⟨411328584877198710716005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548438113169598280954673 411328584877198710716005)
                  ·
                    refine ⟨77124109664474758259251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 411328584877198710716005 77124109664474758259251)
                    ·
                      rfl

theorem cell23_450596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_450596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450596 prefixEnd_450596 := by exact prefixLift 450596
  have htrace : WordTrace (prefixWord ++ tailWord_450596) baseStart_450596 baseEnd_450596 := by
    simpa [prefixWord, tailWord_450596, baseEnd_450596] using wordTrace_append hprefix tailTrace_450596
  have hstable : (prefixWord ++ tailWord_450596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450596).length < 2 ^ (prefixWord ++ tailWord_450596).sum := by decide
  have hdescent : baseEnd_450596 < baseStart_450596 := by decide
  rcases family_descends (prefixWord ++ tailWord_450596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450606 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_450606 : Nat := 118140960795 + 450606 * 2 ^ 59
def prefixEnd_450606 : Nat := 4983230072969 + 3 ^ 40 * 450606 * 2
def baseEnd_450606 : Nat := 231377463799969235652707

theorem tailTrace_450606 : CollatzResearch.WordTrace tailWord_450606 prefixEnd_450606 231377463799969235652707 := by
  unfold tailWord_450606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2054368875692361777877459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10956634003692596148679781 2054368875692361777877459)
  ·
    refine ⟨3081553313538542666816189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2054368875692361777877459 3081553313538542666816189)
    ·
      refine ⟨1155582492576953500056071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3081553313538542666816189 1155582492576953500056071)
      ·
        refine ⟨1733373738865430250084107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155582492576953500056071 1733373738865430250084107)
        ·
          refine ⟨2600060608298145375126161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733373738865430250084107 2600060608298145375126161)
          ·
            refine ⟨1950045456223609031344621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2600060608298145375126161 1950045456223609031344621)
            ·
              refine ⟨731267046083853386754233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1950045456223609031344621 731267046083853386754233)
              ·
                refine ⟨548450284562890040065675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731267046083853386754233 548450284562890040065675)
                ·
                  refine ⟨822675426844335060098513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 548450284562890040065675 822675426844335060098513)
                  ·
                    refine ⟨617006570133251295073885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 822675426844335060098513 617006570133251295073885)
                    ·
                      refine ⟨231377463799969235652707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 617006570133251295073885 231377463799969235652707)
                      ·
                        rfl

theorem cell23_450606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_450606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450606 prefixEnd_450606 := by exact prefixLift 450606
  have htrace : WordTrace (prefixWord ++ tailWord_450606) baseStart_450606 baseEnd_450606 := by
    simpa [prefixWord, tailWord_450606, baseEnd_450606] using wordTrace_append hprefix tailTrace_450606
  have hstable : (prefixWord ++ tailWord_450606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450606).length < 2 ^ (prefixWord ++ tailWord_450606).sum := by decide
  have hdescent : baseEnd_450606 < baseStart_450606 := by decide
  rcases family_descends (prefixWord ++ tailWord_450606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450615 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_450615 : Nat := 118140960795 + 450615 * 2 ^ 59
def prefixEnd_450615 : Nat := 4983230072969 + 3 ^ 40 * 450615 * 2
def baseEnd_450615 : Nat := 231382085125859700440165

theorem tailTrace_450615 : CollatzResearch.WordTrace tailWord_450615 prefixEnd_450615 231382085125859700440165 := by
  unfold tailWord_450615
  simp only [CollatzResearch.WordTrace]
  refine ⟨16435279262506288760097299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10956852841670859173398199 16435279262506288760097299)
  ·
    refine ⟨24652918893759433140145949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16435279262506288760097299 24652918893759433140145949)
    ·
      refine ⟨9244844585159787427554731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24652918893759433140145949 9244844585159787427554731)
      ·
        refine ⟨13867266877739681141332097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9244844585159787427554731 13867266877739681141332097)
        ·
          refine ⟨10400450158304760855999073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13867266877739681141332097 10400450158304760855999073)
          ·
            refine ⟨7800337618728570641999305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10400450158304760855999073 7800337618728570641999305)
            ·
              refine ⟨5850253214046427981499479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7800337618728570641999305 5850253214046427981499479)
              ·
                refine ⟨8775379821069641972249219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5850253214046427981499479 8775379821069641972249219)
                ·
                  refine ⟨13163069731604462958373829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8775379821069641972249219 13163069731604462958373829)
                  ·
                    refine ⟨2468075574675836804695093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13163069731604462958373829 2468075574675836804695093)
                    ·
                      refine ⟨231382085125859700440165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2468075574675836804695093 231382085125859700440165)
                      ·
                        rfl

theorem cell23_450615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_450615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450615 prefixEnd_450615 := by exact prefixLift 450615
  have htrace : WordTrace (prefixWord ++ tailWord_450615) baseStart_450615 baseEnd_450615 := by
    simpa [prefixWord, tailWord_450615, baseEnd_450615] using wordTrace_append hprefix tailTrace_450615
  have hstable : (prefixWord ++ tailWord_450615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450615).length < 2 ^ (prefixWord ++ tailWord_450615).sum := by decide
  have hdescent : baseEnd_450615 < baseStart_450615 := by decide
  rcases family_descends (prefixWord ++ tailWord_450615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450635 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 4, 6]
def baseStart_450635 : Nat := 118140960795 + 450635 * 2 ^ 59
def prefixEnd_450635 : Nat := 4983230072969 + 3 ^ 40 * 450635 * 2
def baseEnd_450635 : Nat := 77130784912983207396691

theorem tailTrace_450635 : CollatzResearch.WordTrace tailWord_450635 prefixEnd_450635 77130784912983207396691 := by
  unfold tailWord_450635
  simp only [CollatzResearch.WordTrace]
  refine ⟨16436008722433832175825359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10957339148289221450550239 16436008722433832175825359)
  ·
    refine ⟨24654013083650748263738039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16436008722433832175825359 24654013083650748263738039)
    ·
      refine ⟨36981019625476122395607059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24654013083650748263738039 36981019625476122395607059)
      ·
        refine ⟨55471529438214183593410589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36981019625476122395607059 55471529438214183593410589)
        ·
          refine ⟨20801823539330318847528971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55471529438214183593410589 20801823539330318847528971)
          ·
            refine ⟨31202735308995478271293457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20801823539330318847528971 31202735308995478271293457)
            ·
              refine ⟨23402051481746608703470093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31202735308995478271293457 23402051481746608703470093)
              ·
                refine ⟨8775769305654978263801285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23402051481746608703470093 8775769305654978263801285)
                ·
                  refine ⟨1645456744810308424462741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8775769305654978263801285 1645456744810308424462741)
                  ·
                    refine ⟨77130784912983207396691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1645456744810308424462741 77130784912983207396691)
                    ·
                      rfl

theorem cell23_450635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 6].length) (baseStart_450635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450635 prefixEnd_450635 := by exact prefixLift 450635
  have htrace : WordTrace (prefixWord ++ tailWord_450635) baseStart_450635 baseEnd_450635 := by
    simpa [prefixWord, tailWord_450635, baseEnd_450635] using wordTrace_append hprefix tailTrace_450635
  have hstable : (prefixWord ++ tailWord_450635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450635).length < 2 ^ (prefixWord ++ tailWord_450635).sum := by decide
  have hdescent : baseEnd_450635 < baseStart_450635 := by decide
  rcases family_descends (prefixWord ++ tailWord_450635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450652 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_450652 : Nat := 118140960795 + 450652 * 2 ^ 59
def prefixEnd_450652 : Nat := 4983230072969 + 3 ^ 40 * 450652 * 2
def baseEnd_450652 : Nat := 77133694636692018559165

theorem tailTrace_450652 : CollatzResearch.WordTrace tailWord_450652 prefixEnd_450652 77133694636692018559165 := by
  unfold tailWord_450652
  simp only [CollatzResearch.WordTrace]
  refine ⟨8218314381686122039597105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10957752508914829386129473 8218314381686122039597105)
  ·
    refine ⟨6163735786264591529697829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8218314381686122039597105 6163735786264591529697829)
    ·
      refine ⟨1155700459924610911818343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6163735786264591529697829 1155700459924610911818343)
      ·
        refine ⟨1733550689886916367727515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155700459924610911818343 1733550689886916367727515)
        ·
          refine ⟨2600326034830374551591273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733550689886916367727515 2600326034830374551591273)
          ·
            refine ⟨1950244526122780913693455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2600326034830374551591273 1950244526122780913693455)
            ·
              refine ⟨2925366789184171370540183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1950244526122780913693455 2925366789184171370540183)
              ·
                refine ⟨4388050183776257055810275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2925366789184171370540183 4388050183776257055810275)
                ·
                  refine ⟨6582075275664385583715413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4388050183776257055810275 6582075275664385583715413)
                  ·
                    refine ⟨77133694636692018559165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6582075275664385583715413 77133694636692018559165)
                    ·
                      rfl

theorem cell23_450652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_450652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450652 prefixEnd_450652 := by exact prefixLift 450652
  have htrace : WordTrace (prefixWord ++ tailWord_450652) baseStart_450652 baseEnd_450652 := by
    simpa [prefixWord, tailWord_450652, baseEnd_450652] using wordTrace_append hprefix tailTrace_450652
  have hstable : (prefixWord ++ tailWord_450652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450652).length < 2 ^ (prefixWord ++ tailWord_450652).sum := by decide
  have hdescent : baseEnd_450652 < baseStart_450652 := by decide
  rcases family_descends (prefixWord ++ tailWord_450652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450653 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_450653 : Nat := 118140960795 + 450653 * 2 ^ 59
def prefixEnd_450653 : Nat := 4983230072969 + 3 ^ 40 * 450653 * 2
def baseEnd_450653 : Nat := 231401597390730551764991

theorem tailTrace_450653 : CollatzResearch.WordTrace tailWord_450653 prefixEnd_450653 231401597390730551764991 := by
  unfold tailWord_450653
  simp only [CollatzResearch.WordTrace]
  refine ⟨16436665236368621249980613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10957776824245747499987075 16436665236368621249980613)
  ·
    refine ⟨3081874731819116484371365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16436665236368621249980613 3081874731819116484371365)
    ·
      refine ⟨577851512216084340819631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3081874731819116484371365 577851512216084340819631)
      ·
        refine ⟨866777268324126511229447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577851512216084340819631 866777268324126511229447)
        ·
          refine ⟨1300165902486189766844171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866777268324126511229447 1300165902486189766844171)
          ·
            refine ⟨1950248853729284650266257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300165902486189766844171 1950248853729284650266257)
            ·
              refine ⟨1462686640296963487699693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1950248853729284650266257 1462686640296963487699693)
              ·
                refine ⟨548507490111361307887385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1462686640296963487699693 548507490111361307887385)
                ·
                  refine ⟨411380617583520980915539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548507490111361307887385 411380617583520980915539)
                  ·
                    refine ⟨617070926375281471373309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 411380617583520980915539 617070926375281471373309)
                    ·
                      refine ⟨231401597390730551764991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 617070926375281471373309 231401597390730551764991)
                      ·
                        rfl

theorem cell23_450653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_450653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450653 prefixEnd_450653 := by exact prefixLift 450653
  have htrace : WordTrace (prefixWord ++ tailWord_450653) baseStart_450653 baseEnd_450653 := by
    simpa [prefixWord, tailWord_450653, baseEnd_450653] using wordTrace_append hprefix tailTrace_450653
  have hstable : (prefixWord ++ tailWord_450653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450653).length < 2 ^ (prefixWord ++ tailWord_450653).sum := by decide
  have hdescent : baseEnd_450653 < baseStart_450653 := by decide
  rcases family_descends (prefixWord ++ tailWord_450653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450659 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 1, 4, 2]
def baseStart_450659 : Nat := 118140960795 + 450659 * 2 ^ 59
def prefixEnd_450659 : Nat := 4983230072969 + 3 ^ 40 * 450659 * 2
def baseEnd_450659 : Nat := 231404678274657528289963

theorem tailTrace_450659 : CollatzResearch.WordTrace tailWord_450659 prefixEnd_450659 231404678274657528289963 := by
  unfold tailWord_450659
  simp only [CollatzResearch.WordTrace]
  refine ⟨16436884074346884274699031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10957922716231256183132687 16436884074346884274699031)
  ·
    refine ⟨24655326111520326412048547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16436884074346884274699031 24655326111520326412048547)
    ·
      refine ⟨36982989167280489618072821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24655326111520326412048547 36982989167280489618072821)
      ·
        refine ⟨3467155234432545901694327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36982989167280489618072821 3467155234432545901694327)
        ·
          refine ⟨5200732851648818852541491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3467155234432545901694327 5200732851648818852541491)
          ·
            refine ⟨7801099277473228278812237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5200732851648818852541491 7801099277473228278812237)
            ·
              refine ⟨2925412229052460604554589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7801099277473228278812237 2925412229052460604554589)
              ·
                refine ⟨1097029585894672726707971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2925412229052460604554589 1097029585894672726707971)
                ·
                  refine ⟨1645544378842009090061957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1097029585894672726707971 1645544378842009090061957)
                  ·
                    refine ⟨308539571032876704386617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1645544378842009090061957 308539571032876704386617)
                    ·
                      refine ⟨231404678274657528289963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 308539571032876704386617 231404678274657528289963)
                      ·
                        rfl

theorem cell23_450659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_450659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450659 prefixEnd_450659 := by exact prefixLift 450659
  have htrace : WordTrace (prefixWord ++ tailWord_450659) baseStart_450659 baseEnd_450659 := by
    simpa [prefixWord, tailWord_450659, baseEnd_450659] using wordTrace_append hprefix tailTrace_450659
  have hstable : (prefixWord ++ tailWord_450659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450659).length < 2 ^ (prefixWord ++ tailWord_450659).sum := by decide
  have hdescent : baseEnd_450659 < baseStart_450659 := by decide
  rcases family_descends (prefixWord ++ tailWord_450659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_450693 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 2, 2, 2]
def baseStart_450693 : Nat := 118140960795 + 450693 * 2 ^ 59
def prefixEnd_450693 : Nat := 4983230072969 + 3 ^ 40 * 450693 * 2
def baseEnd_450693 : Nat := 231422136616910395264807

theorem tailTrace_450693 : CollatzResearch.WordTrace tailWord_450693 prefixEnd_450693 231422136616910395264807 := by
  unfold tailWord_450693
  simp only [CollatzResearch.WordTrace]
  refine ⟨16438124156223708081436733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10958749437482472054291155 16438124156223708081436733)
  ·
    refine ⟨6164296558583890530538775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16438124156223708081436733 6164296558583890530538775)
    ·
      refine ⟨9246444837875835795808163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6164296558583890530538775 9246444837875835795808163)
      ·
        refine ⟨13869667256813753693712245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9246444837875835795808163 13869667256813753693712245)
        ·
          refine ⟨1300281305326289408785523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13869667256813753693712245 1300281305326289408785523)
          ·
            refine ⟨1950421957989434113178285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300281305326289408785523 1950421957989434113178285)
            ·
              refine ⟨731408234246037792441857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1950421957989434113178285 731408234246037792441857)
              ·
                refine ⟨548556175684528344331393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731408234246037792441857 548556175684528344331393)
                ·
                  refine ⟨411417131763396258248545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548556175684528344331393 411417131763396258248545)
                  ·
                    refine ⟨308562848822547193686409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 411417131763396258248545 308562848822547193686409)
                    ·
                      refine ⟨231422136616910395264807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 308562848822547193686409 231422136616910395264807)
                      ·
                        rfl

theorem cell23_450693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 2, 2].length) (baseStart_450693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_450693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_450693 prefixEnd_450693 := by exact prefixLift 450693
  have htrace : WordTrace (prefixWord ++ tailWord_450693) baseStart_450693 baseEnd_450693 := by
    simpa [prefixWord, tailWord_450693, baseEnd_450693] using wordTrace_append hprefix tailTrace_450693
  have hstable : (prefixWord ++ tailWord_450693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_450693).length < 2 ^ (prefixWord ++ tailWord_450693).sum := by decide
  have hdescent : baseEnd_450693 < baseStart_450693 := by decide
  rcases family_descends (prefixWord ++ tailWord_450693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
