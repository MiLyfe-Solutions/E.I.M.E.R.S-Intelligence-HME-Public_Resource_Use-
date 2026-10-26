import V185TrunkScan21Chunk002

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_37323 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 9]
def baseStart_37323 : Nat := 118140960795 + 37323 * 2 ^ 59
def prefixEnd_37323 : Nat := 4983230072969 + 3 ^ 40 * 37323 * 2
def baseEnd_37323 : Nat := 8517617096827869907049

theorem tailTrace_37323 : CollatzResearch.WordTrace tailWord_37323 prefixEnd_37323 8517617096827869907049 := by
  unfold tailWord_37323
  simp only [CollatzResearch.WordTrace]
  refine ⟨1361281643792620106028623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 907521095861746737352415 1361281643792620106028623)
  ·
    refine ⟨2041922465688930159042935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1361281643792620106028623 2041922465688930159042935)
    ·
      refine ⟨3062883698533395238564403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2041922465688930159042935 3062883698533395238564403)
      ·
        refine ⟨4594325547800092857846605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3062883698533395238564403 4594325547800092857846605)
        ·
          refine ⟨1722872080425034821692477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4594325547800092857846605 1722872080425034821692477)
          ·
            refine ⟨646077030159388058134679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1722872080425034821692477 646077030159388058134679)
            ·
              refine ⟨969115545239082087202019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646077030159388058134679 969115545239082087202019)
              ·
                refine ⟨1453673317858623130803029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969115545239082087202019 1453673317858623130803029)
                ·
                  refine ⟨8517617096827869907049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1453673317858623130803029 8517617096827869907049)
                  ·
                    rfl

theorem cell21_37323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_37323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37323 prefixEnd_37323 := by exact prefixLift 37323
  have htrace : WordTrace (prefixWord ++ tailWord_37323) baseStart_37323 baseEnd_37323 := by
    simpa [prefixWord, tailWord_37323, baseEnd_37323] using wordTrace_append hprefix tailTrace_37323
  have hstable : (prefixWord ++ tailWord_37323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37323).length < 2 ^ (prefixWord ++ tailWord_37323).sum := by decide
  have hdescent : baseEnd_37323 < baseStart_37323 := by decide
  rcases family_descends (prefixWord ++ tailWord_37323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37357 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 5]
def baseStart_37357 : Nat := 118140960795 + 37357 * 2 ^ 59
def prefixEnd_37357 : Nat := 4983230072969 + 3 ^ 40 * 37357 * 2
def baseEnd_37357 : Nat := 8525376360051366340313

theorem tailTrace_37357 : CollatzResearch.WordTrace tailWord_37357 prefixEnd_37357 8525376360051366340313 := by
  unfold tailWord_37357
  simp only [CollatzResearch.WordTrace]
  refine ⟨1362521725669443912766325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 908347817112962608510883 1362521725669443912766325)
  ·
    refine ⟨127736411781510366821843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1362521725669443912766325 127736411781510366821843)
    ·
      refine ⟨191604617672265550232765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127736411781510366821843 191604617672265550232765)
      ·
        refine ⟨71851731627099581337287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191604617672265550232765 71851731627099581337287)
        ·
          refine ⟨107777597440649372005931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71851731627099581337287 107777597440649372005931)
          ·
            refine ⟨161666396160974058008897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107777597440649372005931 161666396160974058008897)
            ·
              refine ⟨121249797120730543506673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161666396160974058008897 121249797120730543506673)
              ·
                refine ⟨90937347840547907630005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121249797120730543506673 90937347840547907630005)
                ·
                  refine ⟨8525376360051366340313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90937347840547907630005 8525376360051366340313)
                  ·
                    rfl

theorem cell21_37357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_37357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37357 prefixEnd_37357 := by exact prefixLift 37357
  have htrace : WordTrace (prefixWord ++ tailWord_37357) baseStart_37357 baseEnd_37357 := by
    simpa [prefixWord, tailWord_37357, baseEnd_37357] using wordTrace_append hprefix tailTrace_37357
  have hstable : (prefixWord ++ tailWord_37357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37357).length < 2 ^ (prefixWord ++ tailWord_37357).sum := by decide
  have hdescent : baseEnd_37357 < baseStart_37357 := by decide
  rcases family_descends (prefixWord ++ tailWord_37357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37405 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 4]
def baseStart_37405 : Nat := 118140960795 + 37405 * 2 ^ 59
def prefixEnd_37405 : Nat := 4983230072969 + 3 ^ 40 * 37405 * 2
def baseEnd_37405 : Nat := 8536330614013949540215

theorem tailTrace_37405 : CollatzResearch.WordTrace tailWord_37405 prefixEnd_37405 8536330614013949540215 := by
  unfold tailWord_37405
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364272429495548110513669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 909514952997032073675779 1364272429495548110513669)
  ·
    refine ⟨255801080530415270721313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1364272429495548110513669 255801080530415270721313)
    ·
      refine ⟨191850810397811453040985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255801080530415270721313 191850810397811453040985)
      ·
        refine ⟨143888107798358589780739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191850810397811453040985 143888107798358589780739)
        ·
          refine ⟨215832161697537884671109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143888107798358589780739 215832161697537884671109)
          ·
            refine ⟨40468530318288353375833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215832161697537884671109 40468530318288353375833)
            ·
              refine ⟨30351397738716265031875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40468530318288353375833 30351397738716265031875)
              ·
                refine ⟨45527096608074397547813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30351397738716265031875 45527096608074397547813)
                ·
                  refine ⟨8536330614013949540215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45527096608074397547813 8536330614013949540215)
                  ·
                    rfl

theorem cell21_37405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_37405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37405 prefixEnd_37405 := by exact prefixLift 37405
  have htrace : WordTrace (prefixWord ++ tailWord_37405) baseStart_37405 baseEnd_37405 := by
    simpa [prefixWord, tailWord_37405, baseEnd_37405] using wordTrace_append hprefix tailTrace_37405
  have hstable : (prefixWord ++ tailWord_37405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37405).length < 2 ^ (prefixWord ++ tailWord_37405).sum := by decide
  have hdescent : baseEnd_37405 < baseStart_37405 := by decide
  rcases family_descends (prefixWord ++ tailWord_37405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37433 : List Nat := [1, 2, 1, 5, 1, 1, 2, 5, 3]
def baseStart_37433 : Nat := 118140960795 + 37433 * 2 ^ 59
def prefixEnd_37433 : Nat := 4983230072969 + 3 ^ 40 * 37433 * 2
def baseEnd_37433 : Nat := 8542720595492123073491

theorem tailTrace_37433 : CollatzResearch.WordTrace tailWord_37433 prefixEnd_37433 8542720595492123073491 := by
  unfold tailWord_37433
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365293673394108892532953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 910195782262739261688635 1365293673394108892532953)
  ·
    refine ⟨1023970255045581669399715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1365293673394108892532953 1023970255045581669399715)
    ·
      refine ⟨1535955382568372504099573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023970255045581669399715 1535955382568372504099573)
      ·
        refine ⟨143995817115784922259335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1535955382568372504099573 143995817115784922259335)
        ·
          refine ⟨215993725673677383389003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143995817115784922259335 215993725673677383389003)
          ·
            refine ⟨323990588510516075083505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215993725673677383389003 323990588510516075083505)
            ·
              refine ⟨242992941382887056312629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323990588510516075083505 242992941382887056312629)
              ·
                refine ⟨22780588254645661529309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 242992941382887056312629 22780588254645661529309)
                ·
                  refine ⟨8542720595492123073491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22780588254645661529309 8542720595492123073491)
                  ·
                    rfl

theorem cell21_37433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 3].length) (baseStart_37433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37433 prefixEnd_37433 := by exact prefixLift 37433
  have htrace : WordTrace (prefixWord ++ tailWord_37433) baseStart_37433 baseEnd_37433 := by
    simpa [prefixWord, tailWord_37433, baseEnd_37433] using wordTrace_append hprefix tailTrace_37433
  have hstable : (prefixWord ++ tailWord_37433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37433).length < 2 ^ (prefixWord ++ tailWord_37433).sum := by decide
  have hdescent : baseEnd_37433 < baseStart_37433 := by decide
  rcases family_descends (prefixWord ++ tailWord_37433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37447 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 4]
def baseStart_37447 : Nat := 118140960795 + 37447 * 2 ^ 59
def prefixEnd_37447 : Nat := 4983230072969 + 3 ^ 40 * 37447 * 2
def baseEnd_37447 : Nat := 8545915586231209840129

theorem tailTrace_37447 : CollatzResearch.WordTrace tailWord_37447 prefixEnd_37447 8545915586231209840129 := by
  unfold tailWord_37447
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365804295343389283542595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 910536196895592855695063 1365804295343389283542595)
  ·
    refine ⟨2048706443015083925313893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1365804295343389283542595 2048706443015083925313893)
    ·
      refine ⟨384132458065328235996355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2048706443015083925313893 384132458065328235996355)
      ·
        refine ⟨576198687097992353994533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384132458065328235996355 576198687097992353994533)
        ·
          refine ⟨108037253830873566373975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 576198687097992353994533 108037253830873566373975)
          ·
            refine ⟨162055880746310349560963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108037253830873566373975 162055880746310349560963)
            ·
              refine ⟨243083821119465524341445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162055880746310349560963 243083821119465524341445)
              ·
                refine ⟨45578216459899785814021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243083821119465524341445 45578216459899785814021)
                ·
                  refine ⟨8545915586231209840129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45578216459899785814021 8545915586231209840129)
                  ·
                    rfl

theorem cell21_37447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 4].length) (baseStart_37447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37447 prefixEnd_37447 := by exact prefixLift 37447
  have htrace : WordTrace (prefixWord ++ tailWord_37447) baseStart_37447 baseEnd_37447 := by
    simpa [prefixWord, tailWord_37447, baseEnd_37447] using wordTrace_append hprefix tailTrace_37447
  have hstable : (prefixWord ++ tailWord_37447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37447).length < 2 ^ (prefixWord ++ tailWord_37447).sum := by decide
  have hdescent : baseEnd_37447 < baseStart_37447 := by decide
  rcases family_descends (prefixWord ++ tailWord_37447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37450 : List Nat := [3, 1, 2, 1, 1, 4, 4, 2, 3]
def baseStart_37450 : Nat := 118140960795 + 37450 * 2 ^ 59
def prefixEnd_37450 : Nat := 4983230072969 + 3 ^ 40 * 37450 * 2
def baseEnd_37450 : Nat := 8546600227103871290123

theorem tailTrace_37450 : CollatzResearch.WordTrace tailWord_37450 prefixEnd_37450 8546600227103871290123 := by
  unfold tailWord_37450
  simp only [CollatzResearch.WordTrace]
  refine ⟨341478428583130198975451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 910609142888347197267869 341478428583130198975451)
  ·
    refine ⟨512217642874695298463177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 341478428583130198975451 512217642874695298463177)
    ·
      refine ⟨384163232156021473847383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 512217642874695298463177 384163232156021473847383)
      ·
        refine ⟨576244848234032210771075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384163232156021473847383 576244848234032210771075)
        ·
          refine ⟨864367272351048316156613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576244848234032210771075 864367272351048316156613)
          ·
            refine ⟨162068863565821559279365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 864367272351048316156613 162068863565821559279365)
            ·
              refine ⟨30387911918591542364881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162068863565821559279365 30387911918591542364881)
              ·
                refine ⟨22790933938943656773661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30387911918591542364881 22790933938943656773661)
                ·
                  refine ⟨8546600227103871290123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22790933938943656773661 8546600227103871290123)
                  ·
                    rfl

theorem cell21_37450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_37450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37450 prefixEnd_37450 := by exact prefixLift 37450
  have htrace : WordTrace (prefixWord ++ tailWord_37450) baseStart_37450 baseEnd_37450 := by
    simpa [prefixWord, tailWord_37450, baseEnd_37450] using wordTrace_append hprefix tailTrace_37450
  have hstable : (prefixWord ++ tailWord_37450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37450).length < 2 ^ (prefixWord ++ tailWord_37450).sum := by decide
  have hdescent : baseEnd_37450 < baseStart_37450 := by decide
  rcases family_descends (prefixWord ++ tailWord_37450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37461 : List Nat := [1, 3, 2, 2, 1, 1, 5, 6]
def baseStart_37461 : Nat := 118140960795 + 37461 * 2 ^ 59
def prefixEnd_37461 : Nat := 4983230072969 + 3 ^ 40 * 37461 * 2
def baseEnd_37461 : Nat := 2849703525656765535589

theorem tailTrace_37461 : CollatzResearch.WordTrace tailWord_37461 prefixEnd_37461 2849703525656765535589 := by
  unfold tailWord_37461
  simp only [CollatzResearch.WordTrace]
  refine ⟨1366314917292669674552237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 910876611528446449701491 1366314917292669674552237)
  ·
    refine ⟨512368093984751127957089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1366314917292669674552237 512368093984751127957089)
    ·
      refine ⟨384276070488563345967817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 512368093984751127957089 384276070488563345967817)
      ·
        refine ⟨288207052866422509475863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384276070488563345967817 288207052866422509475863)
        ·
          refine ⟨432310579299633764213795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288207052866422509475863 432310579299633764213795)
          ·
            refine ⟨648465868949450646320693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432310579299633764213795 648465868949450646320693)
            ·
              refine ⟨60793675214010998092565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 648465868949450646320693 60793675214010998092565)
              ·
                refine ⟨2849703525656765535589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60793675214010998092565 2849703525656765535589)
                ·
                  rfl

theorem cell21_37461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 6].length) (baseStart_37461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37461 prefixEnd_37461 := by exact prefixLift 37461
  have htrace : WordTrace (prefixWord ++ tailWord_37461) baseStart_37461 baseEnd_37461 := by
    simpa [prefixWord, tailWord_37461, baseEnd_37461] using wordTrace_append hprefix tailTrace_37461
  have hstable : (prefixWord ++ tailWord_37461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37461).length < 2 ^ (prefixWord ++ tailWord_37461).sum := by decide
  have hdescent : baseEnd_37461 < baseStart_37461 := by decide
  rcases family_descends (prefixWord ++ tailWord_37461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37509 : List Nat := [1, 3, 1, 1, 4, 2, 2, 4, 3]
def baseStart_37509 : Nat := 118140960795 + 37509 * 2 ^ 59
def prefixEnd_37509 : Nat := 4983230072969 + 3 ^ 40 * 37509 * 2
def baseEnd_37509 : Nat := 8560064830932879806669

theorem tailTrace_37509 : CollatzResearch.WordTrace tailWord_37509 prefixEnd_37509 8560064830932879806669 := by
  unfold tailWord_37509
  simp only [CollatzResearch.WordTrace]
  refine ⟨1368065621118773872299581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 912043747412515914866387 1368065621118773872299581)
  ·
    refine ⟨513024607919540202112343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1368065621118773872299581 513024607919540202112343)
    ·
      refine ⟨769536911879310303168515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513024607919540202112343 769536911879310303168515)
      ·
        refine ⟨1154305367818965454752773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769536911879310303168515 1154305367818965454752773)
        ·
          refine ⟨216432256466056022766145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1154305367818965454752773 216432256466056022766145)
          ·
            refine ⟨162324192349542017074609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216432256466056022766145 162324192349542017074609)
            ·
              refine ⟨121743144262156512805957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162324192349542017074609 121743144262156512805957)
              ·
                refine ⟨22826839549154346151117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121743144262156512805957 22826839549154346151117)
                ·
                  refine ⟨8560064830932879806669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22826839549154346151117 8560064830932879806669)
                  ·
                    rfl

theorem cell21_37509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_37509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37509 prefixEnd_37509 := by exact prefixLift 37509
  have htrace : WordTrace (prefixWord ++ tailWord_37509) baseStart_37509 baseEnd_37509 := by
    simpa [prefixWord, tailWord_37509, baseEnd_37509] using wordTrace_append hprefix tailTrace_37509
  have hstable : (prefixWord ++ tailWord_37509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37509).length < 2 ^ (prefixWord ++ tailWord_37509).sum := by decide
  have hdescent : baseEnd_37509 < baseStart_37509 := by decide
  rcases family_descends (prefixWord ++ tailWord_37509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37568 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 5]
def baseStart_37568 : Nat := 118140960795 + 37568 * 2 ^ 59
def prefixEnd_37568 : Nat := 4983230072969 + 3 ^ 40 * 37568 * 2
def baseEnd_37568 : Nat := 8573529434761888323215

theorem tailTrace_37568 : CollatzResearch.WordTrace tailWord_37568 prefixEnd_37568 8573529434761888323215 := by
  unfold tailWord_37568
  simp only [CollatzResearch.WordTrace]
  refine ⟨685108763952513474348679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 913478351936684632464905 685108763952513474348679)
  ·
    refine ⟨1027663145928770211523019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 685108763952513474348679 1027663145928770211523019)
    ·
      refine ⟨1541494718893155317284529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1027663145928770211523019 1541494718893155317284529)
      ·
        refine ⟨1156121039169866487963397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1541494718893155317284529 1156121039169866487963397)
        ·
          refine ⟨216772694844349966493137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1156121039169866487963397 216772694844349966493137)
          ·
            refine ⟨162579521133262474869853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216772694844349966493137 162579521133262474869853)
            ·
              refine ⟨60967320424973428076195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162579521133262474869853 60967320424973428076195)
              ·
                refine ⟨91450980637460142114293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60967320424973428076195 91450980637460142114293)
                ·
                  refine ⟨8573529434761888323215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91450980637460142114293 8573529434761888323215)
                  ·
                    rfl

theorem cell21_37568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_37568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37568 prefixEnd_37568 := by exact prefixLift 37568
  have htrace : WordTrace (prefixWord ++ tailWord_37568) baseStart_37568 baseEnd_37568 := by
    simpa [prefixWord, tailWord_37568, baseEnd_37568] using wordTrace_append hprefix tailTrace_37568
  have hstable : (prefixWord ++ tailWord_37568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37568).length < 2 ^ (prefixWord ++ tailWord_37568).sum := by decide
  have hdescent : baseEnd_37568 < baseStart_37568 := by decide
  rcases family_descends (prefixWord ++ tailWord_37568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37574 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_37574 : Nat := 118140960795 + 37574 * 2 ^ 59
def prefixEnd_37574 : Nat := 4983230072969 + 3 ^ 40 * 37574 * 2
def baseEnd_37574 : Nat := 8574898716507211223203

theorem tailTrace_37574 : CollatzResearch.WordTrace tailWord_37574 prefixEnd_37574 8574898716507211223203 := by
  unfold tailWord_37574
  simp only [CollatzResearch.WordTrace]
  refine ⟨42826136433852811669243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 913624243922193315610517 42826136433852811669243)
  ·
    refine ⟨64239204650779217503865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42826136433852811669243 64239204650779217503865)
    ·
      refine ⟨48179403488084413127899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64239204650779217503865 48179403488084413127899)
      ·
        refine ⟨72269105232126619691849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48179403488084413127899 72269105232126619691849)
        ·
          refine ⟨54201828924094964768887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72269105232126619691849 54201828924094964768887)
          ·
            refine ⟨81302743386142447153331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54201828924094964768887 81302743386142447153331)
            ·
              refine ⟨121954115079213670729997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81302743386142447153331 121954115079213670729997)
              ·
                refine ⟨45732793154705126523749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121954115079213670729997 45732793154705126523749)
                ·
                  refine ⟨8574898716507211223203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45732793154705126523749 8574898716507211223203)
                  ·
                    rfl

theorem cell21_37574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_37574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37574 prefixEnd_37574 := by exact prefixLift 37574
  have htrace : WordTrace (prefixWord ++ tailWord_37574) baseStart_37574 baseEnd_37574 := by
    simpa [prefixWord, tailWord_37574, baseEnd_37574] using wordTrace_append hprefix tailTrace_37574
  have hstable : (prefixWord ++ tailWord_37574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37574).length < 2 ^ (prefixWord ++ tailWord_37574).sum := by decide
  have hdescent : baseEnd_37574 < baseStart_37574 := by decide
  rcases family_descends (prefixWord ++ tailWord_37574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37630 : List Nat := [4, 2, 2, 1, 2, 1, 3, 6]
def baseStart_37630 : Nat := 118140960795 + 37630 * 2 ^ 59
def prefixEnd_37630 : Nat := 4983230072969 + 3 ^ 40 * 37630 * 2
def baseEnd_37630 : Nat := 2862559559821186096585

theorem tailTrace_37630 : CollatzResearch.WordTrace tailWord_37630 prefixEnd_37630 2862559559821186096585 := by
  unfold tailWord_37630
  simp only [CollatzResearch.WordTrace]
  refine ⟨171559856710051442181793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 914985902453607691636229 171559856710051442181793)
  ·
    refine ⟨128669892532538581636345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171559856710051442181793 128669892532538581636345)
    ·
      refine ⟨96502419399403936227259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128669892532538581636345 96502419399403936227259)
      ·
        refine ⟨144753629099105904340889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96502419399403936227259 144753629099105904340889)
        ·
          refine ⟨108565221824329428255667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144753629099105904340889 108565221824329428255667)
          ·
            refine ⟨162847832736494142383501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108565221824329428255667 162847832736494142383501)
            ·
              refine ⟨61067937276185303393813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162847832736494142383501 61067937276185303393813)
              ·
                refine ⟨2862559559821186096585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61067937276185303393813 2862559559821186096585)
                ·
                  rfl

theorem cell21_37630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_37630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37630 prefixEnd_37630 := by exact prefixLift 37630
  have htrace : WordTrace (prefixWord ++ tailWord_37630) baseStart_37630 baseEnd_37630 := by
    simpa [prefixWord, tailWord_37630, baseEnd_37630] using wordTrace_append hprefix tailTrace_37630
  have hstable : (prefixWord ++ tailWord_37630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37630).length < 2 ^ (prefixWord ++ tailWord_37630).sum := by decide
  have hdescent : baseEnd_37630 < baseStart_37630 := by decide
  rcases family_descends (prefixWord ++ tailWord_37630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37658 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_37658 : Nat := 118140960795 + 37658 * 2 ^ 59
def prefixEnd_37658 : Nat := 4983230072969 + 3 ^ 40 * 37658 * 2
def baseEnd_37658 : Nat := 8594068660941731823031

theorem tailTrace_37658 : CollatzResearch.WordTrace tailWord_37658 prefixEnd_37658 8594068660941731823031 := by
  unfold tailWord_37658
  simp only [CollatzResearch.WordTrace]
  refine ⟨343375024394743079868407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 915666731719314879649085 343375024394743079868407)
  ·
    refine ⟨515062536592114619802611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 343375024394743079868407 515062536592114619802611)
    ·
      refine ⟨772593804888171929703917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 515062536592114619802611 772593804888171929703917)
      ·
        refine ⟨289722676833064473638969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 772593804888171929703917 289722676833064473638969)
        ·
          refine ⟨217292007624798355229227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289722676833064473638969 217292007624798355229227)
          ·
            refine ⟨325938011437197532843841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217292007624798355229227 325938011437197532843841)
            ·
              refine ⟨244453508577898149632881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325938011437197532843841 244453508577898149632881)
              ·
                refine ⟨183340131433423612224661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244453508577898149632881 183340131433423612224661)
                ·
                  refine ⟨8594068660941731823031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 183340131433423612224661 8594068660941731823031)
                  ·
                    rfl

theorem cell21_37658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_37658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37658 prefixEnd_37658 := by exact prefixLift 37658
  have htrace : WordTrace (prefixWord ++ tailWord_37658) baseStart_37658 baseEnd_37658 := by
    simpa [prefixWord, tailWord_37658, baseEnd_37658] using wordTrace_append hprefix tailTrace_37658
  have hstable : (prefixWord ++ tailWord_37658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37658).length < 2 ^ (prefixWord ++ tailWord_37658).sum := by decide
  have hdescent : baseEnd_37658 < baseStart_37658 := by decide
  rcases family_descends (prefixWord ++ tailWord_37658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37678 : List Nat := [4, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_37678 : Nat := 118140960795 + 37678 * 2 ^ 59
def prefixEnd_37678 : Nat := 4983230072969 + 3 ^ 40 * 37678 * 2
def baseEnd_37678 : Nat := 8598632933426141489657

theorem tailTrace_37678 : CollatzResearch.WordTrace tailWord_37678 prefixEnd_37678 8598632933426141489657 := by
  unfold tailWord_37678
  simp only [CollatzResearch.WordTrace]
  refine ⟨171778694688314466900211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 916153038337677156801125 171778694688314466900211)
  ·
    refine ⟨257668042032471700350317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171778694688314466900211 257668042032471700350317)
    ·
      refine ⟨96625515762176887631369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257668042032471700350317 96625515762176887631369)
      ·
        refine ⟨72469136821632665723527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96625515762176887631369 72469136821632665723527)
        ·
          refine ⟨108703705232448998585291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72469136821632665723527 108703705232448998585291)
          ·
            refine ⟨163055557848673497877937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108703705232448998585291 163055557848673497877937)
            ·
              refine ⟨122291668386505123408453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163055557848673497877937 122291668386505123408453)
              ·
                refine ⟨22929687822469710639085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122291668386505123408453 22929687822469710639085)
                ·
                  refine ⟨8598632933426141489657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22929687822469710639085 8598632933426141489657)
                  ·
                    rfl

theorem cell21_37678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_37678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37678 prefixEnd_37678 := by exact prefixLift 37678
  have htrace : WordTrace (prefixWord ++ tailWord_37678) baseStart_37678 baseEnd_37678 := by
    simpa [prefixWord, tailWord_37678, baseEnd_37678] using wordTrace_append hprefix tailTrace_37678
  have hstable : (prefixWord ++ tailWord_37678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37678).length < 2 ^ (prefixWord ++ tailWord_37678).sum := by decide
  have hdescent : baseEnd_37678 < baseStart_37678 := by decide
  rcases family_descends (prefixWord ++ tailWord_37678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37788 : List Nat := [2, 2, 3, 3, 3, 1, 2, 2, 3]
def baseStart_37788 : Nat := 118140960795 + 37788 * 2 ^ 59
def prefixEnd_37788 : Nat := 4983230072969 + 3 ^ 40 * 37788 * 2
def baseEnd_37788 : Nat := 8623736432090394656099

theorem tailTrace_37788 : CollatzResearch.WordTrace tailWord_37788 prefixEnd_37788 8623736432090394656099 := by
  unfold tailWord_37788
  simp only [CollatzResearch.WordTrace]
  refine ⟨689120793554002260853009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 918827724738669681137345 689120793554002260853009)
  ·
    refine ⟨516840595165501695639757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 689120793554002260853009 516840595165501695639757)
    ·
      refine ⟨193815223187063135864909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 516840595165501695639757 193815223187063135864909)
      ·
        refine ⟨72680708695148675949341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193815223187063135864909 72680708695148675949341)
        ·
          refine ⟨27255265760680753481003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72680708695148675949341 27255265760680753481003)
          ·
            refine ⟨40882898641021130221505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27255265760680753481003 40882898641021130221505)
            ·
              refine ⟨30662173980765847666129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40882898641021130221505 30662173980765847666129)
              ·
                refine ⟨22996630485574385749597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30662173980765847666129 22996630485574385749597)
                ·
                  refine ⟨8623736432090394656099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22996630485574385749597 8623736432090394656099)
                  ·
                    rfl

theorem cell21_37788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_37788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37788 prefixEnd_37788 := by exact prefixLift 37788
  have htrace : WordTrace (prefixWord ++ tailWord_37788) baseStart_37788 baseEnd_37788 := by
    simpa [prefixWord, tailWord_37788, baseEnd_37788] using wordTrace_append hprefix tailTrace_37788
  have hstable : (prefixWord ++ tailWord_37788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37788).length < 2 ^ (prefixWord ++ tailWord_37788).sum := by decide
  have hdescent : baseEnd_37788 < baseStart_37788 := by decide
  rcases family_descends (prefixWord ++ tailWord_37788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37799 : List Nat := [1, 1, 6, 1, 4, 1, 1, 6]
def baseStart_37799 : Nat := 118140960795 + 37799 * 2 ^ 59
def prefixEnd_37799 : Nat := 4983230072969 + 3 ^ 40 * 37799 * 2
def baseEnd_37799 : Nat := 2875415593985606657581

theorem tailTrace_37799 : CollatzResearch.WordTrace tailWord_37799 prefixEnd_37799 2875415593985606657581 := by
  unfold tailWord_37799
  simp only [CollatzResearch.WordTrace]
  refine ⟨1378642790068153400356451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 919095193378768933570967 1378642790068153400356451)
  ·
    refine ⟨2067964185102230100534677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1378642790068153400356451 2067964185102230100534677)
    ·
      refine ⟨96935821176667035962563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2067964185102230100534677 96935821176667035962563)
      ·
        refine ⟨145403731765000553943845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96935821176667035962563 145403731765000553943845)
        ·
          refine ⟨27263199705937603864471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145403731765000553943845 27263199705937603864471)
          ·
            refine ⟨40894799558906405796707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27263199705937603864471 40894799558906405796707)
            ·
              refine ⟨61342199338359608695061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40894799558906405796707 61342199338359608695061)
              ·
                refine ⟨2875415593985606657581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61342199338359608695061 2875415593985606657581)
                ·
                  rfl

theorem cell21_37799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 6].length) (baseStart_37799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37799 prefixEnd_37799 := by exact prefixLift 37799
  have htrace : WordTrace (prefixWord ++ tailWord_37799) baseStart_37799 baseEnd_37799 := by
    simpa [prefixWord, tailWord_37799, baseEnd_37799] using wordTrace_append hprefix tailTrace_37799
  have hstable : (prefixWord ++ tailWord_37799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37799).length < 2 ^ (prefixWord ++ tailWord_37799).sum := by decide
  have hdescent : baseEnd_37799 < baseStart_37799 := by decide
  rcases family_descends (prefixWord ++ tailWord_37799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37844 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 4]
def baseStart_37844 : Nat := 118140960795 + 37844 * 2 ^ 59
def prefixEnd_37844 : Nat := 4983230072969 + 3 ^ 40 * 37844 * 2
def baseEnd_37844 : Nat := 8636516395046741722651

theorem tailTrace_37844 : CollatzResearch.WordTrace tailWord_37844 prefixEnd_37844 8636516395046741722651 := by
  unfold tailWord_37844
  simp only [CollatzResearch.WordTrace]
  refine ⟨690142037452563042872293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 920189383270084057163057 690142037452563042872293)
  ·
    refine ⟨129401632022355570538555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 690142037452563042872293 129401632022355570538555)
    ·
      refine ⟨194102448033533355807833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129401632022355570538555 194102448033533355807833)
      ·
        refine ⟨145576836025150016855875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194102448033533355807833 145576836025150016855875)
        ·
          refine ⟨218365254037725025283813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145576836025150016855875 218365254037725025283813)
          ·
            refine ⟨40943485132073442240715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218365254037725025283813 40943485132073442240715)
            ·
              refine ⟨61415227698110163361073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40943485132073442240715 61415227698110163361073)
              ·
                refine ⟨46061420773582622520805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61415227698110163361073 46061420773582622520805)
                ·
                  refine ⟨8636516395046741722651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46061420773582622520805 8636516395046741722651)
                  ·
                    rfl

theorem cell21_37844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_37844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37844 prefixEnd_37844 := by exact prefixLift 37844
  have htrace : WordTrace (prefixWord ++ tailWord_37844) baseStart_37844 baseEnd_37844 := by
    simpa [prefixWord, tailWord_37844, baseEnd_37844] using wordTrace_append hprefix tailTrace_37844
  have hstable : (prefixWord ++ tailWord_37844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37844).length < 2 ^ (prefixWord ++ tailWord_37844).sum := by decide
  have hdescent : baseEnd_37844 < baseStart_37844 := by decide
  rcases family_descends (prefixWord ++ tailWord_37844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37861 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 4]
def baseStart_37861 : Nat := 118140960795 + 37861 * 2 ^ 59
def prefixEnd_37861 : Nat := 4983230072969 + 3 ^ 40 * 37861 * 2
def baseEnd_37861 : Nat := 8640396026658489939283

theorem tailTrace_37861 : CollatzResearch.WordTrace tailWord_37861 prefixEnd_37861 8640396026658489939283 := by
  unfold tailWord_37861
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380904115843537989113437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 920602743895691992742291 1380904115843537989113437)
  ·
    refine ⟨517839043441326745917539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1380904115843537989113437 517839043441326745917539)
    ·
      refine ⟨776758565161990118876309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 517839043441326745917539 776758565161990118876309)
      ·
        refine ⟨36410557741968286822327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 776758565161990118876309 36410557741968286822327)
        ·
          refine ⟨54615836612952430233491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36410557741968286822327 54615836612952430233491)
          ·
            refine ⟨81923754919428645350237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54615836612952430233491 81923754919428645350237)
            ·
              refine ⟨30721408094785742006339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81923754919428645350237 30721408094785742006339)
              ·
                refine ⟨46082112142178613009509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30721408094785742006339 46082112142178613009509)
                ·
                  refine ⟨8640396026658489939283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46082112142178613009509 8640396026658489939283)
                  ·
                    rfl

theorem cell21_37861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_37861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37861 prefixEnd_37861 := by exact prefixLift 37861
  have htrace : WordTrace (prefixWord ++ tailWord_37861) baseStart_37861 baseEnd_37861 := by
    simpa [prefixWord, tailWord_37861, baseEnd_37861] using wordTrace_append hprefix tailTrace_37861
  have hstable : (prefixWord ++ tailWord_37861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37861).length < 2 ^ (prefixWord ++ tailWord_37861).sum := by decide
  have hdescent : baseEnd_37861 < baseStart_37861 := by decide
  rcases family_descends (prefixWord ++ tailWord_37861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37889 : List Nat := [1, 2, 4, 1, 2, 2, 3, 3, 3]
def baseStart_37889 : Nat := 118140960795 + 37889 * 2 ^ 59
def prefixEnd_37889 : Nat := 4983230072969 + 3 ^ 40 * 37889 * 2
def baseEnd_37889 : Nat := 8646786008136663472559

theorem tailTrace_37889 : CollatzResearch.WordTrace tailWord_37889 prefixEnd_37889 8646786008136663472559 := by
  unfold tailWord_37889
  simp only [CollatzResearch.WordTrace]
  refine ⟨1381925359742098771132721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 921283573161399180755147 1381925359742098771132721)
  ·
    refine ⟨1036444019806574078349541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1381925359742098771132721 1036444019806574078349541)
    ·
      refine ⟨194333253713732639690539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1036444019806574078349541 194333253713732639690539)
      ·
        refine ⟨291499880570598959535809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194333253713732639690539 291499880570598959535809)
        ·
          refine ⟨218624910427949219651857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291499880570598959535809 218624910427949219651857)
          ·
            refine ⟨163968682820961914738893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218624910427949219651857 163968682820961914738893)
            ·
              refine ⟨61488256057860718027085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163968682820961914738893 61488256057860718027085)
              ·
                refine ⟨23058096021697769260157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61488256057860718027085 23058096021697769260157)
                ·
                  refine ⟨8646786008136663472559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23058096021697769260157 8646786008136663472559)
                  ·
                    rfl

theorem cell21_37889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 3].length) (baseStart_37889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37889 prefixEnd_37889 := by exact prefixLift 37889
  have htrace : WordTrace (prefixWord ++ tailWord_37889) baseStart_37889 baseEnd_37889 := by
    simpa [prefixWord, tailWord_37889, baseEnd_37889] using wordTrace_append hprefix tailTrace_37889
  have hstable : (prefixWord ++ tailWord_37889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37889).length < 2 ^ (prefixWord ++ tailWord_37889).sum := by decide
  have hdescent : baseEnd_37889 < baseStart_37889 := by decide
  rcases family_descends (prefixWord ++ tailWord_37889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37900 : List Nat := [2, 2, 1, 2, 3, 2, 9]
def baseStart_37900 : Nat := 118140960795 + 37900 * 2 ^ 59
def prefixEnd_37900 : Nat := 4983230072969 + 3 ^ 40 * 37900 * 2
def baseEnd_37900 : Nat := 961032928667009865467

theorem tailTrace_37900 : CollatzResearch.WordTrace tailWord_37900 prefixEnd_37900 961032928667009865467 := by
  unfold tailWord_37900
  simp only [CollatzResearch.WordTrace]
  refine ⟨691163281351123824891577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 921551041801498433188769 691163281351123824891577)
  ·
    refine ⟨518372461013342868668683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 691163281351123824891577 518372461013342868668683)
    ·
      refine ⟨777558691520014303003025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 518372461013342868668683 777558691520014303003025)
      ·
        refine ⟨583169018640010727252269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 777558691520014303003025 583169018640010727252269)
        ·
          refine ⟨218688381990004022719601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 583169018640010727252269 218688381990004022719601)
          ·
            refine ⟨164016286492503017039701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218688381990004022719601 164016286492503017039701)
            ·
              refine ⟨961032928667009865467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 164016286492503017039701 961032928667009865467)
              ·
                rfl

theorem cell21_37900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 9].length) (baseStart_37900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37900 prefixEnd_37900 := by exact prefixLift 37900
  have htrace : WordTrace (prefixWord ++ tailWord_37900) baseStart_37900 baseEnd_37900 := by
    simpa [prefixWord, tailWord_37900, baseEnd_37900] using wordTrace_append hprefix tailTrace_37900
  have hstable : (prefixWord ++ tailWord_37900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37900).length < 2 ^ (prefixWord ++ tailWord_37900).sum := by decide
  have hdescent : baseEnd_37900 < baseStart_37900 := by decide
  rcases family_descends (prefixWord ++ tailWord_37900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37920 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 4]
def baseStart_37920 : Nat := 118140960795 + 37920 * 2 ^ 59
def prefixEnd_37920 : Nat := 4983230072969 + 3 ^ 40 * 37920 * 2
def baseEnd_37920 : Nat := 8653860630487498455829

theorem tailTrace_37920 : CollatzResearch.WordTrace tailWord_37920 prefixEnd_37920 8653860630487498455829 := by
  unfold tailWord_37920
  simp only [CollatzResearch.WordTrace]
  refine ⟨691528011314895532755607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 922037348419860710340809 691528011314895532755607)
  ·
    refine ⟨1037292016972343299133411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 691528011314895532755607 1037292016972343299133411)
    ·
      refine ⟨1555938025458514948700117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037292016972343299133411 1555938025458514948700117)
      ·
        refine ⟨36467297471683944110159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 1555938025458514948700117 36467297471683944110159)
        ·
          refine ⟨54700946207525916165239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36467297471683944110159 54700946207525916165239)
          ·
            refine ⟨82051419311288874247859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54700946207525916165239 82051419311288874247859)
            ·
              refine ⟨123077128966933311371789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82051419311288874247859 123077128966933311371789)
              ·
                refine ⟨46153923362599991764421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123077128966933311371789 46153923362599991764421)
                ·
                  refine ⟨8653860630487498455829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46153923362599991764421 8653860630487498455829)
                  ·
                    rfl

theorem cell21_37920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_37920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37920 prefixEnd_37920 := by exact prefixLift 37920
  have htrace : WordTrace (prefixWord ++ tailWord_37920) baseStart_37920 baseEnd_37920 := by
    simpa [prefixWord, tailWord_37920, baseEnd_37920] using wordTrace_append hprefix tailTrace_37920
  have hstable : (prefixWord ++ tailWord_37920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37920).length < 2 ^ (prefixWord ++ tailWord_37920).sum := by decide
  have hdescent : baseEnd_37920 < baseStart_37920 := by decide
  rcases family_descends (prefixWord ++ tailWord_37920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37962 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_37962 : Nat := 118140960795 + 37962 * 2 ^ 59
def prefixEnd_37962 : Nat := 4983230072969 + 3 ^ 40 * 37962 * 2
def baseEnd_37962 : Nat := 8663445602704758755743

theorem tailTrace_37962 : CollatzResearch.WordTrace tailWord_37962 prefixEnd_37962 8663445602704758755743 := by
  unfold tailWord_37962
  simp only [CollatzResearch.WordTrace]
  refine ⟨346146972119408059635035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 923058592318421492360093 346146972119408059635035)
  ·
    refine ⟨519220458179112089452553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 346146972119408059635035 519220458179112089452553)
    ·
      refine ⟨389415343634334067089415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 519220458179112089452553 389415343634334067089415)
      ·
        refine ⟨584123015451501100634123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389415343634334067089415 584123015451501100634123)
        ·
          refine ⟨876184523177251650951185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584123015451501100634123 876184523177251650951185)
          ·
            refine ⟨657138392382938738213389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 876184523177251650951185 657138392382938738213389)
            ·
              refine ⟨246426897143602026830021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 657138392382938738213389 246426897143602026830021)
              ·
                refine ⟨46205043214425380030629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246426897143602026830021 46205043214425380030629)
                ·
                  refine ⟨8663445602704758755743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46205043214425380030629 8663445602704758755743)
                  ·
                    rfl

theorem cell21_37962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_37962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37962 prefixEnd_37962 := by exact prefixLift 37962
  have htrace : WordTrace (prefixWord ++ tailWord_37962) baseStart_37962 baseEnd_37962 := by
    simpa [prefixWord, tailWord_37962, baseEnd_37962] using wordTrace_append hprefix tailTrace_37962
  have hstable : (prefixWord ++ tailWord_37962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37962).length < 2 ^ (prefixWord ++ tailWord_37962).sum := by decide
  have hdescent : baseEnd_37962 < baseStart_37962 := by decide
  rcases family_descends (prefixWord ++ tailWord_37962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37982 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_37982 : Nat := 118140960795 + 37982 * 2 ^ 59
def prefixEnd_37982 : Nat := 4983230072969 + 3 ^ 40 * 37982 * 2
def baseEnd_37982 : Nat := 8668009875189168422369

theorem tailTrace_37982 : CollatzResearch.WordTrace tailWord_37982 prefixEnd_37982 8668009875189168422369 := by
  unfold tailWord_37982
  simp only [CollatzResearch.WordTrace]
  refine ⟨173164668550646956783525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 923544898936783769512133 173164668550646956783525)
  ·
    refine ⟨32468375353246304396911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 173164668550646956783525 32468375353246304396911)
    ·
      refine ⟨48702563029869456595367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32468375353246304396911 48702563029869456595367)
      ·
        refine ⟨73053844544804184893051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48702563029869456595367 73053844544804184893051)
        ·
          refine ⟨109580766817206277339577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73053844544804184893051 109580766817206277339577)
          ·
            refine ⟨82185575112904708004683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109580766817206277339577 82185575112904708004683)
            ·
              refine ⟨123278362669357062007025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82185575112904708004683 123278362669357062007025)
              ·
                refine ⟨92458772002017796505269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123278362669357062007025 92458772002017796505269)
                ·
                  refine ⟨8668009875189168422369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92458772002017796505269 8668009875189168422369)
                  ·
                    rfl

theorem cell21_37982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_37982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37982 prefixEnd_37982 := by exact prefixLift 37982
  have htrace : WordTrace (prefixWord ++ tailWord_37982) baseStart_37982 baseEnd_37982 := by
    simpa [prefixWord, tailWord_37982, baseEnd_37982] using wordTrace_append hprefix tailTrace_37982
  have hstable : (prefixWord ++ tailWord_37982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37982).length < 2 ^ (prefixWord ++ tailWord_37982).sum := by decide
  have hdescent : baseEnd_37982 < baseStart_37982 := by decide
  rcases family_descends (prefixWord ++ tailWord_37982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37993 : List Nat := [1, 2, 1, 1, 1, 7, 3, 5]
def baseStart_37993 : Nat := 118140960795 + 37993 * 2 ^ 59
def prefixEnd_37993 : Nat := 4983230072969 + 3 ^ 40 * 37993 * 2
def baseEnd_37993 : Nat := 2890173408351864579671

theorem tailTrace_37993 : CollatzResearch.WordTrace tailWord_37993 prefixEnd_37993 2890173408351864579671 := by
  unfold tailWord_37993
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385718551365324532918633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 923812367576883021945755 1385718551365324532918633)
  ·
    refine ⟨1039288913523993399688975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1385718551365324532918633 1039288913523993399688975)
    ·
      refine ⟨1558933370285990099533463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1039288913523993399688975 1558933370285990099533463)
      ·
        refine ⟨2338400055428985149300195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558933370285990099533463 2338400055428985149300195)
        ·
          refine ⟨3507600083143477723950293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2338400055428985149300195 3507600083143477723950293)
          ·
            refine ⟨82209376948675259155085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3507600083143477723950293 82209376948675259155085)
            ·
              refine ⟨30828516355753222183157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82209376948675259155085 30828516355753222183157)
              ·
                refine ⟨2890173408351864579671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30828516355753222183157 2890173408351864579671)
                ·
                  rfl

theorem cell21_37993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 5].length) (baseStart_37993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37993 prefixEnd_37993 := by exact prefixLift 37993
  have htrace : WordTrace (prefixWord ++ tailWord_37993) baseStart_37993 baseEnd_37993 := by
    simpa [prefixWord, tailWord_37993, baseEnd_37993] using wordTrace_append hprefix tailTrace_37993
  have hstable : (prefixWord ++ tailWord_37993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37993).length < 2 ^ (prefixWord ++ tailWord_37993).sum := by decide
  have hdescent : baseEnd_37993 < baseStart_37993 := by decide
  rcases family_descends (prefixWord ++ tailWord_37993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38058 : List Nat := [3, 1, 5, 1, 1, 1, 3, 3, 3]
def baseStart_38058 : Nat := 118140960795 + 38058 * 2 ^ 59
def prefixEnd_38058 : Nat := 4983230072969 + 3 ^ 40 * 38058 * 2
def baseEnd_38058 : Nat := 8685354110629925155547

theorem tailTrace_38058 : CollatzResearch.WordTrace tailWord_38058 prefixEnd_38058 8685354110629925155547 := by
  unfold tailWord_38058
  simp only [CollatzResearch.WordTrace]
  refine ⟨347022324032460158508707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 925392864086560422689885 347022324032460158508707)
  ·
    refine ⟨520533486048690237763061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 347022324032460158508707 520533486048690237763061)
    ·
      refine ⟨48800014317064709790287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 520533486048690237763061 48800014317064709790287)
      ·
        refine ⟨73200021475597064685431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48800014317064709790287 73200021475597064685431)
        ·
          refine ⟨109800032213395597028147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73200021475597064685431 109800032213395597028147)
          ·
            refine ⟨164700048320093395542221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109800032213395597028147 164700048320093395542221)
            ·
              refine ⟨61762518120035023328333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164700048320093395542221 61762518120035023328333)
              ·
                refine ⟨23160944295013133748125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61762518120035023328333 23160944295013133748125)
                ·
                  refine ⟨8685354110629925155547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23160944295013133748125 8685354110629925155547)
                  ·
                    rfl

theorem cell21_38058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_38058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38058 prefixEnd_38058 := by exact prefixLift 38058
  have htrace : WordTrace (prefixWord ++ tailWord_38058) baseStart_38058 baseEnd_38058 := by
    simpa [prefixWord, tailWord_38058, baseEnd_38058] using wordTrace_append hprefix tailTrace_38058
  have hstable : (prefixWord ++ tailWord_38058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38058).length < 2 ^ (prefixWord ++ tailWord_38058).sum := by decide
  have hdescent : baseEnd_38058 < baseStart_38058 := by decide
  rcases family_descends (prefixWord ++ tailWord_38058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38145 : List Nat := [1, 2, 4, 1, 1, 5, 1, 6]
def baseStart_38145 : Nat := 118140960795 + 38145 * 2 ^ 59
def prefixEnd_38145 : Nat := 4983230072969 + 3 ^ 40 * 38145 * 2
def baseEnd_38145 : Nat := 2901736231979035735123

theorem tailTrace_38145 : CollatzResearch.WordTrace tailWord_38145 prefixEnd_38145 2901736231979035735123 := by
  unfold tailWord_38145
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391262446814654492451889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 927508297876436328301259 1391262446814654492451889)
  ·
    refine ⟨1043446835110990869338917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1391262446814654492451889 1043446835110990869338917)
    ·
      refine ⟨195646281583310788001047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1043446835110990869338917 195646281583310788001047)
      ·
        refine ⟨293469422374966182001571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195646281583310788001047 293469422374966182001571)
        ·
          refine ⟨440204133562449273002357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293469422374966182001571 440204133562449273002357)
          ·
            refine ⟨41269137521479619343971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 440204133562449273002357 41269137521479619343971)
            ·
              refine ⟨61903706282219429015957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41269137521479619343971 61903706282219429015957)
              ·
                refine ⟨2901736231979035735123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61903706282219429015957 2901736231979035735123)
                ·
                  rfl

theorem cell21_38145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 6].length) (baseStart_38145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38145 prefixEnd_38145 := by exact prefixLift 38145
  have htrace : WordTrace (prefixWord ++ tailWord_38145) baseStart_38145 baseEnd_38145 := by
    simpa [prefixWord, tailWord_38145, baseEnd_38145] using wordTrace_append hprefix tailTrace_38145
  have hstable : (prefixWord ++ tailWord_38145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38145).length < 2 ^ (prefixWord ++ tailWord_38145).sum := by decide
  have hdescent : baseEnd_38145 < baseStart_38145 := by decide
  rcases family_descends (prefixWord ++ tailWord_38145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38207 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 4]
def baseStart_38207 : Nat := 118140960795 + 38207 * 2 ^ 59
def prefixEnd_38207 : Nat := 4983230072969 + 3 ^ 40 * 38207 * 2
def baseEnd_38207 : Nat := 8719357940638777171909

theorem tailTrace_38207 : CollatzResearch.WordTrace tailWord_38207 prefixEnd_38207 8719357940638777171909 := by
  unfold tailWord_38207
  simp only [CollatzResearch.WordTrace]
  refine ⟨1393523772590039081208875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 929015848393359387472583 1393523772590039081208875)
  ·
    refine ⟨2090285658885058621813313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1393523772590039081208875 2090285658885058621813313)
    ·
      refine ⟨1567714244163793966359985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2090285658885058621813313 1567714244163793966359985)
      ·
        refine ⟨1175785683122845474769989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1567714244163793966359985 1175785683122845474769989)
        ·
          refine ⟨220459815585533526519373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1175785683122845474769989 220459815585533526519373)
          ·
            refine ⟨82672430844575072444765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220459815585533526519373 82672430844575072444765)
            ·
              refine ⟨31002161566715652166787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82672430844575072444765 31002161566715652166787)
              ·
                refine ⟨46503242350073478250181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31002161566715652166787 46503242350073478250181)
                ·
                  refine ⟨8719357940638777171909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46503242350073478250181 8719357940638777171909)
                  ·
                    rfl

theorem cell21_38207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 4].length) (baseStart_38207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38207 prefixEnd_38207 := by exact prefixLift 38207
  have htrace : WordTrace (prefixWord ++ tailWord_38207) baseStart_38207 baseEnd_38207 := by
    simpa [prefixWord, tailWord_38207, baseEnd_38207] using wordTrace_append hprefix tailTrace_38207
  have hstable : (prefixWord ++ tailWord_38207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38207).length < 2 ^ (prefixWord ++ tailWord_38207).sum := by decide
  have hdescent : baseEnd_38207 < baseStart_38207 := by decide
  rcases family_descends (prefixWord ++ tailWord_38207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38252 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 5]
def baseStart_38252 : Nat := 118140960795 + 38252 * 2 ^ 59
def prefixEnd_38252 : Nat := 4983230072969 + 3 ^ 40 * 38252 * 2
def baseEnd_38252 : Nat := 8729627553728698921817

theorem tailTrace_38252 : CollatzResearch.WordTrace tailWord_38252 prefixEnd_38252 8729627553728698921817 := by
  unfold tailWord_38252
  simp only [CollatzResearch.WordTrace]
  refine ⟨697582528713505883298505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 930110038284674511064673 697582528713505883298505)
  ·
    refine ⟨523186896535129412473879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 697582528713505883298505 523186896535129412473879)
    ·
      refine ⟨784780344802694118710819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 523186896535129412473879 784780344802694118710819)
      ·
        refine ⟨1177170517204041178066229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784780344802694118710819 1177170517204041178066229)
        ·
          refine ⟨110359735987878860443709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1177170517204041178066229 110359735987878860443709)
          ·
            refine ⟨41384900995454572666391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110359735987878860443709 41384900995454572666391)
            ·
              refine ⟨62077351493181858999587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41384900995454572666391 62077351493181858999587)
              ·
                refine ⟨93116027239772788499381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62077351493181858999587 93116027239772788499381)
                ·
                  refine ⟨8729627553728698921817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93116027239772788499381 8729627553728698921817)
                  ·
                    rfl

theorem cell21_38252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_38252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38252 prefixEnd_38252 := by exact prefixLift 38252
  have htrace : WordTrace (prefixWord ++ tailWord_38252) baseStart_38252 baseEnd_38252 := by
    simpa [prefixWord, tailWord_38252, baseEnd_38252] using wordTrace_append hprefix tailTrace_38252
  have hstable : (prefixWord ++ tailWord_38252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38252).length < 2 ^ (prefixWord ++ tailWord_38252).sum := by decide
  have hdescent : baseEnd_38252 < baseStart_38252 := by decide
  rcases family_descends (prefixWord ++ tailWord_38252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38280 : List Nat := [2, 1, 3, 3, 1, 2, 2, 7]
def baseStart_38280 : Nat := 118140960795 + 38280 * 2 ^ 59
def prefixEnd_38280 : Nat := 4983230072969 + 3 ^ 40 * 38280 * 2
def baseEnd_38280 : Nat := 2912005845068957485031

theorem tailTrace_38280 : CollatzResearch.WordTrace tailWord_38280 prefixEnd_38280 2912005845068957485031 := by
  unfold tailWord_38280
  simp only [CollatzResearch.WordTrace]
  refine ⟨698093150662786274308147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 930790867550381699077529 698093150662786274308147)
  ·
    refine ⟨1047139725994179411462221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 698093150662786274308147 1047139725994179411462221)
    ·
      refine ⟨392677397247817279298333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1047139725994179411462221 392677397247817279298333)
      ·
        refine ⟨147254023967931479736875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 392677397247817279298333 147254023967931479736875)
        ·
          refine ⟨220881035951897219605313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147254023967931479736875 220881035951897219605313)
          ·
            refine ⟨165660776963922914703985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220881035951897219605313 165660776963922914703985)
            ·
              refine ⟨124245582722942186027989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165660776963922914703985 124245582722942186027989)
              ·
                refine ⟨2912005845068957485031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 124245582722942186027989 2912005845068957485031)
                ·
                  rfl

theorem cell21_38280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_38280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38280 prefixEnd_38280 := by exact prefixLift 38280
  have htrace : WordTrace (prefixWord ++ tailWord_38280) baseStart_38280 baseEnd_38280 := by
    simpa [prefixWord, tailWord_38280, baseEnd_38280] using wordTrace_append hprefix tailTrace_38280
  have hstable : (prefixWord ++ tailWord_38280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38280).length < 2 ^ (prefixWord ++ tailWord_38280).sum := by decide
  have hdescent : baseEnd_38280 < baseStart_38280 := by decide
  rcases family_descends (prefixWord ++ tailWord_38280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38300 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 4]
def baseStart_38300 : Nat := 118140960795 + 38300 * 2 ^ 59
def prefixEnd_38300 : Nat := 4983230072969 + 3 ^ 40 * 38300 * 2
def baseEnd_38300 : Nat := 8740581807691282121719

theorem tailTrace_38300 : CollatzResearch.WordTrace tailWord_38300 prefixEnd_38300 8740581807691282121719 := by
  unfold tailWord_38300
  simp only [CollatzResearch.WordTrace]
  refine ⟨698457880626557982172177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 931277174168743976229569 698457880626557982172177)
  ·
    refine ⟨523843410469918486629133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 698457880626557982172177 523843410469918486629133)
    ·
      refine ⟨196441278926219432485925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 523843410469918486629133 196441278926219432485925)
      ·
        refine ⟨36832739798666143591111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196441278926219432485925 36832739798666143591111)
        ·
          refine ⟨55249109697999215386667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36832739798666143591111 55249109697999215386667)
          ·
            refine ⟨82873664546998823080001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55249109697999215386667 82873664546998823080001)
            ·
              refine ⟨62155248410249117310001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82873664546998823080001 62155248410249117310001)
              ·
                refine ⟨46616436307686837982501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62155248410249117310001 46616436307686837982501)
                ·
                  refine ⟨8740581807691282121719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46616436307686837982501 8740581807691282121719)
                  ·
                    rfl

theorem cell21_38300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_38300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38300 prefixEnd_38300 := by exact prefixLift 38300
  have htrace : WordTrace (prefixWord ++ tailWord_38300) baseStart_38300 baseEnd_38300 := by
    simpa [prefixWord, tailWord_38300, baseEnd_38300] using wordTrace_append hprefix tailTrace_38300
  have hstable : (prefixWord ++ tailWord_38300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38300).length < 2 ^ (prefixWord ++ tailWord_38300).sum := by decide
  have hdescent : baseEnd_38300 < baseStart_38300 := by decide
  rcases family_descends (prefixWord ++ tailWord_38300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38311 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 5]
def baseStart_38311 : Nat := 118140960795 + 38311 * 2 ^ 59
def prefixEnd_38311 : Nat := 4983230072969 + 3 ^ 40 * 38311 * 2
def baseEnd_38311 : Nat := 8743092157557707438363

theorem tailTrace_38311 : CollatzResearch.WordTrace tailWord_38311 prefixEnd_38311 8743092157557707438363 := by
  unfold tailWord_38311
  simp only [CollatzResearch.WordTrace]
  refine ⟨1397316964213264842994787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 931544642808843228663191 1397316964213264842994787)
  ·
    refine ⟨2095975446319897264492181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1397316964213264842994787 2095975446319897264492181)
    ·
      refine ⟨98248849046245184273071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2095975446319897264492181 98248849046245184273071)
      ·
        refine ⟨147373273569367776409607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98248849046245184273071 147373273569367776409607)
        ·
          refine ⟨221059910354051664614411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147373273569367776409607 221059910354051664614411)
          ·
            refine ⟨331589865531077496921617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221059910354051664614411 331589865531077496921617)
            ·
              refine ⟨248692399148308122691213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331589865531077496921617 248692399148308122691213)
              ·
                refine ⟨93259649680615546009205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248692399148308122691213 93259649680615546009205)
                ·
                  refine ⟨8743092157557707438363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93259649680615546009205 8743092157557707438363)
                  ·
                    rfl

theorem cell21_38311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_38311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38311 prefixEnd_38311 := by exact prefixLift 38311
  have htrace : WordTrace (prefixWord ++ tailWord_38311) baseStart_38311 baseEnd_38311 := by
    simpa [prefixWord, tailWord_38311, baseEnd_38311] using wordTrace_append hprefix tailTrace_38311
  have hstable : (prefixWord ++ tailWord_38311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38311).length < 2 ^ (prefixWord ++ tailWord_38311).sum := by decide
  have hdescent : baseEnd_38311 < baseStart_38311 := by decide
  rcases family_descends (prefixWord ++ tailWord_38311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38339 : List Nat := [1, 1, 1, 3, 1, 1, 4, 9]
def baseStart_38339 : Nat := 118140960795 + 38339 * 2 ^ 59
def prefixEnd_38339 : Nat := 4983230072969 + 3 ^ 40 * 38339 * 2
def baseEnd_38339 : Nat := 2916494046345293657213

theorem tailTrace_38339 : CollatzResearch.WordTrace tailWord_38339 prefixEnd_38339 2916494046345293657213 := by
  unfold tailWord_38339
  simp only [CollatzResearch.WordTrace]
  refine ⟨1398338208111825625014071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 932225472074550416676047 1398338208111825625014071)
  ·
    refine ⟨2097507312167738437521107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1398338208111825625014071 2097507312167738437521107)
    ·
      refine ⟨3146260968251607656281661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2097507312167738437521107 3146260968251607656281661)
      ·
        refine ⟨1179847863094352871105623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3146260968251607656281661 1179847863094352871105623)
        ·
          refine ⟨1769771794641529306658435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179847863094352871105623 1769771794641529306658435)
          ·
            refine ⟨2654657691962293959987653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769771794641529306658435 2654657691962293959987653)
            ·
              refine ⟨497748317242930117497685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2654657691962293959987653 497748317242930117497685)
              ·
                refine ⟨2916494046345293657213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 497748317242930117497685 2916494046345293657213)
                ·
                  rfl

theorem cell21_38339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 9].length) (baseStart_38339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38339 prefixEnd_38339 := by exact prefixLift 38339
  have htrace : WordTrace (prefixWord ++ tailWord_38339) baseStart_38339 baseEnd_38339 := by
    simpa [prefixWord, tailWord_38339, baseEnd_38339] using wordTrace_append hprefix tailTrace_38339
  have hstable : (prefixWord ++ tailWord_38339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38339).length < 2 ^ (prefixWord ++ tailWord_38339).sum := by decide
  have hdescent : baseEnd_38339 < baseStart_38339 := by decide
  rcases family_descends (prefixWord ++ tailWord_38339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38390 : List Nat := [5, 1, 1, 1, 2, 4, 2, 5]
def baseStart_38390 : Nat := 118140960795 + 38390 * 2 ^ 59
def prefixEnd_38390 : Nat := 4983230072969 + 3 ^ 40 * 38390 * 2
def baseEnd_38390 : Nat := 2920373677957041873845

theorem tailTrace_38390 : CollatzResearch.WordTrace tailWord_38390 prefixEnd_38390 2920373677957041873845 := by
  unfold tailWord_38390
  simp only [CollatzResearch.WordTrace]
  refine ⟨87512395682941333445039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 933465553951374223413749 87512395682941333445039)
  ·
    refine ⟨131268593524412000167559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87512395682941333445039 131268593524412000167559)
    ·
      refine ⟨196902890286618000251339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131268593524412000167559 196902890286618000251339)
      ·
        refine ⟨295354335429927000377009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196902890286618000251339 295354335429927000377009)
        ·
          refine ⟨221515751572445250282757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295354335429927000377009 221515751572445250282757)
          ·
            refine ⟨41534203419833484428017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221515751572445250282757 41534203419833484428017)
            ·
              refine ⟨31150652564875113321013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41534203419833484428017 31150652564875113321013)
              ·
                refine ⟨2920373677957041873845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31150652564875113321013 2920373677957041873845)
                ·
                  rfl

theorem cell21_38390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_38390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38390 prefixEnd_38390 := by exact prefixLift 38390
  have htrace : WordTrace (prefixWord ++ tailWord_38390) baseStart_38390 baseEnd_38390 := by
    simpa [prefixWord, tailWord_38390, baseEnd_38390] using wordTrace_append hprefix tailTrace_38390
  have hstable : (prefixWord ++ tailWord_38390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38390).length < 2 ^ (prefixWord ++ tailWord_38390).sum := by decide
  have hdescent : baseEnd_38390 < baseStart_38390 := by decide
  rcases family_descends (prefixWord ++ tailWord_38390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38421 : List Nat := [1, 3, 2, 1, 3, 3, 3, 2, 3]
def baseStart_38421 : Nat := 118140960795 + 38421 * 2 ^ 59
def prefixEnd_38421 : Nat := 4983230072969 + 3 ^ 40 * 38421 * 2
def baseEnd_38421 : Nat := 8768195656221960604805

theorem tailTrace_38421 : CollatzResearch.WordTrace tailWord_38421 prefixEnd_38421 8768195656221960604805 := by
  unfold tailWord_38421
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401328993814753629499117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 934219329209835752999411 1401328993814753629499117)
  ·
    refine ⟨525498372680532611062169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1401328993814753629499117 525498372680532611062169)
    ·
      refine ⟨394123779510399458296627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 525498372680532611062169 394123779510399458296627)
      ·
        refine ⟨591185669265599187444941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394123779510399458296627 591185669265599187444941)
        ·
          refine ⟨221694625974599695291853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 591185669265599187444941 221694625974599695291853)
          ·
            refine ⟨83135484740474885734445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221694625974599695291853 83135484740474885734445)
            ·
              refine ⟨31175806777678082150417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83135484740474885734445 31175806777678082150417)
              ·
                refine ⟨23381855083258561612813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31175806777678082150417 23381855083258561612813)
                ·
                  refine ⟨8768195656221960604805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23381855083258561612813 8768195656221960604805)
                  ·
                    rfl

theorem cell21_38421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_38421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38421 prefixEnd_38421 := by exact prefixLift 38421
  have htrace : WordTrace (prefixWord ++ tailWord_38421) baseStart_38421 baseEnd_38421 := by
    simpa [prefixWord, tailWord_38421, baseEnd_38421] using wordTrace_append hprefix tailTrace_38421
  have hstable : (prefixWord ++ tailWord_38421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38421).length < 2 ^ (prefixWord ++ tailWord_38421).sum := by decide
  have hdescent : baseEnd_38421 < baseStart_38421 := by decide
  rcases family_descends (prefixWord ++ tailWord_38421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38432 : List Nat := [2, 1, 1, 6, 1, 1, 1, 8]
def baseStart_38432 : Nat := 118140960795 + 38432 * 2 ^ 59
def prefixEnd_38432 : Nat := 4983230072969 + 3 ^ 40 * 38432 * 2
def baseEnd_38432 : Nat := 2923568668696128640483

theorem tailTrace_38432 : CollatzResearch.WordTrace tailWord_38432 prefixEnd_38432 2923568668696128640483 := by
  unfold tailWord_38432
  simp only [CollatzResearch.WordTrace]
  refine ⟨700865098387451254074775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 934486797849935005433033 700865098387451254074775)
  ·
    refine ⟨1051297647581176881112163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 700865098387451254074775 1051297647581176881112163)
    ·
      refine ⟨1576946471371765321668245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1051297647581176881112163 1576946471371765321668245)
      ·
        refine ⟨73919365845551499453199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1576946471371765321668245 73919365845551499453199)
        ·
          refine ⟨110879048768327249179799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73919365845551499453199 110879048768327249179799)
          ·
            refine ⟨166318573152490873769699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110879048768327249179799 166318573152490873769699)
            ·
              refine ⟨249477859728736310654549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166318573152490873769699 249477859728736310654549)
              ·
                refine ⟨2923568668696128640483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 249477859728736310654549 2923568668696128640483)
                ·
                  rfl

theorem cell21_38432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_38432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38432 prefixEnd_38432 := by exact prefixLift 38432
  have htrace : WordTrace (prefixWord ++ tailWord_38432) baseStart_38432 baseEnd_38432 := by
    simpa [prefixWord, tailWord_38432, baseEnd_38432] using wordTrace_append hprefix tailTrace_38432
  have hstable : (prefixWord ++ tailWord_38432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38432).length < 2 ^ (prefixWord ++ tailWord_38432).sum := by decide
  have hdescent : baseEnd_38432 < baseStart_38432 := by decide
  rcases family_descends (prefixWord ++ tailWord_38432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38539 : List Nat := [1, 1, 1, 1, 4, 1, 3, 6, 3]
def baseStart_38539 : Nat := 118140960795 + 38539 * 2 ^ 59
def prefixEnd_38539 : Nat := 4983230072969 + 3 ^ 40 * 38539 * 2
def baseEnd_38539 : Nat := 8795124863879977637897

theorem tailTrace_38539 : CollatzResearch.WordTrace tailWord_38539 prefixEnd_38539 8795124863879977637897 := by
  unfold tailWord_38539
  simp only [CollatzResearch.WordTrace]
  refine ⟨1405632807387259782294671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 937088538258173188196447 1405632807387259782294671)
  ·
    refine ⟨2108449211080889673442007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1405632807387259782294671 2108449211080889673442007)
    ·
      refine ⟨3162673816621334510163011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2108449211080889673442007 3162673816621334510163011)
      ·
        refine ⟨4744010724932001765244517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3162673816621334510163011 4744010724932001765244517)
        ·
          refine ⟨889502010924750330983347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4744010724932001765244517 889502010924750330983347)
          ·
            refine ⟨1334253016387125496475021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889502010924750330983347 1334253016387125496475021)
            ·
              refine ⟨500344881145172061178133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1334253016387125496475021 500344881145172061178133)
              ·
                refine ⟨23453666303679940367725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 500344881145172061178133 23453666303679940367725)
                ·
                  refine ⟨8795124863879977637897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23453666303679940367725 8795124863879977637897)
                  ·
                    rfl

theorem cell21_38539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 3].length) (baseStart_38539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38539 prefixEnd_38539 := by exact prefixLift 38539
  have htrace : WordTrace (prefixWord ++ tailWord_38539) baseStart_38539 baseEnd_38539 := by
    simpa [prefixWord, tailWord_38539, baseEnd_38539] using wordTrace_append hprefix tailTrace_38539
  have hstable : (prefixWord ++ tailWord_38539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38539).length < 2 ^ (prefixWord ++ tailWord_38539).sum := by decide
  have hdescent : baseEnd_38539 < baseStart_38539 := by decide
  rcases family_descends (prefixWord ++ tailWord_38539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38559 : List Nat := [1, 1, 2, 7, 2, 1, 2, 5]
def baseStart_38559 : Nat := 118140960795 + 38559 * 2 ^ 59
def prefixEnd_38559 : Nat := 4983230072969 + 3 ^ 40 * 38559 * 2
def baseEnd_38559 : Nat := 2933229712121462434841

theorem tailTrace_38559 : CollatzResearch.WordTrace tailWord_38559 prefixEnd_38559 2933229712121462434841 := by
  unfold tailWord_38559
  simp only [CollatzResearch.WordTrace]
  refine ⟨1406362267314803198022731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 937574844876535465348487 1406362267314803198022731)
  ·
    refine ⟨2109543400972204797034097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1406362267314803198022731 2109543400972204797034097)
    ·
      refine ⟨1582157550729153597775573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2109543400972204797034097 1582157550729153597775573)
      ·
        refine ⟨37081817595214537447865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 1582157550729153597775573 37081817595214537447865)
        ·
          refine ⟨27811363196410903085899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37081817595214537447865 27811363196410903085899)
          ·
            refine ⟨41717044794616354628849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27811363196410903085899 41717044794616354628849)
            ·
              refine ⟨31287783595962265971637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41717044794616354628849 31287783595962265971637)
              ·
                refine ⟨2933229712121462434841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31287783595962265971637 2933229712121462434841)
                ·
                  rfl

theorem cell21_38559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 5].length) (baseStart_38559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38559 prefixEnd_38559 := by exact prefixLift 38559
  have htrace : WordTrace (prefixWord ++ tailWord_38559) baseStart_38559 baseEnd_38559 := by
    simpa [prefixWord, tailWord_38559, baseEnd_38559] using wordTrace_append hprefix tailTrace_38559
  have hstable : (prefixWord ++ tailWord_38559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38559).length < 2 ^ (prefixWord ++ tailWord_38559).sum := by decide
  have hdescent : baseEnd_38559 < baseStart_38559 := by decide
  rcases family_descends (prefixWord ++ tailWord_38559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38604 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 4]
def baseStart_38604 : Nat := 118140960795 + 38604 * 2 ^ 59
def prefixEnd_38604 : Nat := 4983230072969 + 3 ^ 40 * 38604 * 2
def baseEnd_38604 : Nat := 8809958749454309054431

theorem tailTrace_38604 : CollatzResearch.WordTrace tailWord_38604 prefixEnd_38604 8809958749454309054431 := by
  unfold tailWord_38604
  simp only [CollatzResearch.WordTrace]
  refine ⟨704001776075887941705433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 938669034767850588940577 704001776075887941705433)
  ·
    refine ⟨528001332056915956279075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 704001776075887941705433 528001332056915956279075)
    ·
      refine ⟨792001998085373934418613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 528001332056915956279075 792001998085373934418613)
      ·
        refine ⟨74250187320503806351745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 792001998085373934418613 74250187320503806351745)
        ·
          refine ⟨55687640490377854763809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74250187320503806351745 55687640490377854763809)
          ·
            refine ⟨41765730367783391072857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55687640490377854763809 41765730367783391072857)
            ·
              refine ⟨31324297775837543304643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41765730367783391072857 31324297775837543304643)
              ·
                refine ⟨46986446663756314956965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31324297775837543304643 46986446663756314956965)
                ·
                  refine ⟨8809958749454309054431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46986446663756314956965 8809958749454309054431)
                  ·
                    rfl

theorem cell21_38604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_38604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38604 prefixEnd_38604 := by exact prefixLift 38604
  have htrace : WordTrace (prefixWord ++ tailWord_38604) baseStart_38604 baseEnd_38604 := by
    simpa [prefixWord, tailWord_38604, baseEnd_38604] using wordTrace_append hprefix tailTrace_38604
  have hstable : (prefixWord ++ tailWord_38604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38604).length < 2 ^ (prefixWord ++ tailWord_38604).sum := by decide
  have hdescent : baseEnd_38604 < baseStart_38604 := by decide
  rcases family_descends (prefixWord ++ tailWord_38604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38646 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_38646 : Nat := 118140960795 + 38646 * 2 ^ 59
def prefixEnd_38646 : Nat := 4983230072969 + 3 ^ 40 * 38646 * 2
def baseEnd_38646 : Nat := 8819543721671569354345

theorem tailTrace_38646 : CollatzResearch.WordTrace tailWord_38646 prefixEnd_38646 8819543721671569354345 := by
  unfold tailWord_38646
  simp only [CollatzResearch.WordTrace]
  refine ⟨88095963624976066027487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 939690278666411370959861 88095963624976066027487)
  ·
    refine ⟨132143945437464099041231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88095963624976066027487 132143945437464099041231)
    ·
      refine ⟨198215918156196148561847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132143945437464099041231 198215918156196148561847)
      ·
        refine ⟨297323877234294222842771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198215918156196148561847 297323877234294222842771)
        ·
          refine ⟨445985815851441334264157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297323877234294222842771 445985815851441334264157)
          ·
            refine ⟨167244680944290500349059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 445985815851441334264157 167244680944290500349059)
            ·
              refine ⟨250867021416435750523589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167244680944290500349059 250867021416435750523589)
              ·
                refine ⟨47037566515581703223173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250867021416435750523589 47037566515581703223173)
                ·
                  refine ⟨8819543721671569354345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47037566515581703223173 8819543721671569354345)
                  ·
                    rfl

theorem cell21_38646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_38646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38646 prefixEnd_38646 := by exact prefixLift 38646
  have htrace : WordTrace (prefixWord ++ tailWord_38646) baseStart_38646 baseEnd_38646 := by
    simpa [prefixWord, tailWord_38646, baseEnd_38646] using wordTrace_append hprefix tailTrace_38646
  have hstable : (prefixWord ++ tailWord_38646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38646).length < 2 ^ (prefixWord ++ tailWord_38646).sum := by decide
  have hdescent : baseEnd_38646 < baseStart_38646 := by decide
  rcases family_descends (prefixWord ++ tailWord_38646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38660 : List Nat := [2, 3, 2, 2, 1, 2, 3, 6]
def baseStart_38660 : Nat := 118140960795 + 38660 * 2 ^ 59
def prefixEnd_38660 : Nat := 4983230072969 + 3 ^ 40 * 38660 * 2
def baseEnd_38660 : Nat := 2940912904136885373661

theorem tailTrace_38660 : CollatzResearch.WordTrace tailWord_38660 prefixEnd_38660 2940912904136885373661 := by
  unfold tailWord_38660
  simp only [CollatzResearch.WordTrace]
  refine ⟨705023019974448723724717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 940030693299264964966289 705023019974448723724717)
  ·
    refine ⟨264383632490418271396769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 705023019974448723724717 264383632490418271396769)
    ·
      refine ⟨198287724367813703547577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264383632490418271396769 198287724367813703547577)
      ·
        refine ⟨148715793275860277660683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198287724367813703547577 148715793275860277660683)
        ·
          refine ⟨223073689913790416491025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148715793275860277660683 223073689913790416491025)
          ·
            refine ⟨167305267435342812368269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223073689913790416491025 167305267435342812368269)
            ·
              refine ⟨62739475288253554638101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167305267435342812368269 62739475288253554638101)
              ·
                refine ⟨2940912904136885373661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62739475288253554638101 2940912904136885373661)
                ·
                  rfl

theorem cell21_38660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_38660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38660 prefixEnd_38660 := by exact prefixLift 38660
  have htrace : WordTrace (prefixWord ++ tailWord_38660) baseStart_38660 baseEnd_38660 := by
    simpa [prefixWord, tailWord_38660, baseEnd_38660] using wordTrace_append hprefix tailTrace_38660
  have hstable : (prefixWord ++ tailWord_38660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38660).length < 2 ^ (prefixWord ++ tailWord_38660).sum := by decide
  have hdescent : baseEnd_38660 < baseStart_38660 := by decide
  rcases family_descends (prefixWord ++ tailWord_38660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38691 : List Nat := [1, 1, 1, 4, 2, 1, 3, 5, 3]
def baseStart_38691 : Nat := 118140960795 + 38691 * 2 ^ 59
def prefixEnd_38691 : Nat := 4983230072969 + 3 ^ 40 * 38691 * 2
def baseEnd_38691 : Nat := 8829813334761491104253

theorem tailTrace_38691 : CollatzResearch.WordTrace tailWord_38691 prefixEnd_38691 8829813334761491104253 := by
  unfold tailWord_38691
  simp only [CollatzResearch.WordTrace]
  refine ⟨1411176702836589741827927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 940784468557726494551951 1411176702836589741827927)
  ·
    refine ⟨2116765054254884612741891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1411176702836589741827927 2116765054254884612741891)
    ·
      refine ⟨3175147581382326919112837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2116765054254884612741891 3175147581382326919112837)
      ·
        refine ⟨595340171509186297333657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3175147581382326919112837 595340171509186297333657)
        ·
          refine ⟨446505128631889723000243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595340171509186297333657 446505128631889723000243)
          ·
            refine ⟨669757692947834584500365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446505128631889723000243 669757692947834584500365)
            ·
              refine ⟨251159134855437969187637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 669757692947834584500365 251159134855437969187637)
              ·
                refine ⟨23546168892697309611341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 251159134855437969187637 23546168892697309611341)
                ·
                  refine ⟨8829813334761491104253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23546168892697309611341 8829813334761491104253)
                  ·
                    rfl

theorem cell21_38691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 3].length) (baseStart_38691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38691 prefixEnd_38691 := by exact prefixLift 38691
  have htrace : WordTrace (prefixWord ++ tailWord_38691) baseStart_38691 baseEnd_38691 := by
    simpa [prefixWord, tailWord_38691, baseEnd_38691] using wordTrace_append hprefix tailTrace_38691
  have hstable : (prefixWord ++ tailWord_38691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38691).length < 2 ^ (prefixWord ++ tailWord_38691).sum := by decide
  have hdescent : baseEnd_38691 < baseStart_38691 := by decide
  rcases family_descends (prefixWord ++ tailWord_38691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38705 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 6]
def baseStart_38705 : Nat := 118140960795 + 38705 * 2 ^ 59
def prefixEnd_38705 : Nat := 4983230072969 + 3 ^ 40 * 38705 * 2
def baseEnd_38705 : Nat := 8833008325500577870891

theorem tailTrace_38705 : CollatzResearch.WordTrace tailWord_38705 prefixEnd_38705 8833008325500577870891 := by
  unfold tailWord_38705
  simp only [CollatzResearch.WordTrace]
  refine ⟨1411687324785870132837569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 941124883190580088558379 1411687324785870132837569)
  ·
    refine ⟨1058765493589402599628177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1411687324785870132837569 1058765493589402599628177)
    ·
      refine ⟨794074120192051949721133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1058765493589402599628177 794074120192051949721133)
      ·
        refine ⟨297777795072019481145425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 794074120192051949721133 297777795072019481145425)
        ·
          refine ⟨223333346304014610859069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297777795072019481145425 223333346304014610859069)
          ·
            refine ⟨83750004864005479072151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223333346304014610859069 83750004864005479072151)
            ·
              refine ⟨125625007296008218608227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83750004864005479072151 125625007296008218608227)
              ·
                refine ⟨188437510944012327912341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125625007296008218608227 188437510944012327912341)
                ·
                  refine ⟨8833008325500577870891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 188437510944012327912341 8833008325500577870891)
                  ·
                    rfl

theorem cell21_38705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_38705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38705 prefixEnd_38705 := by exact prefixLift 38705
  have htrace : WordTrace (prefixWord ++ tailWord_38705) baseStart_38705 baseEnd_38705 := by
    simpa [prefixWord, tailWord_38705, baseEnd_38705] using wordTrace_append hprefix tailTrace_38705
  have hstable : (prefixWord ++ tailWord_38705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38705).length < 2 ^ (prefixWord ++ tailWord_38705).sum := by decide
  have hdescent : baseEnd_38705 < baseStart_38705 := by decide
  rcases family_descends (prefixWord ++ tailWord_38705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38708 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 5]
def baseStart_38708 : Nat := 118140960795 + 38708 * 2 ^ 59
def prefixEnd_38708 : Nat := 4983230072969 + 3 ^ 40 * 38708 * 2
def baseEnd_38708 : Nat := 8833692966373239320885

theorem tailTrace_38708 : CollatzResearch.WordTrace tailWord_38708 prefixEnd_38708 8833692966373239320885 := by
  unfold tailWord_38708
  simp only [CollatzResearch.WordTrace]
  refine ⟨705898371887500822598389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 941197829183334430131185 705898371887500822598389)
  ·
    refine ⟨66177972364453202118599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 705898371887500822598389 66177972364453202118599)
    ·
      refine ⟨99266958546679803177899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66177972364453202118599 99266958546679803177899)
      ·
        refine ⟨148900437820019704766849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99266958546679803177899 148900437820019704766849)
        ·
          refine ⟨111675328365014778575137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148900437820019704766849 111675328365014778575137)
          ·
            refine ⟨83756496273761083931353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111675328365014778575137 83756496273761083931353)
            ·
              refine ⟨62817372205320812948515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83756496273761083931353 62817372205320812948515)
              ·
                refine ⟨94226058307981219422773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62817372205320812948515 94226058307981219422773)
                ·
                  refine ⟨8833692966373239320885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94226058307981219422773 8833692966373239320885)
                  ·
                    rfl

theorem cell21_38708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_38708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38708 prefixEnd_38708 := by exact prefixLift 38708
  have htrace : WordTrace (prefixWord ++ tailWord_38708) baseStart_38708 baseEnd_38708 := by
    simpa [prefixWord, tailWord_38708, baseEnd_38708] using wordTrace_append hprefix tailTrace_38708
  have hstable : (prefixWord ++ tailWord_38708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38708).length < 2 ^ (prefixWord ++ tailWord_38708).sum := by decide
  have hdescent : baseEnd_38708 < baseStart_38708 := by decide
  rcases family_descends (prefixWord ++ tailWord_38708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38818 : List Nat := [3, 3, 1, 2, 3, 2, 2, 2, 3]
def baseStart_38818 : Nat := 118140960795 + 38818 * 2 ^ 59
def prefixEnd_38818 : Nat := 4983230072969 + 3 ^ 40 * 38818 * 2
def baseEnd_38818 : Nat := 8858796465037492487327

theorem tailTrace_38818 : CollatzResearch.WordTrace tailWord_38818 prefixEnd_38818 8858796465037492487327 := by
  unfold tailWord_38818
  simp only [CollatzResearch.WordTrace]
  refine ⟨353952193344122607925277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 943872515584326954467405 353952193344122607925277)
  ·
    refine ⟨132732072504045977971979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 353952193344122607925277 132732072504045977971979)
    ·
      refine ⟨199098108756068966957969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132732072504045977971979 199098108756068966957969)
      ·
        refine ⟨149323581567051725218477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199098108756068966957969 149323581567051725218477)
        ·
          refine ⟨55996343087644396956929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149323581567051725218477 55996343087644396956929)
          ·
            refine ⟨41997257315733297717697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55996343087644396956929 41997257315733297717697)
            ·
              refine ⟨31497942986799973288273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41997257315733297717697 31497942986799973288273)
              ·
                refine ⟨23623457240099979966205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31497942986799973288273 23623457240099979966205)
                ·
                  refine ⟨8858796465037492487327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23623457240099979966205 8858796465037492487327)
                  ·
                    rfl

theorem cell21_38818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_38818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38818 prefixEnd_38818 := by exact prefixLift 38818
  have htrace : WordTrace (prefixWord ++ tailWord_38818) baseStart_38818 baseEnd_38818 := by
    simpa [prefixWord, tailWord_38818, baseEnd_38818] using wordTrace_append hprefix tailTrace_38818
  have hstable : (prefixWord ++ tailWord_38818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38818).length < 2 ^ (prefixWord ++ tailWord_38818).sum := by decide
  have hdescent : baseEnd_38818 < baseStart_38818 := by decide
  rcases family_descends (prefixWord ++ tailWord_38818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38860 : List Nat := [2, 2, 1, 4, 1, 3, 2, 3, 3]
def baseStart_38860 : Nat := 118140960795 + 38860 * 2 ^ 59
def prefixEnd_38860 : Nat := 4983230072969 + 3 ^ 40 * 38860 * 2
def baseEnd_38860 : Nat := 8868381437254752787241

theorem tailTrace_38860 : CollatzResearch.WordTrace tailWord_38860 prefixEnd_38860 8868381437254752787241 := by
  unfold tailWord_38860
  simp only [CollatzResearch.WordTrace]
  refine ⟨708670319612165802365017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 944893759482887736486689 708670319612165802365017)
  ·
    refine ⟨531502739709124351773763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 708670319612165802365017 531502739709124351773763)
    ·
      refine ⟨797254109563686527660645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 531502739709124351773763 797254109563686527660645)
      ·
        refine ⟨149485145543191223936371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 797254109563686527660645 149485145543191223936371)
        ·
          refine ⟨224227718314786835904557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149485145543191223936371 224227718314786835904557)
          ·
            refine ⟨84085394368045063464209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224227718314786835904557 84085394368045063464209)
            ·
              refine ⟨63064045776033797598157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84085394368045063464209 63064045776033797598157)
              ·
                refine ⟨23649017166012674099309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63064045776033797598157 23649017166012674099309)
                ·
                  refine ⟨8868381437254752787241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23649017166012674099309 8868381437254752787241)
                  ·
                    rfl

theorem cell21_38860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_38860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38860 prefixEnd_38860 := by exact prefixLift 38860
  have htrace : WordTrace (prefixWord ++ tailWord_38860) baseStart_38860 baseEnd_38860 := by
    simpa [prefixWord, tailWord_38860, baseEnd_38860] using wordTrace_append hprefix tailTrace_38860
  have hstable : (prefixWord ++ tailWord_38860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38860).length < 2 ^ (prefixWord ++ tailWord_38860).sum := by decide
  have hdescent : baseEnd_38860 < baseStart_38860 := by decide
  rcases family_descends (prefixWord ++ tailWord_38860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38936 : List Nat := [2, 1, 2, 3, 2, 1, 5, 2, 3]
def baseStart_38936 : Nat := 118140960795 + 38936 * 2 ^ 59
def prefixEnd_38936 : Nat := 4983230072969 + 3 ^ 40 * 38936 * 2
def baseEnd_38936 : Nat := 8885725672695509520419

theorem tailTrace_38936 : CollatzResearch.WordTrace tailWord_38936 prefixEnd_38936 8885725672695509520419 := by
  unfold tailWord_38936
  simp only [CollatzResearch.WordTrace]
  refine ⟨710056293474498292248331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 946741724632664389664441 710056293474498292248331)
  ·
    refine ⟨1065084440211747438372497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 710056293474498292248331 1065084440211747438372497)
    ·
      refine ⟨798813330158810578779373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1065084440211747438372497 798813330158810578779373)
      ·
        refine ⟨299554998809553967042265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 798813330158810578779373 299554998809553967042265)
        ·
          refine ⟨224666249107165475281699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299554998809553967042265 224666249107165475281699)
          ·
            refine ⟨336999373660748212922549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224666249107165475281699 336999373660748212922549)
            ·
              refine ⟨31593691280695144961489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 336999373660748212922549 31593691280695144961489)
              ·
                refine ⟨23695268460521358721117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31593691280695144961489 23695268460521358721117)
                ·
                  refine ⟨8885725672695509520419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23695268460521358721117 8885725672695509520419)
                  ·
                    rfl

theorem cell21_38936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 3].length) (baseStart_38936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38936 prefixEnd_38936 := by exact prefixLift 38936
  have htrace : WordTrace (prefixWord ++ tailWord_38936) baseStart_38936 baseEnd_38936 := by
    simpa [prefixWord, tailWord_38936, baseEnd_38936] using wordTrace_append hprefix tailTrace_38936
  have hstable : (prefixWord ++ tailWord_38936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38936).length < 2 ^ (prefixWord ++ tailWord_38936).sum := by decide
  have hdescent : baseEnd_38936 < baseStart_38936 := by decide
  rcases family_descends (prefixWord ++ tailWord_38936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38947 : List Nat := [1, 1, 1, 4, 3, 1, 4, 6]
def baseStart_38947 : Nat := 118140960795 + 38947 * 2 ^ 59
def prefixEnd_38947 : Nat := 4983230072969 + 3 ^ 40 * 38947 * 2
def baseEnd_38947 : Nat := 2962745340853978279021

theorem tailTrace_38947 : CollatzResearch.WordTrace tailWord_38947 prefixEnd_38947 2962745340853978279021 := by
  unfold tailWord_38947
  simp only [CollatzResearch.WordTrace]
  refine ⟨1420513789909145463147095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 947009193272763642098063 1420513789909145463147095)
  ·
    refine ⟨2130770684863718194720643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1420513789909145463147095 2130770684863718194720643)
    ·
      refine ⟨3196156027295577292080965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2130770684863718194720643 3196156027295577292080965)
      ·
        refine ⟨599279255117920742265181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3196156027295577292080965 599279255117920742265181)
        ·
          refine ⟨224729720669220278349443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 599279255117920742265181 224729720669220278349443)
          ·
            refine ⟨337094581003830417524165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224729720669220278349443 337094581003830417524165)
            ·
              refine ⟨63205233938218203285781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 337094581003830417524165 63205233938218203285781)
              ·
                refine ⟨2962745340853978279021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63205233938218203285781 2962745340853978279021)
                ·
                  rfl

theorem cell21_38947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 6].length) (baseStart_38947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38947 prefixEnd_38947 := by exact prefixLift 38947
  have htrace : WordTrace (prefixWord ++ tailWord_38947) baseStart_38947 baseEnd_38947 := by
    simpa [prefixWord, tailWord_38947, baseEnd_38947] using wordTrace_append hprefix tailTrace_38947
  have hstable : (prefixWord ++ tailWord_38947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38947).length < 2 ^ (prefixWord ++ tailWord_38947).sum := by decide
  have hdescent : baseEnd_38947 < baseStart_38947 := by decide
  rcases family_descends (prefixWord ++ tailWord_38947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38998 : List Nat := [5, 2, 2, 1, 1, 3, 1, 6]
def baseStart_38998 : Nat := 118140960795 + 38998 * 2 ^ 59
def prefixEnd_38998 : Nat := 4983230072969 + 3 ^ 40 * 38998 * 2
def baseEnd_38998 : Nat := 2966624972465726495653

theorem tailTrace_38998 : CollatzResearch.WordTrace tailWord_38998 prefixEnd_38998 2966624972465726495653 := by
  unfold tailWord_38998
  simp only [CollatzResearch.WordTrace]
  refine ⟨88898369545273823328353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 948249275149587448835765 88898369545273823328353)
  ·
    refine ⟨66673777158955367496265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88898369545273823328353 66673777158955367496265)
    ·
      refine ⟨50005332869216525622199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66673777158955367496265 50005332869216525622199)
      ·
        refine ⟨75007999303824788433299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50005332869216525622199 75007999303824788433299)
        ·
          refine ⟨112511998955737182649949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75007999303824788433299 112511998955737182649949)
          ·
            refine ⟨42191999608401443493731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112511998955737182649949 42191999608401443493731)
            ·
              refine ⟨63287999412602165240597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42191999608401443493731 63287999412602165240597)
              ·
                refine ⟨2966624972465726495653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63287999412602165240597 2966624972465726495653)
                ·
                  rfl

theorem cell21_38998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_38998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_38998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_38998 prefixEnd_38998 := by exact prefixLift 38998
  have htrace : WordTrace (prefixWord ++ tailWord_38998) baseStart_38998 baseEnd_38998 := by
    simpa [prefixWord, tailWord_38998, baseEnd_38998] using wordTrace_append hprefix tailTrace_38998
  have hstable : (prefixWord ++ tailWord_38998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38998).length < 2 ^ (prefixWord ++ tailWord_38998).sum := by decide
  have hdescent : baseEnd_38998 < baseStart_38998 := by decide
  rcases family_descends (prefixWord ++ tailWord_38998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39060 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 4]
def baseStart_39060 : Nat := 118140960795 + 39060 * 2 ^ 59
def prefixEnd_39060 : Nat := 4983230072969 + 3 ^ 40 * 39060 * 2
def baseEnd_39060 : Nat := 8914024162098849453499

theorem tailTrace_39060 : CollatzResearch.WordTrace tailWord_39060 prefixEnd_39060 8914024162098849453499 := by
  unfold tailWord_39060
  simp only [CollatzResearch.WordTrace]
  refine ⟨712317619249882881005317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 949756825666510508007089 712317619249882881005317)
  ·
    refine ⟨133559553609353040188497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 712317619249882881005317 133559553609353040188497)
    ·
      refine ⟨100169665207014780141373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133559553609353040188497 100169665207014780141373)
      ·
        refine ⟨37563624452630542553015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100169665207014780141373 37563624452630542553015)
        ·
          refine ⟨56345436678945813829523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37563624452630542553015 56345436678945813829523)
          ·
            refine ⟨84518155018418720744285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56345436678945813829523 84518155018418720744285)
            ·
              refine ⟨31694308131907020279107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84518155018418720744285 31694308131907020279107)
              ·
                refine ⟨47541462197860530418661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31694308131907020279107 47541462197860530418661)
                ·
                  refine ⟨8914024162098849453499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47541462197860530418661 8914024162098849453499)
                  ·
                    rfl

theorem cell21_39060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_39060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39060 prefixEnd_39060 := by exact prefixLift 39060
  have htrace : WordTrace (prefixWord ++ tailWord_39060) baseStart_39060 baseEnd_39060 := by
    simpa [prefixWord, tailWord_39060, baseEnd_39060] using wordTrace_append hprefix tailTrace_39060
  have hstable : (prefixWord ++ tailWord_39060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39060).length < 2 ^ (prefixWord ++ tailWord_39060).sum := by decide
  have hdescent : baseEnd_39060 < baseStart_39060 := by decide
  rcases family_descends (prefixWord ++ tailWord_39060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39085 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 6]
def baseStart_39085 : Nat := 118140960795 + 39085 * 2 ^ 59
def prefixEnd_39085 : Nat := 4983230072969 + 3 ^ 40 * 39085 * 2
def baseEnd_39085 : Nat := 8919729502704361536781

theorem tailTrace_39085 : CollatzResearch.WordTrace tailWord_39085 prefixEnd_39085 8919729502704361536781 := by
  unfold tailWord_39085
  simp only [CollatzResearch.WordTrace]
  refine ⟨1425547063409195031670709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 950364708939463354447139 1425547063409195031670709)
  ·
    refine ⟨133645037194612034219129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1425547063409195031670709 133645037194612034219129)
    ·
      refine ⟨100233777895959025664347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133645037194612034219129 100233777895959025664347)
      ·
        refine ⟨150350666843938538496521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100233777895959025664347 150350666843938538496521)
        ·
          refine ⟨112763000132953903872391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150350666843938538496521 112763000132953903872391)
          ·
            refine ⟨169144500199430855808587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112763000132953903872391 169144500199430855808587)
            ·
              refine ⟨253716750299146283712881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169144500199430855808587 253716750299146283712881)
              ·
                refine ⟨190287562724359712784661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253716750299146283712881 190287562724359712784661)
                ·
                  refine ⟨8919729502704361536781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 190287562724359712784661 8919729502704361536781)
                  ·
                    rfl

theorem cell21_39085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_39085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39085 prefixEnd_39085 := by exact prefixLift 39085
  have htrace : WordTrace (prefixWord ++ tailWord_39085) baseStart_39085 baseEnd_39085 := by
    simpa [prefixWord, tailWord_39085, baseEnd_39085] using wordTrace_append hprefix tailTrace_39085
  have hstable : (prefixWord ++ tailWord_39085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39085).length < 2 ^ (prefixWord ++ tailWord_39085).sum := by decide
  have hdescent : baseEnd_39085 < baseStart_39085 := by decide
  rcases family_descends (prefixWord ++ tailWord_39085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39105 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 5]
def baseStart_39105 : Nat := 118140960795 + 39105 * 2 ^ 59
def prefixEnd_39105 : Nat := 4983230072969 + 3 ^ 40 * 39105 * 2
def baseEnd_39105 : Nat := 8924293775188771203407

theorem tailTrace_39105 : CollatzResearch.WordTrace tailWord_39105 prefixEnd_39105 8924293775188771203407 := by
  unfold tailWord_39105
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426276523336738447398769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 950851015557825631599179 1426276523336738447398769)
  ·
    refine ⟨1069707392502553835549077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1426276523336738447398769 1069707392502553835549077)
    ·
      refine ⟨50142534023557211041363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1069707392502553835549077 50142534023557211041363)
      ·
        refine ⟨75213801035335816562045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50142534023557211041363 75213801035335816562045)
        ·
          refine ⟨28205175388250931210767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75213801035335816562045 28205175388250931210767)
          ·
            refine ⟨42307763082376396816151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28205175388250931210767 42307763082376396816151)
            ·
              refine ⟨63461644623564595224227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42307763082376396816151 63461644623564595224227)
              ·
                refine ⟨95192466935346892836341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63461644623564595224227 95192466935346892836341)
                ·
                  refine ⟨8924293775188771203407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95192466935346892836341 8924293775188771203407)
                  ·
                    rfl

theorem cell21_39105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 5].length) (baseStart_39105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39105 prefixEnd_39105 := by exact prefixLift 39105
  have htrace : WordTrace (prefixWord ++ tailWord_39105) baseStart_39105 baseEnd_39105 := by
    simpa [prefixWord, tailWord_39105, baseEnd_39105] using wordTrace_append hprefix tailTrace_39105
  have hstable : (prefixWord ++ tailWord_39105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39105).length < 2 ^ (prefixWord ++ tailWord_39105).sum := by decide
  have hdescent : baseEnd_39105 < baseStart_39105 := by decide
  rcases family_descends (prefixWord ++ tailWord_39105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39113 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 5]
def baseStart_39113 : Nat := 118140960795 + 39113 * 2 ^ 59
def prefixEnd_39113 : Nat := 4983230072969 + 3 ^ 40 * 39113 * 2
def baseEnd_39113 : Nat := 8926119484182535070057

theorem tailTrace_39113 : CollatzResearch.WordTrace tailWord_39113 prefixEnd_39113 8926119484182535070057 := by
  unfold tailWord_39113
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426568307307755813689993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 951045538205170542459995 1426568307307755813689993)
  ·
    refine ⟨1069926230480816860267495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1426568307307755813689993 1069926230480816860267495)
    ·
      refine ⟨1604889345721225290401243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069926230480816860267495 1604889345721225290401243)
      ·
        refine ⟨2407334018581837935601865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604889345721225290401243 2407334018581837935601865)
        ·
          refine ⟨1805500513936378451701399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407334018581837935601865 1805500513936378451701399)
          ·
            refine ⟨2708250770904567677552099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805500513936378451701399 2708250770904567677552099)
            ·
              refine ⟨4062376156356851516328149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708250770904567677552099 4062376156356851516328149)
              ·
                refine ⟨95211941164613707413941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4062376156356851516328149 95211941164613707413941)
                ·
                  refine ⟨8926119484182535070057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95211941164613707413941 8926119484182535070057)
                  ·
                    rfl

theorem cell21_39113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_39113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39113 prefixEnd_39113 := by exact prefixLift 39113
  have htrace : WordTrace (prefixWord ++ tailWord_39113) baseStart_39113 baseEnd_39113 := by
    simpa [prefixWord, tailWord_39113, baseEnd_39113] using wordTrace_append hprefix tailTrace_39113
  have hstable : (prefixWord ++ tailWord_39113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39113).length < 2 ^ (prefixWord ++ tailWord_39113).sum := by decide
  have hdescent : baseEnd_39113 < baseStart_39113 := by decide
  rcases family_descends (prefixWord ++ tailWord_39113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39164 : List Nat := [2, 2, 2, 1, 4, 1, 4, 2, 3]
def baseStart_39164 : Nat := 118140960795 + 39164 * 2 ^ 59
def prefixEnd_39164 : Nat := 4983230072969 + 3 ^ 40 * 39164 * 2
def baseEnd_39164 : Nat := 8937758379017779719953

theorem tailTrace_39164 : CollatzResearch.WordTrace tailWord_39164 prefixEnd_39164 8937758379017779719953 := by
  unfold tailWord_39164
  simp only [CollatzResearch.WordTrace]
  refine ⟨714214215061495761898273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 952285620081994349197697 714214215061495761898273)
  ·
    refine ⟨535660661296121821423705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 714214215061495761898273 535660661296121821423705)
    ·
      refine ⟨401745495972091366067779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 535660661296121821423705 401745495972091366067779)
      ·
        refine ⟨602618243958137049101669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401745495972091366067779 602618243958137049101669)
        ·
          refine ⟨112990920742150696706563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 602618243958137049101669 112990920742150696706563)
          ·
            refine ⟨169486381113226045059845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112990920742150696706563 169486381113226045059845)
            ·
              refine ⟨31778696458729883448721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169486381113226045059845 31778696458729883448721)
              ·
                refine ⟨23834022344047412586541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31778696458729883448721 23834022344047412586541)
                ·
                  refine ⟨8937758379017779719953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23834022344047412586541 8937758379017779719953)
                  ·
                    rfl

theorem cell21_39164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_39164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39164 prefixEnd_39164 := by exact prefixLift 39164
  have htrace : WordTrace (prefixWord ++ tailWord_39164) baseStart_39164 baseEnd_39164 := by
    simpa [prefixWord, tailWord_39164, baseEnd_39164] using wordTrace_append hprefix tailTrace_39164
  have hstable : (prefixWord ++ tailWord_39164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39164).length < 2 ^ (prefixWord ++ tailWord_39164).sum := by decide
  have hdescent : baseEnd_39164 < baseStart_39164 := by decide
  rcases family_descends (prefixWord ++ tailWord_39164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39189 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 7]
def baseStart_39189 : Nat := 118140960795 + 39189 * 2 ^ 59
def prefixEnd_39189 : Nat := 4983230072969 + 3 ^ 40 * 39189 * 2
def baseEnd_39189 : Nat := 8943463719623291803235

theorem tailTrace_39189 : CollatzResearch.WordTrace tailWord_39189 prefixEnd_39189 8943463719623291803235 := by
  unfold tailWord_39189
  simp only [CollatzResearch.WordTrace]
  refine ⟨1429340255032420793456621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 952893503354947195637747 1429340255032420793456621)
  ·
    refine ⟨536002595637157797546233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1429340255032420793456621 536002595637157797546233)
    ·
      refine ⟨402001946727868348159675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 536002595637157797546233 402001946727868348159675)
      ·
        refine ⟨603002920091802522239513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402001946727868348159675 603002920091802522239513)
        ·
          refine ⟨452252190068851891679635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 603002920091802522239513 452252190068851891679635)
          ·
            refine ⟨678378285103277837519453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452252190068851891679635 678378285103277837519453)
            ·
              refine ⟨254391856913729189069795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 678378285103277837519453 254391856913729189069795)
              ·
                refine ⟨381587785370593783604693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254391856913729189069795 381587785370593783604693)
                ·
                  refine ⟨8943463719623291803235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 381587785370593783604693 8943463719623291803235)
                  ·
                    rfl

theorem cell21_39189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_39189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39189 prefixEnd_39189 := by exact prefixLift 39189
  have htrace : WordTrace (prefixWord ++ tailWord_39189) baseStart_39189 baseEnd_39189 := by
    simpa [prefixWord, tailWord_39189, baseEnd_39189] using wordTrace_append hprefix tailTrace_39189
  have hstable : (prefixWord ++ tailWord_39189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39189).length < 2 ^ (prefixWord ++ tailWord_39189).sum := by decide
  have hdescent : baseEnd_39189 < baseStart_39189 := by decide
  rcases family_descends (prefixWord ++ tailWord_39189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39282 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_39282 : Nat := 118140960795 + 39282 * 2 ^ 59
def prefixEnd_39282 : Nat := 4983230072969 + 3 ^ 40 * 39282 * 2
def baseEnd_39282 : Nat := 8964687586675796753045

theorem tailTrace_39282 : CollatzResearch.WordTrace tailWord_39282 prefixEnd_39282 8964687586675796753045 := by
  unfold tailWord_39282
  simp only [CollatzResearch.WordTrace]
  refine ⟨358183060923874419148025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 955154829130331784394733 358183060923874419148025)
  ·
    refine ⟨268637295692905814361019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 358183060923874419148025 268637295692905814361019)
    ·
      refine ⟨402955943539358721541529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268637295692905814361019 402955943539358721541529)
      ·
        refine ⟨302216957654519041156147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402955943539358721541529 302216957654519041156147)
        ·
          refine ⟨453325436481778561734221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302216957654519041156147 453325436481778561734221)
          ·
            refine ⟨169997038680666960650333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 453325436481778561734221 169997038680666960650333)
            ·
              refine ⟨63748889505250110243875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169997038680666960650333 63748889505250110243875)
              ·
                refine ⟨95623334257875165365813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63748889505250110243875 95623334257875165365813)
                ·
                  refine ⟨8964687586675796753045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95623334257875165365813 8964687586675796753045)
                  ·
                    rfl

theorem cell21_39282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_39282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39282 prefixEnd_39282 := by exact prefixLift 39282
  have htrace : WordTrace (prefixWord ++ tailWord_39282) baseStart_39282 baseEnd_39282 := by
    simpa [prefixWord, tailWord_39282, baseEnd_39282] using wordTrace_append hprefix tailTrace_39282
  have hstable : (prefixWord ++ tailWord_39282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39282).length < 2 ^ (prefixWord ++ tailWord_39282).sum := by decide
  have hdescent : baseEnd_39282 < baseStart_39282 := by decide
  rcases family_descends (prefixWord ++ tailWord_39282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39386 : List Nat := [3, 1, 1, 2, 3, 1, 10]
def baseStart_39386 : Nat := 118140960795 + 39386 * 2 ^ 59
def prefixEnd_39386 : Nat := 4983230072969 + 3 ^ 40 * 39386 * 2
def baseEnd_39386 : Nat := 998713533732747446611

theorem tailTrace_39386 : CollatzResearch.WordTrace tailWord_39386 prefixEnd_39386 998713533732747446611 := by
  unfold tailWord_39386
  simp only [CollatzResearch.WordTrace]
  refine ⟨359131358829680859594503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 957683623545815625585341 359131358829680859594503)
  ·
    refine ⟨538697038244521289391755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 359131358829680859594503 538697038244521289391755)
    ·
      refine ⟨808045557366781934087633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 538697038244521289391755 808045557366781934087633)
      ·
        refine ⟨606034168025086450565725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 808045557366781934087633 606034168025086450565725)
        ·
          refine ⟨227262813009407418962147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 606034168025086450565725 227262813009407418962147)
          ·
            refine ⟨340894219514111128443221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227262813009407418962147 340894219514111128443221)
            ·
              refine ⟨998713533732747446611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 340894219514111128443221 998713533732747446611)
              ·
                rfl

theorem cell21_39386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 10].length) (baseStart_39386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39386 prefixEnd_39386 := by exact prefixLift 39386
  have htrace : WordTrace (prefixWord ++ tailWord_39386) baseStart_39386 baseEnd_39386 := by
    simpa [prefixWord, tailWord_39386, baseEnd_39386] using wordTrace_append hprefix tailTrace_39386
  have hstable : (prefixWord ++ tailWord_39386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39386).length < 2 ^ (prefixWord ++ tailWord_39386).sum := by decide
  have hdescent : baseEnd_39386 < baseStart_39386 := by decide
  rcases family_descends (prefixWord ++ tailWord_39386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39406 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_39406 : Nat := 118140960795 + 39406 * 2 ^ 59
def prefixEnd_39406 : Nat := 4983230072969 + 3 ^ 40 * 39406 * 2
def baseEnd_39406 : Nat := 8992986076079136686125

theorem tailTrace_39406 : CollatzResearch.WordTrace tailWord_39406 prefixEnd_39406 8992986076079136686125 := by
  unfold tailWord_39406
  simp only [CollatzResearch.WordTrace]
  refine ⟨179656861905783356763259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 958169930164177902737381 179656861905783356763259)
  ·
    refine ⟨269485292858675035144889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179656861905783356763259 269485292858675035144889)
    ·
      refine ⟨202113969644006276358667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 269485292858675035144889 202113969644006276358667)
      ·
        refine ⟨303170954466009414538001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202113969644006276358667 303170954466009414538001)
        ·
          refine ⟨227378215849507060903501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303170954466009414538001 227378215849507060903501)
          ·
            refine ⟨85266830943565147838813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 227378215849507060903501 85266830943565147838813)
            ·
              refine ⟨31975061603836930439555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85266830943565147838813 31975061603836930439555)
              ·
                refine ⟨47962592405755395659333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31975061603836930439555 47962592405755395659333)
                ·
                  refine ⟨8992986076079136686125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47962592405755395659333 8992986076079136686125)
                  ·
                    rfl

theorem cell21_39406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_39406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39406 prefixEnd_39406 := by exact prefixLift 39406
  have htrace : WordTrace (prefixWord ++ tailWord_39406) baseStart_39406 baseEnd_39406 := by
    simpa [prefixWord, tailWord_39406, baseEnd_39406] using wordTrace_append hprefix tailTrace_39406
  have hstable : (prefixWord ++ tailWord_39406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39406).length < 2 ^ (prefixWord ++ tailWord_39406).sum := by decide
  have hdescent : baseEnd_39406 < baseStart_39406 := by decide
  rcases family_descends (prefixWord ++ tailWord_39406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39417 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 5]
def baseStart_39417 : Nat := 118140960795 + 39417 * 2 ^ 59
def prefixEnd_39417 : Nat := 4983230072969 + 3 ^ 40 * 39417 * 2
def baseEnd_39417 : Nat := 8995496425945562002769

theorem tailTrace_39417 : CollatzResearch.WordTrace tailWord_39417 prefixEnd_39417 8995496425945562002769 := by
  unfold tailWord_39417
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437656098206415732756505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 958437398804277155171003 1437656098206415732756505)
  ·
    refine ⟨1078242073654811799567379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1437656098206415732756505 1078242073654811799567379)
    ·
      refine ⟨1617363110482217699351069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078242073654811799567379 1617363110482217699351069)
      ·
        refine ⟨606511166430831637256651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1617363110482217699351069 606511166430831637256651)
        ·
          refine ⟨909766749646247455884977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606511166430831637256651 909766749646247455884977)
          ·
            refine ⟨682325062234685591913733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 909766749646247455884977 682325062234685591913733)
            ·
              refine ⟨127935949169003548483825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 682325062234685591913733 127935949169003548483825)
              ·
                refine ⟨95951961876752661362869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127935949169003548483825 95951961876752661362869)
                ·
                  refine ⟨8995496425945562002769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95951961876752661362869 8995496425945562002769)
                  ·
                    rfl

theorem cell21_39417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_39417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39417 prefixEnd_39417 := by exact prefixLift 39417
  have htrace : WordTrace (prefixWord ++ tailWord_39417) baseStart_39417 baseEnd_39417 := by
    simpa [prefixWord, tailWord_39417, baseEnd_39417] using wordTrace_append hprefix tailTrace_39417
  have hstable : (prefixWord ++ tailWord_39417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39417).length < 2 ^ (prefixWord ++ tailWord_39417).sum := by decide
  have hdescent : baseEnd_39417 < baseStart_39417 := by decide
  rcases family_descends (prefixWord ++ tailWord_39417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39426 : List Nat := [3, 4, 1, 2, 3, 1, 1, 3, 3]
def baseStart_39426 : Nat := 118140960795 + 39426 * 2 ^ 59
def prefixEnd_39426 : Nat := 4983230072969 + 3 ^ 40 * 39426 * 2
def baseEnd_39426 : Nat := 8997550348563546352751

theorem tailTrace_39426 : CollatzResearch.WordTrace tailWord_39426 prefixEnd_39426 8997550348563546352751 := by
  unfold tailWord_39426
  simp only [CollatzResearch.WordTrace]
  refine ⟨359496088793452567458533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 958656236782540179889421 359496088793452567458533)
  ·
    refine ⟨67405516648772356398475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 359496088793452567458533 67405516648772356398475)
    ·
      refine ⟨101108274973158534597713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67405516648772356398475 101108274973158534597713)
      ·
        refine ⟨75831206229868900948285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101108274973158534597713 75831206229868900948285)
        ·
          refine ⟨28436702336200837855607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75831206229868900948285 28436702336200837855607)
          ·
            refine ⟨42655053504301256783411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28436702336200837855607 42655053504301256783411)
            ·
              refine ⟨63982580256451885175117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42655053504301256783411 63982580256451885175117)
              ·
                refine ⟨23993467596169456940669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63982580256451885175117 23993467596169456940669)
                ·
                  refine ⟨8997550348563546352751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23993467596169456940669 8997550348563546352751)
                  ·
                    rfl

theorem cell21_39426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_39426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39426 prefixEnd_39426 := by exact prefixLift 39426
  have htrace : WordTrace (prefixWord ++ tailWord_39426) baseStart_39426 baseEnd_39426 := by
    simpa [prefixWord, tailWord_39426, baseEnd_39426] using wordTrace_append hprefix tailTrace_39426
  have hstable : (prefixWord ++ tailWord_39426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39426).length < 2 ^ (prefixWord ++ tailWord_39426).sum := by decide
  have hdescent : baseEnd_39426 < baseStart_39426 := by decide
  rcases family_descends (prefixWord ++ tailWord_39426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39437 : List Nat := [1, 7, 1, 1, 1, 3, 7]
def baseStart_39437 : Nat := 118140960795 + 39437 * 2 ^ 59
def prefixEnd_39437 : Nat := 4983230072969 + 3 ^ 40 * 39437 * 2
def baseEnd_39437 : Nat := 1000006744269996852155

theorem tailTrace_39437 : CollatzResearch.WordTrace tailWord_39437 prefixEnd_39437 1000006744269996852155 := by
  unfold tailWord_39437
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438385558133959148484565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 958923705422639432323043 1438385558133959148484565)
  ·
    refine ⟨33712161518764667542607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 1438385558133959148484565 33712161518764667542607)
    ·
      refine ⟨50568242278147001313911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33712161518764667542607 50568242278147001313911)
      ·
        refine ⟨75852363417220501970867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50568242278147001313911 75852363417220501970867)
        ·
          refine ⟨113778545125830752956301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75852363417220501970867 113778545125830752956301)
          ·
            refine ⟨42666954422186532358613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113778545125830752956301 42666954422186532358613)
            ·
              refine ⟨1000006744269996852155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 42666954422186532358613 1000006744269996852155)
              ·
                rfl

theorem cell21_39437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 7].length) (baseStart_39437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39437 prefixEnd_39437 := by exact prefixLift 39437
  have htrace : WordTrace (prefixWord ++ tailWord_39437) baseStart_39437 baseEnd_39437 := by
    simpa [prefixWord, tailWord_39437, baseEnd_39437] using wordTrace_append hprefix tailTrace_39437
  have hstable : (prefixWord ++ tailWord_39437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39437).length < 2 ^ (prefixWord ++ tailWord_39437).sum := by decide
  have hdescent : baseEnd_39437 < baseStart_39437 := by decide
  rcases family_descends (prefixWord ++ tailWord_39437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39448 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_39448 : Nat := 118140960795 + 39448 * 2 ^ 59
def prefixEnd_39448 : Nat := 4983230072969 + 3 ^ 40 * 39448 * 2
def baseEnd_39448 : Nat := 9002571048296396986039

theorem tailTrace_39448 : CollatzResearch.WordTrace tailWord_39448 prefixEnd_39448 9002571048296396986039 := by
  unfold tailWord_39448
  simp only [CollatzResearch.WordTrace]
  refine ⟨719393380547054013567499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 959191174062738684756665 719393380547054013567499)
  ·
    refine ⟨1079090070820581020351249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 719393380547054013567499 1079090070820581020351249)
    ·
      refine ⟨809317553115435765263437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1079090070820581020351249 809317553115435765263437)
      ·
        refine ⟨303494082418288411973789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 809317553115435765263437 303494082418288411973789)
        ·
          refine ⟨113810280906858154490171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 303494082418288411973789 113810280906858154490171)
          ·
            refine ⟨170715421360287231735257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113810280906858154490171 170715421360287231735257)
            ·
              refine ⟨128036566020215423801443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170715421360287231735257 128036566020215423801443)
              ·
                refine ⟨192054849030323135702165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128036566020215423801443 192054849030323135702165)
                ·
                  refine ⟨9002571048296396986039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 192054849030323135702165 9002571048296396986039)
                  ·
                    rfl

theorem cell21_39448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_39448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39448 prefixEnd_39448 := by exact prefixLift 39448
  have htrace : WordTrace (prefixWord ++ tailWord_39448) baseStart_39448 baseEnd_39448 := by
    simpa [prefixWord, tailWord_39448, baseEnd_39448] using wordTrace_append hprefix tailTrace_39448
  have hstable : (prefixWord ++ tailWord_39448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39448).length < 2 ^ (prefixWord ++ tailWord_39448).sum := by decide
  have hdescent : baseEnd_39448 < baseStart_39448 := by decide
  rcases family_descends (prefixWord ++ tailWord_39448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39524 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 4]
def baseStart_39524 : Nat := 118140960795 + 39524 * 2 ^ 59
def prefixEnd_39524 : Nat := 4983230072969 + 3 ^ 40 * 39524 * 2
def baseEnd_39524 : Nat := 9019915283737153719217

theorem tailTrace_39524 : CollatzResearch.WordTrace tailWord_39524 prefixEnd_39524 9019915283737153719217 := by
  unfold tailWord_39524
  simp only [CollatzResearch.WordTrace]
  refine ⟨720779354409386503450813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 961039139212515337934417 720779354409386503450813)
  ·
    refine ⟨270292257903519938794055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 720779354409386503450813 270292257903519938794055)
    ·
      refine ⟨405438386855279908191083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270292257903519938794055 405438386855279908191083)
      ·
        refine ⟨608157580282919862286625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405438386855279908191083 608157580282919862286625)
        ·
          refine ⟨456118185212189896714969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608157580282919862286625 456118185212189896714969)
          ·
            refine ⟨342088638909142422536227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456118185212189896714969 342088638909142422536227)
            ·
              refine ⟨513132958363713633804341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342088638909142422536227 513132958363713633804341)
              ·
                refine ⟨48106214846598153169157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 513132958363713633804341 48106214846598153169157)
                ·
                  refine ⟨9019915283737153719217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48106214846598153169157 9019915283737153719217)
                  ·
                    rfl

theorem cell21_39524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_39524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39524 prefixEnd_39524 := by exact prefixLift 39524
  have htrace : WordTrace (prefixWord ++ tailWord_39524) baseStart_39524 baseEnd_39524 := by
    simpa [prefixWord, tailWord_39524, baseEnd_39524] using wordTrace_append hprefix tailTrace_39524
  have hstable : (prefixWord ++ tailWord_39524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39524).length < 2 ^ (prefixWord ++ tailWord_39524).sum := by decide
  have hdescent : baseEnd_39524 < baseStart_39524 := by decide
  rcases family_descends (prefixWord ++ tailWord_39524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39603 : List Nat := [1, 1, 1, 2, 3, 6, 1, 3, 3]
def baseStart_39603 : Nat := 118140960795 + 39603 * 2 ^ 59
def prefixEnd_39603 : Nat := 4983230072969 + 3 ^ 40 * 39603 * 2
def baseEnd_39603 : Nat := 9037944160050571902389

theorem tailTrace_39603 : CollatzResearch.WordTrace tailWord_39603 prefixEnd_39603 9037944160050571902389 := by
  unfold tailWord_39603
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444440075532569499027463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 962960050355046332684975 1444440075532569499027463)
  ·
    refine ⟨2166660113298854248541195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1444440075532569499027463 2166660113298854248541195)
    ·
      refine ⟨3249990169948281372811793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166660113298854248541195 3249990169948281372811793)
      ·
        refine ⟨2437492627461211029608845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3249990169948281372811793 2437492627461211029608845)
        ·
          refine ⟨914059735297954136103317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2437492627461211029608845 914059735297954136103317)
          ·
            refine ⟨42846550092091600129843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 914059735297954136103317 42846550092091600129843)
            ·
              refine ⟨64269825138137400194765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42846550092091600129843 64269825138137400194765)
              ·
                refine ⟨24101184426801525073037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64269825138137400194765 24101184426801525073037)
                ·
                  refine ⟨9037944160050571902389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24101184426801525073037 9037944160050571902389)
                  ·
                    rfl

theorem cell21_39603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 3].length) (baseStart_39603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39603 prefixEnd_39603 := by exact prefixLift 39603
  have htrace : WordTrace (prefixWord ++ tailWord_39603) baseStart_39603 baseEnd_39603 := by
    simpa [prefixWord, tailWord_39603, baseEnd_39603] using wordTrace_append hprefix tailTrace_39603
  have hstable : (prefixWord ++ tailWord_39603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39603).length < 2 ^ (prefixWord ++ tailWord_39603).sum := by decide
  have hdescent : baseEnd_39603 < baseStart_39603 := by decide
  rcases family_descends (prefixWord ++ tailWord_39603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39620 : List Nat := [2, 3, 3, 1, 1, 3, 3, 2, 3]
def baseStart_39620 : Nat := 118140960795 + 39620 * 2 ^ 59
def prefixEnd_39620 : Nat := 4983230072969 + 3 ^ 40 * 39620 * 2
def baseEnd_39620 : Nat := 9041823791662320119021

theorem tailTrace_39620 : CollatzResearch.WordTrace tailWord_39620 prefixEnd_39620 9041823791662320119021 := by
  unfold tailWord_39620
  simp only [CollatzResearch.WordTrace]
  refine ⟨722530058235490701198157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 963373410980654268264209 722530058235490701198157)
  ·
    refine ⟨270948771838309012949309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 722530058235490701198157 270948771838309012949309)
    ·
      refine ⟨101605789439365879855991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270948771838309012949309 101605789439365879855991)
      ·
        refine ⟨152408684159048819783987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101605789439365879855991 152408684159048819783987)
        ·
          refine ⟨228613026238573229675981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152408684159048819783987 228613026238573229675981)
          ·
            refine ⟨85729884839464961128493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228613026238573229675981 85729884839464961128493)
            ·
              refine ⟨32148706814799360423185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85729884839464961128493 32148706814799360423185)
              ·
                refine ⟨24111530111099520317389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32148706814799360423185 24111530111099520317389)
                ·
                  refine ⟨9041823791662320119021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24111530111099520317389 9041823791662320119021)
                  ·
                    rfl

theorem cell21_39620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_39620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39620 prefixEnd_39620 := by exact prefixLift 39620
  have htrace : WordTrace (prefixWord ++ tailWord_39620) baseStart_39620 baseEnd_39620 := by
    simpa [prefixWord, tailWord_39620, baseEnd_39620] using wordTrace_append hprefix tailTrace_39620
  have hstable : (prefixWord ++ tailWord_39620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39620).length < 2 ^ (prefixWord ++ tailWord_39620).sum := by decide
  have hdescent : baseEnd_39620 < baseStart_39620 := by decide
  rcases family_descends (prefixWord ++ tailWord_39620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39676 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 4]
def baseStart_39676 : Nat := 118140960795 + 39676 * 2 ^ 59
def prefixEnd_39676 : Nat := 4983230072969 + 3 ^ 40 * 39676 * 2
def baseEnd_39676 : Nat := 9054603754618667185573

theorem tailTrace_39676 : CollatzResearch.WordTrace tailWord_39676 prefixEnd_39676 9054603754618667185573 := by
  unfold tailWord_39676
  simp only [CollatzResearch.WordTrace]
  refine ⟨723551302134051483217441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 964735069512068644289921 723551302134051483217441)
  ·
    refine ⟨542663476600538612413081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 723551302134051483217441 542663476600538612413081)
    ·
      refine ⟨406997607450403959309811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 542663476600538612413081 406997607450403959309811)
      ·
        refine ⟨610496411175605938964717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406997607450403959309811 610496411175605938964717)
        ·
          refine ⟨228936154190852227111769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 610496411175605938964717 228936154190852227111769)
          ·
            refine ⟨171702115643139170333827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228936154190852227111769 171702115643139170333827)
            ·
              refine ⟨257553173464708755500741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171702115643139170333827 257553173464708755500741)
              ·
                refine ⟨48291220024632891656389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257553173464708755500741 48291220024632891656389)
                ·
                  refine ⟨9054603754618667185573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48291220024632891656389 9054603754618667185573)
                  ·
                    rfl

theorem cell21_39676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_39676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39676 prefixEnd_39676 := by exact prefixLift 39676
  have htrace : WordTrace (prefixWord ++ tailWord_39676) baseStart_39676 baseEnd_39676 := by
    simpa [prefixWord, tailWord_39676, baseEnd_39676] using wordTrace_append hprefix tailTrace_39676
  have hstable : (prefixWord ++ tailWord_39676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39676).length < 2 ^ (prefixWord ++ tailWord_39676).sum := by decide
  have hdescent : baseEnd_39676 < baseStart_39676 := by decide
  rcases family_descends (prefixWord ++ tailWord_39676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39735 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 6]
def baseStart_39735 : Nat := 118140960795 + 39735 * 2 ^ 59
def prefixEnd_39735 : Nat := 4983230072969 + 3 ^ 40 * 39735 * 2
def baseEnd_39735 : Nat := 9068068358447675702119

theorem tailTrace_39735 : CollatzResearch.WordTrace tailWord_39735 prefixEnd_39735 9068068358447675702119 := by
  unfold tailWord_39735
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449254511054356042832659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 966169674036237361888439 1449254511054356042832659)
  ·
    refine ⟨2173881766581534064248989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1449254511054356042832659 2173881766581534064248989)
    ·
      refine ⟨815205662468075274093371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2173881766581534064248989 815205662468075274093371)
      ·
        refine ⟨1222808493702112911140057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815205662468075274093371 1222808493702112911140057)
        ·
          refine ⟨917106370276584683355043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1222808493702112911140057 917106370276584683355043)
          ·
            refine ⟨1375659555414877025032565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917106370276584683355043 1375659555414877025032565)
            ·
              refine ⟨128968083320144721096803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1375659555414877025032565 128968083320144721096803)
              ·
                refine ⟨193452124980217081645205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128968083320144721096803 193452124980217081645205)
                ·
                  refine ⟨9068068358447675702119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 193452124980217081645205 9068068358447675702119)
                  ·
                    rfl

theorem cell21_39735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_39735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39735 prefixEnd_39735 := by exact prefixLift 39735
  have htrace : WordTrace (prefixWord ++ tailWord_39735) baseStart_39735 baseEnd_39735 := by
    simpa [prefixWord, tailWord_39735, baseEnd_39735] using wordTrace_append hprefix tailTrace_39735
  have hstable : (prefixWord ++ tailWord_39735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39735).length < 2 ^ (prefixWord ++ tailWord_39735).sum := by decide
  have hdescent : baseEnd_39735 < baseStart_39735 := by decide
  rcases family_descends (prefixWord ++ tailWord_39735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39738 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_39738 : Nat := 118140960795 + 39738 * 2 ^ 59
def prefixEnd_39738 : Nat := 4983230072969 + 3 ^ 40 * 39738 * 2
def baseEnd_39738 : Nat := 9068752999320337152113

theorem tailTrace_39738 : CollatzResearch.WordTrace tailWord_39738 prefixEnd_39738 9068752999320337152113 := by
  unfold tailWord_39738
  simp only [CollatzResearch.WordTrace]
  refine ⟨362340982510871888797967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 966242620028991703461245 362340982510871888797967)
  ·
    refine ⟨543511473766307833196951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 362340982510871888797967 543511473766307833196951)
    ·
      refine ⟨815267210649461749795427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 543511473766307833196951 815267210649461749795427)
      ·
        refine ⟨1222900815974192624693141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815267210649461749795427 1222900815974192624693141)
        ·
          refine ⟨57323475748790279282491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1222900815974192624693141 57323475748790279282491)
          ·
            refine ⟨85985213623185418923737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57323475748790279282491 85985213623185418923737)
            ·
              refine ⟨64488910217389064192803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85985213623185418923737 64488910217389064192803)
              ·
                refine ⟨96733365326083596289205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64488910217389064192803 96733365326083596289205)
                ·
                  refine ⟨9068752999320337152113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96733365326083596289205 9068752999320337152113)
                  ·
                    rfl

theorem cell21_39738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_39738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39738 prefixEnd_39738 := by exact prefixLift 39738
  have htrace : WordTrace (prefixWord ++ tailWord_39738) baseStart_39738 baseEnd_39738 := by
    simpa [prefixWord, tailWord_39738, baseEnd_39738] using wordTrace_append hprefix tailTrace_39738
  have hstable : (prefixWord ++ tailWord_39738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39738).length < 2 ^ (prefixWord ++ tailWord_39738).sum := by decide
  have hdescent : baseEnd_39738 < baseStart_39738 := by decide
  rcases family_descends (prefixWord ++ tailWord_39738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39772 : List Nat := [2, 2, 4, 2, 1, 3, 1, 3, 3]
def baseStart_39772 : Nat := 118140960795 + 39772 * 2 ^ 59
def prefixEnd_39772 : Nat := 4983230072969 + 3 ^ 40 * 39772 * 2
def baseEnd_39772 : Nat := 9076512262543833585377

theorem tailTrace_39772 : CollatzResearch.WordTrace tailWord_39772 prefixEnd_39772 9076512262543833585377 := by
  unfold tailWord_39772
  simp only [CollatzResearch.WordTrace]
  refine ⟨725302005960155680964785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 967069341280207574619713 725302005960155680964785)
  ·
    refine ⟨543976504470116760723589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 725302005960155680964785 543976504470116760723589)
    ·
      refine ⟨101995594588146892635673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 543976504470116760723589 101995594588146892635673)
      ·
        refine ⟨76496695941110169476755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101995594588146892635673 76496695941110169476755)
        ·
          refine ⟨114745043911665254215133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76496695941110169476755 114745043911665254215133)
          ·
            refine ⟨43029391466874470330675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114745043911665254215133 43029391466874470330675)
            ·
              refine ⟨64544087200311705496013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43029391466874470330675 64544087200311705496013)
              ·
                refine ⟨24204032700116889561005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64544087200311705496013 24204032700116889561005)
                ·
                  refine ⟨9076512262543833585377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24204032700116889561005 9076512262543833585377)
                  ·
                    rfl

theorem cell21_39772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_39772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39772 prefixEnd_39772 := by exact prefixLift 39772
  have htrace : WordTrace (prefixWord ++ tailWord_39772) baseStart_39772 baseEnd_39772 := by
    simpa [prefixWord, tailWord_39772, baseEnd_39772] using wordTrace_append hprefix tailTrace_39772
  have hstable : (prefixWord ++ tailWord_39772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39772).length < 2 ^ (prefixWord ++ tailWord_39772).sum := by decide
  have hdescent : baseEnd_39772 < baseStart_39772 := by decide
  rcases family_descends (prefixWord ++ tailWord_39772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39842 : List Nat := [3, 3, 1, 2, 2, 10]
def baseStart_39842 : Nat := 118140960795 + 39842 * 2 ^ 59
def prefixEnd_39842 : Nat := 4983230072969 + 3 ^ 40 * 39842 * 2
def baseEnd_39842 : Nat := 336758785786639534021

theorem tailTrace_39842 : CollatzResearch.WordTrace tailWord_39842 prefixEnd_39842 336758785786639534021 := by
  unfold tailWord_39842
  simp only [CollatzResearch.WordTrace]
  refine ⟨363289280416678329244445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 968771414444475544651853 363289280416678329244445)
  ·
    refine ⟨136233480156254373466667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 363289280416678329244445 136233480156254373466667)
    ·
      refine ⟨204350220234381560200001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136233480156254373466667 204350220234381560200001)
      ·
        refine ⟨153262665175786170150001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204350220234381560200001 153262665175786170150001)
        ·
          refine ⟨114946998881839627612501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153262665175786170150001 114946998881839627612501)
          ·
            refine ⟨336758785786639534021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 114946998881839627612501 336758785786639534021)
            ·
              rfl

theorem cell21_39842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 10].length) (baseStart_39842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39842 prefixEnd_39842 := by exact prefixLift 39842
  have htrace : WordTrace (prefixWord ++ tailWord_39842) baseStart_39842 baseEnd_39842 := by
    simpa [prefixWord, tailWord_39842, baseEnd_39842] using wordTrace_append hprefix tailTrace_39842
  have hstable : (prefixWord ++ tailWord_39842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39842).length < 2 ^ (prefixWord ++ tailWord_39842).sum := by decide
  have hdescent : baseEnd_39842 < baseStart_39842 := by decide
  rcases family_descends (prefixWord ++ tailWord_39842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39921 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 4]
def baseStart_39921 : Nat := 118140960795 + 39921 * 2 ^ 59
def prefixEnd_39921 : Nat := 4983230072969 + 3 ^ 40 * 39921 * 2
def baseEnd_39921 : Nat := 9110516092552685601739

theorem tailTrace_39921 : CollatzResearch.WordTrace tailWord_39921 prefixEnd_39921 9110516092552685601739 := by
  unfold tailWord_39921
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456038488380509809103617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 970692325587006539402411 1456038488380509809103617)
  ·
    refine ⟨1092028866285382356827713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1456038488380509809103617 1092028866285382356827713)
    ·
      refine ⟨819021649714036767620785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1092028866285382356827713 819021649714036767620785)
      ·
        refine ⟨614266237285527575715589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 819021649714036767620785 614266237285527575715589)
        ·
          refine ⟨115174919491036420446673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 614266237285527575715589 115174919491036420446673)
          ·
            refine ⟨86381189618277315335005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115174919491036420446673 86381189618277315335005)
            ·
              refine ⟨32392946106853993250627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86381189618277315335005 32392946106853993250627)
              ·
                refine ⟨48589419160280989875941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32392946106853993250627 48589419160280989875941)
                ·
                  refine ⟨9110516092552685601739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48589419160280989875941 9110516092552685601739)
                  ·
                    rfl

theorem cell21_39921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_39921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_39921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_39921 prefixEnd_39921 := by exact prefixLift 39921
  have htrace : WordTrace (prefixWord ++ tailWord_39921) baseStart_39921 baseEnd_39921 := by
    simpa [prefixWord, tailWord_39921, baseEnd_39921] using wordTrace_append hprefix tailTrace_39921
  have hstable : (prefixWord ++ tailWord_39921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39921).length < 2 ^ (prefixWord ++ tailWord_39921).sum := by decide
  have hdescent : baseEnd_39921 < baseStart_39921 := by decide
  rcases family_descends (prefixWord ++ tailWord_39921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40146 : List Nat := [3, 2, 2, 2, 1, 1, 4, 6]
def baseStart_40146 : Nat := 118140960795 + 40146 * 2 ^ 59
def prefixEnd_40146 : Nat := 4983230072969 + 3 ^ 40 * 40146 * 2
def baseEnd_40146 : Nat := 3053954719334098117093

theorem tailTrace_40146 : CollatzResearch.WordTrace tailWord_40146 prefixEnd_40146 3053954719334098117093 := by
  unfold tailWord_40146
  simp only [CollatzResearch.WordTrace]
  refine ⟨366061228141343309011073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 976163275043582157362861 366061228141343309011073)
  ·
    refine ⟨274545921106007481758305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 366061228141343309011073 274545921106007481758305)
    ·
      refine ⟨205909440829505611318729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274545921106007481758305 205909440829505611318729)
      ·
        refine ⟨154432080622129208489047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205909440829505611318729 154432080622129208489047)
        ·
          refine ⟨231648120933193812733571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154432080622129208489047 231648120933193812733571)
          ·
            refine ⟨347472181399790719100357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231648120933193812733571 347472181399790719100357)
            ·
              refine ⟨65151034012460759831317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 347472181399790719100357 65151034012460759831317)
              ·
                refine ⟨3053954719334098117093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65151034012460759831317 3053954719334098117093)
                ·
                  rfl

theorem cell21_40146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_40146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40146 prefixEnd_40146 := by exact prefixLift 40146
  have htrace : WordTrace (prefixWord ++ tailWord_40146) baseStart_40146 baseEnd_40146 := by
    simpa [prefixWord, tailWord_40146, baseEnd_40146] using wordTrace_append hprefix tailTrace_40146
  have hstable : (prefixWord ++ tailWord_40146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40146).length < 2 ^ (prefixWord ++ tailWord_40146).sum := by decide
  have hdescent : baseEnd_40146 < baseStart_40146 := by decide
  rcases family_descends (prefixWord ++ tailWord_40146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40149 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 4]
def baseStart_40149 : Nat := 118140960795 + 40149 * 2 ^ 59
def prefixEnd_40149 : Nat := 4983230072969 + 3 ^ 40 * 40149 * 2
def baseEnd_40149 : Nat := 9162548798874955801273

theorem tailTrace_40149 : CollatzResearch.WordTrace tailWord_40149 prefixEnd_40149 9162548798874955801273 := by
  unfold tailWord_40149
  simp only [CollatzResearch.WordTrace]
  refine ⟨1464354331554504748403501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 976236221036336498935667 1464354331554504748403501)
  ·
    refine ⟨549132874332939280651313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1464354331554504748403501 549132874332939280651313)
    ·
      refine ⟨411849655749704460488485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 549132874332939280651313 411849655749704460488485)
      ·
        refine ⟨77221810453069586341591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 411849655749704460488485 77221810453069586341591)
        ·
          refine ⟨115832715679604379512387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77221810453069586341591 115832715679604379512387)
          ·
            refine ⟨173749073519406569268581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115832715679604379512387 173749073519406569268581)
            ·
              refine ⟨32577951284888731737859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173749073519406569268581 32577951284888731737859)
              ·
                refine ⟨48866926927333097606789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32577951284888731737859 48866926927333097606789)
                ·
                  refine ⟨9162548798874955801273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48866926927333097606789 9162548798874955801273)
                  ·
                    rfl

theorem cell21_40149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_40149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40149 prefixEnd_40149 := by exact prefixLift 40149
  have htrace : WordTrace (prefixWord ++ tailWord_40149) baseStart_40149 baseEnd_40149 := by
    simpa [prefixWord, tailWord_40149, baseEnd_40149] using wordTrace_append hprefix tailTrace_40149
  have hstable : (prefixWord ++ tailWord_40149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40149).length < 2 ^ (prefixWord ++ tailWord_40149).sum := by decide
  have hdescent : baseEnd_40149 < baseStart_40149 := by decide
  rcases family_descends (prefixWord ++ tailWord_40149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40177 : List Nat := [1, 2, 2, 2, 2, 1, 1, 7, 3]
def baseStart_40177 : Nat := 118140960795 + 40177 * 2 ^ 59
def prefixEnd_40177 : Nat := 4983230072969 + 3 ^ 40 * 40177 * 2
def baseEnd_40177 : Nat := 9168938780353129334549

theorem tailTrace_40177 : CollatzResearch.WordTrace tailWord_40177 prefixEnd_40177 9168938780353129334549 := by
  unfold tailWord_40177
  simp only [CollatzResearch.WordTrace]
  refine ⟨1465375575453065530422785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 976917050302043686948523 1465375575453065530422785)
  ·
    refine ⟨1099031681589799147817089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1465375575453065530422785 1099031681589799147817089)
    ·
      refine ⟨824273761192349360862817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1099031681589799147817089 824273761192349360862817)
      ·
        refine ⟨618205320894262020647113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 824273761192349360862817 618205320894262020647113)
        ·
          refine ⟨463653990670696515485335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618205320894262020647113 463653990670696515485335)
          ·
            refine ⟨695480986006044773228003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463653990670696515485335 695480986006044773228003)
            ·
              refine ⟨1043221479009067159842005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695480986006044773228003 1043221479009067159842005)
              ·
                refine ⟨24450503414275011558797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1043221479009067159842005 24450503414275011558797)
                ·
                  refine ⟨9168938780353129334549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24450503414275011558797 9168938780353129334549)
                  ·
                    rfl

theorem cell21_40177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 3].length) (baseStart_40177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40177 prefixEnd_40177 := by exact prefixLift 40177
  have htrace : WordTrace (prefixWord ++ tailWord_40177) baseStart_40177 baseEnd_40177 := by
    simpa [prefixWord, tailWord_40177, baseEnd_40177] using wordTrace_append hprefix tailTrace_40177
  have hstable : (prefixWord ++ tailWord_40177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40177).length < 2 ^ (prefixWord ++ tailWord_40177).sum := by decide
  have hdescent : baseEnd_40177 < baseStart_40177 := by decide
  rcases family_descends (prefixWord ++ tailWord_40177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40180 : List Nat := [2, 6, 1, 2, 1, 9]
def baseStart_40180 : Nat := 118140960795 + 40180 * 2 ^ 59
def prefixEnd_40180 : Nat := 4983230072969 + 3 ^ 40 * 40180 * 2
def baseEnd_40180 : Nat := 339615682267621880909

theorem tailTrace_40180 : CollatzResearch.WordTrace tailWord_40180 prefixEnd_40180 339615682267621880909 := by
  unfold tailWord_40180
  simp only [CollatzResearch.WordTrace]
  refine ⟨732742497221098521390997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 976989996294798028521329 732742497221098521390997)
  ·
    refine ⟨34347304557238993190203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 732742497221098521390997 34347304557238993190203)
    ·
      refine ⟨51520956835858489785305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34347304557238993190203 51520956835858489785305)
      ·
        refine ⟨38640717626893867338979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51520956835858489785305 38640717626893867338979)
        ·
          refine ⟨57961076440340801008469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38640717626893867338979 57961076440340801008469)
          ·
            refine ⟨339615682267621880909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 57961076440340801008469 339615682267621880909)
            ·
              rfl

theorem cell21_40180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 9].length) (baseStart_40180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40180 prefixEnd_40180 := by exact prefixLift 40180
  have htrace : WordTrace (prefixWord ++ tailWord_40180) baseStart_40180 baseEnd_40180 := by
    simpa [prefixWord, tailWord_40180, baseEnd_40180] using wordTrace_append hprefix tailTrace_40180
  have hstable : (prefixWord ++ tailWord_40180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40180).length < 2 ^ (prefixWord ++ tailWord_40180).sum := by decide
  have hdescent : baseEnd_40180 < baseStart_40180 := by decide
  rcases family_descends (prefixWord ++ tailWord_40180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40191 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 4]
def baseStart_40191 : Nat := 118140960795 + 40191 * 2 ^ 59
def prefixEnd_40191 : Nat := 4983230072969 + 3 ^ 40 * 40191 * 2
def baseEnd_40191 : Nat := 9172133771092216101187

theorem tailTrace_40191 : CollatzResearch.WordTrace tailWord_40191 prefixEnd_40191 9172133771092216101187 := by
  unfold tailWord_40191
  simp only [CollatzResearch.WordTrace]
  refine ⟨1465886197402345921432427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 977257464934897280954951 1465886197402345921432427)
  ·
    refine ⟨2198829296103518882148641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1465886197402345921432427 2198829296103518882148641)
    ·
      refine ⟨1649121972077639161611481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2198829296103518882148641 1649121972077639161611481)
      ·
        refine ⟨1236841479058229371208611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1649121972077639161611481 1236841479058229371208611)
        ·
          refine ⟨1855262218587344056812917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236841479058229371208611 1855262218587344056812917)
          ·
            refine ⟨173930832992563505326211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1855262218587344056812917 173930832992563505326211)
            ·
              refine ⟨260896249488845257989317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173930832992563505326211 260896249488845257989317)
              ·
                refine ⟨48918046779158485872997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260896249488845257989317 48918046779158485872997)
                ·
                  refine ⟨9172133771092216101187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48918046779158485872997 9172133771092216101187)
                  ·
                    rfl

theorem cell21_40191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 4].length) (baseStart_40191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40191 prefixEnd_40191 := by exact prefixLift 40191
  have htrace : WordTrace (prefixWord ++ tailWord_40191) baseStart_40191 baseEnd_40191 := by
    simpa [prefixWord, tailWord_40191, baseEnd_40191] using wordTrace_append hprefix tailTrace_40191
  have hstable : (prefixWord ++ tailWord_40191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40191).length < 2 ^ (prefixWord ++ tailWord_40191).sum := by decide
  have hdescent : baseEnd_40191 < baseStart_40191 := by decide
  rcases family_descends (prefixWord ++ tailWord_40191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40318 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_40318 : Nat := 118140960795 + 40318 * 2 ^ 59
def prefixEnd_40318 : Nat := 4983230072969 + 3 ^ 40 * 40318 * 2
def baseEnd_40318 : Nat := 9201116901368217484261

theorem tailTrace_40318 : CollatzResearch.WordTrace tailWord_40318 prefixEnd_40318 9201116901368217484261 := by
  unfold tailWord_40318
  simp only [CollatzResearch.WordTrace]
  refine ⟨183814783492780826413201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 980345511961497740870405 183814783492780826413201)
  ·
    refine ⟨137861087619585619809901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183814783492780826413201 137861087619585619809901)
    ·
      refine ⟨51697907857344607428713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137861087619585619809901 51697907857344607428713)
      ·
        refine ⟨38773430893008455571535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51697907857344607428713 38773430893008455571535)
        ·
          refine ⟨58160146339512683357303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38773430893008455571535 58160146339512683357303)
          ·
            refine ⟨87240219509269025035955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58160146339512683357303 87240219509269025035955)
            ·
              refine ⟨130860329263903537553933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87240219509269025035955 130860329263903537553933)
              ·
                refine ⟨49072623473963826582725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130860329263903537553933 49072623473963826582725)
                ·
                  refine ⟨9201116901368217484261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49072623473963826582725 9201116901368217484261)
                  ·
                    rfl

theorem cell21_40318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_40318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40318 prefixEnd_40318 := by exact prefixLift 40318
  have htrace : WordTrace (prefixWord ++ tailWord_40318) baseStart_40318 baseEnd_40318 := by
    simpa [prefixWord, tailWord_40318, baseEnd_40318] using wordTrace_append hprefix tailTrace_40318
  have hstable : (prefixWord ++ tailWord_40318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40318).length < 2 ^ (prefixWord ++ tailWord_40318).sum := by decide
  have hdescent : baseEnd_40318 < baseStart_40318 := by decide
  rcases family_descends (prefixWord ++ tailWord_40318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40371 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 9]
def baseStart_40371 : Nat := 118140960795 + 40371 * 2 ^ 59
def prefixEnd_40371 : Nat := 4983230072969 + 3 ^ 40 * 40371 * 2
def baseEnd_40371 : Nat := 9213212223451903100819

theorem tailTrace_40371 : CollatzResearch.WordTrace tailWord_40371 prefixEnd_40371 9213212223451903100819 := by
  unfold tailWord_40371
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472451336750236662984967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 981634224500157775323311 1472451336750236662984967)
  ·
    refine ⟨2208677005125354994477451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1472451336750236662984967 2208677005125354994477451)
    ·
      refine ⟨3313015507688032491716177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2208677005125354994477451 3313015507688032491716177)
      ·
        refine ⟨2484761630766024368787133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3313015507688032491716177 2484761630766024368787133)
        ·
          refine ⟨931785611537259138295175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2484761630766024368787133 931785611537259138295175)
          ·
            refine ⟨1397678417305888707442763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931785611537259138295175 1397678417305888707442763)
            ·
              refine ⟨2096517625958833061164145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397678417305888707442763 2096517625958833061164145)
              ·
                refine ⟨1572388219469124795873109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2096517625958833061164145 1572388219469124795873109)
                ·
                  refine ⟨9213212223451903100819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1572388219469124795873109 9213212223451903100819)
                  ·
                    rfl

theorem cell21_40371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_40371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40371 prefixEnd_40371 := by exact prefixLift 40371
  have htrace : WordTrace (prefixWord ++ tailWord_40371) baseStart_40371 baseEnd_40371 := by
    simpa [prefixWord, tailWord_40371, baseEnd_40371] using wordTrace_append hprefix tailTrace_40371
  have hstable : (prefixWord ++ tailWord_40371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40371).length < 2 ^ (prefixWord ++ tailWord_40371).sum := by decide
  have hdescent : baseEnd_40371 < baseStart_40371 := by decide
  rcases family_descends (prefixWord ++ tailWord_40371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40419 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 6]
def baseStart_40419 : Nat := 118140960795 + 40419 * 2 ^ 59
def prefixEnd_40419 : Nat := 4983230072969 + 3 ^ 40 * 40419 * 2
def baseEnd_40419 : Nat := 9224166477414486300721

theorem tailTrace_40419 : CollatzResearch.WordTrace tailWord_40419 prefixEnd_40419 9224166477414486300721 := by
  unfold tailWord_40419
  simp only [CollatzResearch.WordTrace]
  refine ⟨1474202040576340860732311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 982801360384227240488207 1474202040576340860732311)
  ·
    refine ⟨2211303060864511291098467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1474202040576340860732311 2211303060864511291098467)
    ·
      refine ⟨3316954591296766936647701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2211303060864511291098467 3316954591296766936647701)
      ·
        refine ⟨155482246467035950155361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3316954591296766936647701 155482246467035950155361)
        ·
          refine ⟨116611684850276962616521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155482246467035950155361 116611684850276962616521)
          ·
            refine ⟨87458763637707721962391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116611684850276962616521 87458763637707721962391)
            ·
              refine ⟨131188145456561582943587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87458763637707721962391 131188145456561582943587)
              ·
                refine ⟨196782218184842374415381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131188145456561582943587 196782218184842374415381)
                ·
                  refine ⟨9224166477414486300721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 196782218184842374415381 9224166477414486300721)
                  ·
                    rfl

theorem cell21_40419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 6].length) (baseStart_40419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40419 prefixEnd_40419 := by exact prefixLift 40419
  have htrace : WordTrace (prefixWord ++ tailWord_40419) baseStart_40419 baseEnd_40419 := by
    simpa [prefixWord, tailWord_40419, baseEnd_40419] using wordTrace_append hprefix tailTrace_40419
  have hstable : (prefixWord ++ tailWord_40419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40419).length < 2 ^ (prefixWord ++ tailWord_40419).sum := by decide
  have hdescent : baseEnd_40419 < baseStart_40419 := by decide
  rcases family_descends (prefixWord ++ tailWord_40419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40447 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 7]
def baseStart_40447 : Nat := 118140960795 + 40447 * 2 ^ 59
def prefixEnd_40447 : Nat := 4983230072969 + 3 ^ 40 * 40447 * 2
def baseEnd_40447 : Nat := 9230556458892659833997

theorem tailTrace_40447 : CollatzResearch.WordTrace tailWord_40447 prefixEnd_40447 9230556458892659833997 := by
  unfold tailWord_40447
  simp only [CollatzResearch.WordTrace]
  refine ⟨1475223284474901642751595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 983482189649934428501063 1475223284474901642751595)
  ·
    refine ⟨2212834926712352464127393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1475223284474901642751595 2212834926712352464127393)
    ·
      refine ⟨1659626195034264348095545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2212834926712352464127393 1659626195034264348095545)
      ·
        refine ⟨1244719646275698261071659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1659626195034264348095545 1244719646275698261071659)
        ·
          refine ⟨1867079469413547391607489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244719646275698261071659 1867079469413547391607489)
          ·
            refine ⟨1400309602060160543705617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1867079469413547391607489 1400309602060160543705617)
            ·
              refine ⟨1050232201545120407779213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1400309602060160543705617 1050232201545120407779213)
              ·
                refine ⟨393837075579420152917205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1050232201545120407779213 393837075579420152917205)
                ·
                  refine ⟨9230556458892659833997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 393837075579420152917205 9230556458892659833997)
                  ·
                    rfl

theorem cell21_40447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_40447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40447 prefixEnd_40447 := by exact prefixLift 40447
  have htrace : WordTrace (prefixWord ++ tailWord_40447) baseStart_40447 baseEnd_40447 := by
    simpa [prefixWord, tailWord_40447, baseEnd_40447] using wordTrace_append hprefix tailTrace_40447
  have hstable : (prefixWord ++ tailWord_40447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40447).length < 2 ^ (prefixWord ++ tailWord_40447).sum := by decide
  have hdescent : baseEnd_40447 < baseStart_40447 := by decide
  rcases family_descends (prefixWord ++ tailWord_40447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40481 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 5]
def baseStart_40481 : Nat := 118140960795 + 40481 * 2 ^ 59
def prefixEnd_40481 : Nat := 4983230072969 + 3 ^ 40 * 40481 * 2
def baseEnd_40481 : Nat := 9238315722116156267261

theorem tailTrace_40481 : CollatzResearch.WordTrace tailWord_40481 prefixEnd_40481 9238315722116156267261 := by
  unfold tailWord_40481
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476463366351725449489297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 984308910901150299659531 1476463366351725449489297)
  ·
    refine ⟨1107347524763794087116973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1476463366351725449489297 1107347524763794087116973)
    ·
      refine ⟨415255321786422782668865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1107347524763794087116973 415255321786422782668865)
      ·
        refine ⟨311441491339817087001649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415255321786422782668865 311441491339817087001649)
        ·
          refine ⟨233581118504862815251237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311441491339817087001649 233581118504862815251237)
          ·
            refine ⟨43796459719661777859607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 233581118504862815251237 43796459719661777859607)
            ·
              refine ⟨65694689579492666789411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43796459719661777859607 65694689579492666789411)
              ·
                refine ⟨98542034369239000184117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65694689579492666789411 98542034369239000184117)
                ·
                  refine ⟨9238315722116156267261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98542034369239000184117 9238315722116156267261)
                  ·
                    rfl

theorem cell21_40481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_40481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40481 prefixEnd_40481 := by exact prefixLift 40481
  have htrace : WordTrace (prefixWord ++ tailWord_40481) baseStart_40481 baseEnd_40481 := by
    simpa [prefixWord, tailWord_40481, baseEnd_40481] using wordTrace_append hprefix tailTrace_40481
  have hstable : (prefixWord ++ tailWord_40481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40481).length < 2 ^ (prefixWord ++ tailWord_40481).sum := by decide
  have hdescent : baseEnd_40481 < baseStart_40481 := by decide
  rcases family_descends (prefixWord ++ tailWord_40481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40557 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 5]
def baseStart_40557 : Nat := 118140960795 + 40557 * 2 ^ 59
def prefixEnd_40557 : Nat := 4983230072969 + 3 ^ 40 * 40557 * 2
def baseEnd_40557 : Nat := 9255659957556913000439

theorem tailTrace_40557 : CollatzResearch.WordTrace tailWord_40557 prefixEnd_40557 9255659957556913000439 := by
  unfold tailWord_40557
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479235314076390429255925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 986156876050926952837283 1479235314076390429255925)
  ·
    refine ⟨138678310694661602742743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1479235314076390429255925 138678310694661602742743)
    ·
      refine ⟨208017466041992404114115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138678310694661602742743 208017466041992404114115)
      ·
        refine ⟨312026199062988606171173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208017466041992404114115 312026199062988606171173)
        ·
          refine ⟨58504912324310363657095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312026199062988606171173 58504912324310363657095)
          ·
            refine ⟨87757368486465545485643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58504912324310363657095 87757368486465545485643)
            ·
              refine ⟨131636052729698318228465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87757368486465545485643 131636052729698318228465)
              ·
                refine ⟨98727039547273738671349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131636052729698318228465 98727039547273738671349)
                ·
                  refine ⟨9255659957556913000439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98727039547273738671349 9255659957556913000439)
                  ·
                    rfl

theorem cell21_40557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_40557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40557 prefixEnd_40557 := by exact prefixLift 40557
  have htrace : WordTrace (prefixWord ++ tailWord_40557) baseStart_40557 baseEnd_40557 := by
    simpa [prefixWord, tailWord_40557, baseEnd_40557] using wordTrace_append hprefix tailTrace_40557
  have hstable : (prefixWord ++ tailWord_40557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40557).length < 2 ^ (prefixWord ++ tailWord_40557).sum := by decide
  have hdescent : baseEnd_40557 < baseStart_40557 := by decide
  rcases family_descends (prefixWord ++ tailWord_40557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40633 : List Nat := [1, 2, 1, 4, 1, 1, 5, 3, 3]
def baseStart_40633 : Nat := 118140960795 + 40633 * 2 ^ 59
def prefixEnd_40633 : Nat := 4983230072969 + 3 ^ 40 * 40633 * 2
def baseEnd_40633 : Nat := 9273004192997669733617

theorem tailTrace_40633 : CollatzResearch.WordTrace tailWord_40633 prefixEnd_40633 9273004192997669733617 := by
  unfold tailWord_40633
  simp only [CollatzResearch.WordTrace]
  refine ⟨1482007261801055409022553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 988004841200703606015035 1482007261801055409022553)
  ·
    refine ⟨1111505446350791556766915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1482007261801055409022553 1111505446350791556766915)
    ·
      refine ⟨1667258169526187335150373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1111505446350791556766915 1667258169526187335150373)
      ·
        refine ⟨312610906786160125340695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1667258169526187335150373 312610906786160125340695)
        ·
          refine ⟨468916360179240188011043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312610906786160125340695 468916360179240188011043)
          ·
            refine ⟨703374540268860282016565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468916360179240188011043 703374540268860282016565)
            ·
              refine ⟨65941363150205651439053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 703374540268860282016565 65941363150205651439053)
              ·
                refine ⟨24728011181327119289645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65941363150205651439053 24728011181327119289645)
                ·
                  refine ⟨9273004192997669733617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24728011181327119289645 9273004192997669733617)
                  ·
                    rfl

theorem cell21_40633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 3].length) (baseStart_40633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40633 prefixEnd_40633 := by exact prefixLift 40633
  have htrace : WordTrace (prefixWord ++ tailWord_40633) baseStart_40633 baseEnd_40633 := by
    simpa [prefixWord, tailWord_40633, baseEnd_40633] using wordTrace_append hprefix tailTrace_40633
  have hstable : (prefixWord ++ tailWord_40633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40633).length < 2 ^ (prefixWord ++ tailWord_40633).sum := by decide
  have hdescent : baseEnd_40633 < baseStart_40633 := by decide
  rcases family_descends (prefixWord ++ tailWord_40633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40650 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 5]
def baseStart_40650 : Nat := 118140960795 + 40650 * 2 ^ 59
def prefixEnd_40650 : Nat := 4983230072969 + 3 ^ 40 * 40650 * 2
def baseEnd_40650 : Nat := 9276883824609417950249

theorem tailTrace_40650 : CollatzResearch.WordTrace tailWord_40650 prefixEnd_40650 9276883824609417950249 := by
  unfold tailWord_40650
  simp only [CollatzResearch.WordTrace]
  refine ⟨370656825684866828097851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 988418201826311541594269 370656825684866828097851)
  ·
    refine ⟨555985238527300242146777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 370656825684866828097851 555985238527300242146777)
    ·
      refine ⟨416988928895475181610083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 555985238527300242146777 416988928895475181610083)
      ·
        refine ⟨625483393343212772415125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416988928895475181610083 625483393343212772415125)
        ·
          refine ⟨29319534062963098706959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 625483393343212772415125 29319534062963098706959)
          ·
            refine ⟨43979301094444648060439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29319534062963098706959 43979301094444648060439)
            ·
              refine ⟨65968951641666972090659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43979301094444648060439 65968951641666972090659)
              ·
                refine ⟨98953427462500458135989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65968951641666972090659 98953427462500458135989)
                ·
                  refine ⟨9276883824609417950249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98953427462500458135989 9276883824609417950249)
                  ·
                    rfl

theorem cell21_40650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_40650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40650 prefixEnd_40650 := by exact prefixLift 40650
  have htrace : WordTrace (prefixWord ++ tailWord_40650) baseStart_40650 baseEnd_40650 := by
    simpa [prefixWord, tailWord_40650, baseEnd_40650] using wordTrace_append hprefix tailTrace_40650
  have hstable : (prefixWord ++ tailWord_40650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40650).length < 2 ^ (prefixWord ++ tailWord_40650).sum := by decide
  have hdescent : baseEnd_40650 < baseStart_40650 := by decide
  rcases family_descends (prefixWord ++ tailWord_40650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40757 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 4]
def baseStart_40757 : Nat := 118140960795 + 40757 * 2 ^ 59
def prefixEnd_40757 : Nat := 4983230072969 + 3 ^ 40 * 40757 * 2
def baseEnd_40757 : Nat := 9301302682401009666697

theorem tailTrace_40757 : CollatzResearch.WordTrace tailWord_40757 prefixEnd_40757 9301302682401009666697 := by
  unfold tailWord_40757
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486529913351824586536525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 991019942234549724357683 1486529913351824586536525)
  ·
    refine ⟨557448717506934219951197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1486529913351824586536525 557448717506934219951197)
    ·
      refine ⟨209043269065100332481699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 557448717506934219951197 209043269065100332481699)
      ·
        refine ⟨313564903597650498722549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209043269065100332481699 313564903597650498722549)
        ·
          refine ⟨29396709712279734255239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 313564903597650498722549 29396709712279734255239)
          ·
            refine ⟨44095064568419601382859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29396709712279734255239 44095064568419601382859)
            ·
              refine ⟨66142596852629402074289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44095064568419601382859 66142596852629402074289)
              ·
                refine ⟨49606947639472051555717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66142596852629402074289 49606947639472051555717)
                ·
                  refine ⟨9301302682401009666697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49606947639472051555717 9301302682401009666697)
                  ·
                    rfl

theorem cell21_40757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_40757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40757 prefixEnd_40757 := by exact prefixLift 40757
  have htrace : WordTrace (prefixWord ++ tailWord_40757) baseStart_40757 baseEnd_40757 := by
    simpa [prefixWord, tailWord_40757, baseEnd_40757] using wordTrace_append hprefix tailTrace_40757
  have hstable : (prefixWord ++ tailWord_40757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40757).length < 2 ^ (prefixWord ++ tailWord_40757).sum := by decide
  have hdescent : baseEnd_40757 < baseStart_40757 := by decide
  rcases family_descends (prefixWord ++ tailWord_40757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40774 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_40774 : Nat := 118140960795 + 40774 * 2 ^ 59
def prefixEnd_40774 : Nat := 4983230072969 + 3 ^ 40 * 40774 * 2
def baseEnd_40774 : Nat := 9305182314012757883329

theorem tailTrace_40774 : CollatzResearch.WordTrace tailWord_40774 prefixEnd_40774 9305182314012757883329 := by
  unfold tailWord_40774
  simp only [CollatzResearch.WordTrace]
  refine ⟨46473436071569890309543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 991433302860157659936917 46473436071569890309543)
  ·
    refine ⟨69710154107354835464315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46473436071569890309543 69710154107354835464315)
    ·
      refine ⟨104565231161032253196473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69710154107354835464315 104565231161032253196473)
      ·
        refine ⟨78423923370774189897355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104565231161032253196473 78423923370774189897355)
        ·
          refine ⟨117635885056161284846033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78423923370774189897355 117635885056161284846033)
          ·
            refine ⟨88226913792120963634525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117635885056161284846033 88226913792120963634525)
            ·
              refine ⟨33085092672045361362947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88226913792120963634525 33085092672045361362947)
              ·
                refine ⟨49627639008068042044421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33085092672045361362947 49627639008068042044421)
                ·
                  refine ⟨9305182314012757883329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49627639008068042044421 9305182314012757883329)
                  ·
                    rfl

theorem cell21_40774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_40774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40774 prefixEnd_40774 := by exact prefixLift 40774
  have htrace : WordTrace (prefixWord ++ tailWord_40774) baseStart_40774 baseEnd_40774 := by
    simpa [prefixWord, tailWord_40774, baseEnd_40774] using wordTrace_append hprefix tailTrace_40774
  have hstable : (prefixWord ++ tailWord_40774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40774).length < 2 ^ (prefixWord ++ tailWord_40774).sum := by decide
  have hdescent : baseEnd_40774 < baseStart_40774 := by decide
  rcases family_descends (prefixWord ++ tailWord_40774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40802 : List Nat := [3, 3, 2, 1, 2, 1, 3, 3, 3]
def baseStart_40802 : Nat := 118140960795 + 40802 * 2 ^ 59
def prefixEnd_40802 : Nat := 4983230072969 + 3 ^ 40 * 40802 * 2
def baseEnd_40802 : Nat := 9311572295490931416605

theorem tailTrace_40802 : CollatzResearch.WordTrace tailWord_40802 prefixEnd_40802 9311572295490931416605 := by
  unfold tailWord_40802
  simp only [CollatzResearch.WordTrace]
  refine ⟨372042799547199317981165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 992114132125864847949773 372042799547199317981165)
  ·
    refine ⟨139516049830199744242937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 372042799547199317981165 139516049830199744242937)
    ·
      refine ⟨104637037372649808182203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139516049830199744242937 104637037372649808182203)
      ·
        refine ⟨156955556058974712273305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104637037372649808182203 156955556058974712273305)
        ·
          refine ⟨117716667044231034204979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156955556058974712273305 117716667044231034204979)
          ·
            refine ⟨176575000566346551307469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117716667044231034204979 176575000566346551307469)
            ·
              refine ⟨66215625212379956740301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176575000566346551307469 66215625212379956740301)
              ·
                refine ⟨24830859454642483777613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66215625212379956740301 24830859454642483777613)
                ·
                  refine ⟨9311572295490931416605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24830859454642483777613 9311572295490931416605)
                  ·
                    rfl

theorem cell21_40802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_40802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40802 prefixEnd_40802 := by exact prefixLift 40802
  have htrace : WordTrace (prefixWord ++ tailWord_40802) baseStart_40802 baseEnd_40802 := by
    simpa [prefixWord, tailWord_40802, baseEnd_40802] using wordTrace_append hprefix tailTrace_40802
  have hstable : (prefixWord ++ tailWord_40802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40802).length < 2 ^ (prefixWord ++ tailWord_40802).sum := by decide
  have hdescent : baseEnd_40802 < baseStart_40802 := by decide
  rcases family_descends (prefixWord ++ tailWord_40802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40830 : List Nat := [4, 2, 3, 1, 1, 1, 1, 8]
def baseStart_40830 : Nat := 118140960795 + 40830 * 2 ^ 59
def prefixEnd_40830 : Nat := 4983230072969 + 3 ^ 40 * 40830 * 2
def baseEnd_40830 : Nat := 3105987425656368316627

theorem tailTrace_40830 : CollatzResearch.WordTrace tailWord_40830 prefixEnd_40830 3105987425656368316627 := by
  unfold tailWord_40830
  simp only [CollatzResearch.WordTrace]
  refine ⟨186149055260919756742993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 992794961391572035962629 186149055260919756742993)
  ·
    refine ⟨139611791445689817557245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186149055260919756742993 139611791445689817557245)
    ·
      refine ⟨52354421792133681583967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139611791445689817557245 52354421792133681583967)
      ·
        refine ⟨78531632688200522375951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52354421792133681583967 78531632688200522375951)
        ·
          refine ⟨117797449032300783563927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78531632688200522375951 117797449032300783563927)
          ·
            refine ⟨176696173548451175345891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117797449032300783563927 176696173548451175345891)
            ·
              refine ⟨265044260322676763018837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176696173548451175345891 265044260322676763018837)
              ·
                refine ⟨3105987425656368316627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 265044260322676763018837 3105987425656368316627)
                ·
                  rfl

theorem cell21_40830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_40830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40830 prefixEnd_40830 := by exact prefixLift 40830
  have htrace : WordTrace (prefixWord ++ tailWord_40830) baseStart_40830 baseEnd_40830 := by
    simpa [prefixWord, tailWord_40830, baseEnd_40830] using wordTrace_append hprefix tailTrace_40830
  have hstable : (prefixWord ++ tailWord_40830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40830).length < 2 ^ (prefixWord ++ tailWord_40830).sum := by decide
  have hdescent : baseEnd_40830 < baseStart_40830 := by decide
  rcases family_descends (prefixWord ++ tailWord_40830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40965 : List Nat := [1, 3, 1, 1, 2, 4, 4, 5]
def baseStart_40965 : Nat := 118140960795 + 40965 * 2 ^ 59
def prefixEnd_40965 : Nat := 4983230072969 + 3 ^ 40 * 40965 * 2
def baseEnd_40965 : Nat := 3116257038746290066535

theorem tailTrace_40965 : CollatzResearch.WordTrace tailWord_40965 prefixEnd_40965 3116257038746290066535 := by
  unfold tailWord_40965
  simp only [CollatzResearch.WordTrace]
  refine ⟨1494116296598276110108349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 996077531065517406738899 1494116296598276110108349)
  ·
    refine ⟨560293611224353541290631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1494116296598276110108349 560293611224353541290631)
    ·
      refine ⟨840440416836530311935947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 560293611224353541290631 840440416836530311935947)
      ·
        refine ⟨1260660625254795467903921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840440416836530311935947 1260660625254795467903921)
        ·
          refine ⟨945495468941096600927941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1260660625254795467903921 945495468941096600927941)
          ·
            refine ⟨177280400426455612673989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 945495468941096600927941 177280400426455612673989)
            ·
              refine ⟨33240075079960427376373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177280400426455612673989 33240075079960427376373)
              ·
                refine ⟨3116257038746290066535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33240075079960427376373 3116257038746290066535)
                ·
                  rfl

theorem cell21_40965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 5].length) (baseStart_40965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_40965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_40965 prefixEnd_40965 := by exact prefixLift 40965
  have htrace : WordTrace (prefixWord ++ tailWord_40965) baseStart_40965 baseEnd_40965 := by
    simpa [prefixWord, tailWord_40965, baseEnd_40965] using wordTrace_append hprefix tailTrace_40965
  have hstable : (prefixWord ++ tailWord_40965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40965).length < 2 ^ (prefixWord ++ tailWord_40965).sum := by decide
  have hdescent : baseEnd_40965 < baseStart_40965 := by decide
  rcases family_descends (prefixWord ++ tailWord_40965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41024 : List Nat := [2, 1, 1, 2, 2, 4, 2, 7]
def baseStart_41024 : Nat := 118140960795 + 41024 * 2 ^ 59
def prefixEnd_41024 : Nat := 4983230072969 + 3 ^ 40 * 41024 * 2
def baseEnd_41024 : Nat := 3120745240022626238717

theorem tailTrace_41024 : CollatzResearch.WordTrace tailWord_41024 prefixEnd_41024 3120745240022626238717 := by
  unfold tailWord_41024
  simp only [CollatzResearch.WordTrace]
  refine ⟨748134101692264593253063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 997512135589686124337417 748134101692264593253063)
  ·
    refine ⟨1122201152538396889879595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 748134101692264593253063 1122201152538396889879595)
    ·
      refine ⟨1683301728807595334819393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122201152538396889879595 1683301728807595334819393)
      ·
        refine ⟨1262476296605696501114545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1683301728807595334819393 1262476296605696501114545)
        ·
          refine ⟨946857222454272375835909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1262476296605696501114545 946857222454272375835909)
          ·
            refine ⟨177535729210176070469233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 946857222454272375835909 177535729210176070469233)
            ·
              refine ⟨133151796907632052851925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177535729210176070469233 133151796907632052851925)
              ·
                refine ⟨3120745240022626238717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 133151796907632052851925 3120745240022626238717)
                ·
                  rfl

theorem cell21_41024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_41024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41024 prefixEnd_41024 := by exact prefixLift 41024
  have htrace : WordTrace (prefixWord ++ tailWord_41024) baseStart_41024 baseEnd_41024 := by
    simpa [prefixWord, tailWord_41024, baseEnd_41024] using wordTrace_append hprefix tailTrace_41024
  have hstable : (prefixWord ++ tailWord_41024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41024).length < 2 ^ (prefixWord ++ tailWord_41024).sum := by decide
  have hdescent : baseEnd_41024 < baseStart_41024 := by decide
  rcases family_descends (prefixWord ++ tailWord_41024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41030 : List Nat := [6, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_41030 : Nat := 118140960795 + 41030 * 2 ^ 59
def prefixEnd_41030 : Nat := 4983230072969 + 3 ^ 40 * 41030 * 2
def baseEnd_41030 : Nat := 9363605001813201616139

theorem tailTrace_41030 : CollatzResearch.WordTrace tailWord_41030 prefixEnd_41030 9363605001813201616139 := by
  unfold tailWord_41030
  simp only [CollatzResearch.WordTrace]
  refine ⟨46765220042587256600767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 997658027575194807483029 46765220042587256600767)
  ·
    refine ⟨70147830063880884901151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46765220042587256600767 70147830063880884901151)
    ·
      refine ⟨105221745095821327351727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70147830063880884901151 105221745095821327351727)
      ·
        refine ⟨157832617643731991027591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105221745095821327351727 157832617643731991027591)
        ·
          refine ⟨236748926465597986541387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157832617643731991027591 236748926465597986541387)
          ·
            refine ⟨355123389698396979812081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236748926465597986541387 355123389698396979812081)
            ·
              refine ⟨266342542273797734859061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355123389698396979812081 266342542273797734859061)
              ·
                refine ⟨24969613338168537643037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 266342542273797734859061 24969613338168537643037)
                ·
                  refine ⟨9363605001813201616139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24969613338168537643037 9363605001813201616139)
                  ·
                    rfl

theorem cell21_41030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_41030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41030 prefixEnd_41030 := by exact prefixLift 41030
  have htrace : WordTrace (prefixWord ++ tailWord_41030) baseStart_41030 baseEnd_41030 := by
    simpa [prefixWord, tailWord_41030, baseEnd_41030] using wordTrace_append hprefix tailTrace_41030
  have hstable : (prefixWord ++ tailWord_41030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41030).length < 2 ^ (prefixWord ++ tailWord_41030).sum := by decide
  have hdescent : baseEnd_41030 < baseStart_41030 := by decide
  rcases family_descends (prefixWord ++ tailWord_41030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41145 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 8]
def baseStart_41145 : Nat := 118140960795 + 41145 * 2 ^ 59
def prefixEnd_41145 : Nat := 4983230072969 + 3 ^ 40 * 41145 * 2
def baseEnd_41145 : Nat := 9389849568598557199237

theorem tailTrace_41145 : CollatzResearch.WordTrace tailWord_41145 prefixEnd_41145 9389849568598557199237 := by
  unfold tailWord_41145
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500681435946166851660889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1000454290630777901107259 1500681435946166851660889)
  ·
    refine ⟨1125511076959625138745667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1500681435946166851660889 1125511076959625138745667)
    ·
      refine ⟨1688266615439437708118501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125511076959625138745667 1688266615439437708118501)
      ·
        refine ⟨316549990394894570272219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1688266615439437708118501 316549990394894570272219)
        ·
          refine ⟨474824985592341855408329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316549990394894570272219 474824985592341855408329)
          ·
            refine ⟨356118739194256391556247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474824985592341855408329 356118739194256391556247)
            ·
              refine ⟨534178108791384587334371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356118739194256391556247 534178108791384587334371)
              ·
                refine ⟨801267163187076881001557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534178108791384587334371 801267163187076881001557)
                ·
                  refine ⟨9389849568598557199237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 801267163187076881001557 9389849568598557199237)
                  ·
                    rfl

theorem cell21_41145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_41145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41145 prefixEnd_41145 := by exact prefixLift 41145
  have htrace : WordTrace (prefixWord ++ tailWord_41145) baseStart_41145 baseEnd_41145 := by
    simpa [prefixWord, tailWord_41145, baseEnd_41145] using wordTrace_append hprefix tailTrace_41145
  have hstable : (prefixWord ++ tailWord_41145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41145).length < 2 ^ (prefixWord ++ tailWord_41145).sum := by decide
  have hdescent : baseEnd_41145 < baseStart_41145 := by decide
  rcases family_descends (prefixWord ++ tailWord_41145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41162 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_41162 : Nat := 118140960795 + 41162 * 2 ^ 59
def prefixEnd_41162 : Nat := 4983230072969 + 3 ^ 40 * 41162 * 2
def baseEnd_41162 : Nat := 9393729200210305415869

theorem tailTrace_41162 : CollatzResearch.WordTrace tailWord_41162 prefixEnd_41162 9393729200210305415869 := by
  unfold tailWord_41162
  simp only [CollatzResearch.WordTrace]
  refine ⟨375325369221144688757435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1000867651256385836686493 375325369221144688757435)
  ·
    refine ⟨562988053831717033136153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 375325369221144688757435 562988053831717033136153)
    ·
      refine ⟨422241040373787774852115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 562988053831717033136153 422241040373787774852115)
      ·
        refine ⟨633361560560681662278173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422241040373787774852115 633361560560681662278173)
        ·
          refine ⟨237510585210255623354315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 633361560560681662278173 237510585210255623354315)
          ·
            refine ⟨356265877815383435031473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237510585210255623354315 356265877815383435031473)
            ·
              refine ⟨267199408361537576273605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356265877815383435031473 267199408361537576273605)
              ·
                refine ⟨50099889067788295551301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 267199408361537576273605 50099889067788295551301)
                ·
                  refine ⟨9393729200210305415869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50099889067788295551301 9393729200210305415869)
                  ·
                    rfl

theorem cell21_41162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_41162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41162 prefixEnd_41162 := by exact prefixLift 41162
  have htrace : WordTrace (prefixWord ++ tailWord_41162) baseStart_41162 baseEnd_41162 := by
    simpa [prefixWord, tailWord_41162, baseEnd_41162] using wordTrace_append hprefix tailTrace_41162
  have hstable : (prefixWord ++ tailWord_41162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41162).length < 2 ^ (prefixWord ++ tailWord_41162).sum := by decide
  have hdescent : baseEnd_41162 < baseStart_41162 := by decide
  rcases family_descends (prefixWord ++ tailWord_41162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41176 : List Nat := [2, 1, 2, 2, 4, 1, 1, 8]
def baseStart_41176 : Nat := 118140960795 + 41176 * 2 ^ 59
def prefixEnd_41176 : Nat := 4983230072969 + 3 ^ 40 * 41176 * 2
def baseEnd_41176 : Nat := 3132308063649797394169

theorem tailTrace_41176 : CollatzResearch.WordTrace tailWord_41176 prefixEnd_41176 3132308063649797394169 := by
  unfold tailWord_41176
  simp only [CollatzResearch.WordTrace]
  refine ⟨750906049416929573019691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1001208065889239430692921 750906049416929573019691)
  ·
    refine ⟨1126359074125394359529537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 750906049416929573019691 1126359074125394359529537)
    ·
      refine ⟨844769305594045769647153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1126359074125394359529537 844769305594045769647153)
      ·
        refine ⟨633576979195534327235365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 844769305594045769647153 633576979195534327235365)
        ·
          refine ⟨118795683599162686356631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 633576979195534327235365 118795683599162686356631)
          ·
            refine ⟨178193525398744029534947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118795683599162686356631 178193525398744029534947)
            ·
              refine ⟨267290288098116044302421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178193525398744029534947 267290288098116044302421)
              ·
                refine ⟨3132308063649797394169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 267290288098116044302421 3132308063649797394169)
                ·
                  rfl

theorem cell21_41176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_41176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41176 prefixEnd_41176 := by exact prefixLift 41176
  have htrace : WordTrace (prefixWord ++ tailWord_41176) baseStart_41176 baseEnd_41176 := by
    simpa [prefixWord, tailWord_41176, baseEnd_41176] using wordTrace_append hprefix tailTrace_41176
  have hstable : (prefixWord ++ tailWord_41176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41176).length < 2 ^ (prefixWord ++ tailWord_41176).sum := by decide
  have hdescent : baseEnd_41176 < baseStart_41176 := by decide
  rcases family_descends (prefixWord ++ tailWord_41176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41258 : List Nat := [3, 1, 4, 2, 2, 1, 2, 3, 3]
def baseStart_41258 : Nat := 118140960795 + 41258 * 2 ^ 59
def prefixEnd_41258 : Nat := 4983230072969 + 3 ^ 40 * 41258 * 2
def baseEnd_41258 : Nat := 9415637708135471815673

theorem tailTrace_41258 : CollatzResearch.WordTrace tailWord_41258 prefixEnd_41258 9415637708135471815673 := by
  unfold tailWord_41258
  simp only [CollatzResearch.WordTrace]
  refine ⟨376200721134196787631107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1003201923024524767016285 376200721134196787631107)
  ·
    refine ⟨564301081701295181446661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 376200721134196787631107 564301081701295181446661)
    ·
      refine ⟨105806452818992846521249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 564301081701295181446661 105806452818992846521249)
      ·
        refine ⟨79354839614244634890937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105806452818992846521249 79354839614244634890937)
        ·
          refine ⟨59516129710683476168203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79354839614244634890937 59516129710683476168203)
          ·
            refine ⟨89274194566025214252305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59516129710683476168203 89274194566025214252305)
            ·
              refine ⟨66955645924518910689229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89274194566025214252305 66955645924518910689229)
              ·
                refine ⟨25108367221694591508461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66955645924518910689229 25108367221694591508461)
                ·
                  refine ⟨9415637708135471815673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25108367221694591508461 9415637708135471815673)
                  ·
                    rfl

theorem cell21_41258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_41258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41258 prefixEnd_41258 := by exact prefixLift 41258
  have htrace : WordTrace (prefixWord ++ tailWord_41258) baseStart_41258 baseEnd_41258 := by
    simpa [prefixWord, tailWord_41258, baseEnd_41258] using wordTrace_append hprefix tailTrace_41258
  have hstable : (prefixWord ++ tailWord_41258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41258).length < 2 ^ (prefixWord ++ tailWord_41258).sum := by decide
  have hdescent : baseEnd_41258 < baseStart_41258 := by decide
  rcases family_descends (prefixWord ++ tailWord_41258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41314 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_41314 : Nat := 118140960795 + 41314 * 2 ^ 59
def prefixEnd_41314 : Nat := 4983230072969 + 3 ^ 40 * 41314 * 2
def baseEnd_41314 : Nat := 9428417671091818882225

theorem tailTrace_41314 : CollatzResearch.WordTrace tailWord_41314 prefixEnd_41314 9428417671091818882225 := by
  unfold tailWord_41314
  simp only [CollatzResearch.WordTrace]
  refine ⟨376711343083477178640749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1004563581555939143041997 376711343083477178640749)
  ·
    refine ⟨141266753656303941990281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 376711343083477178640749 141266753656303941990281)
    ·
      refine ⟨105950065242227956492711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141266753656303941990281 105950065242227956492711)
      ·
        refine ⟨158925097863341934739067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105950065242227956492711 158925097863341934739067)
        ·
          refine ⟨238387646795012902108601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158925097863341934739067 238387646795012902108601)
          ·
            refine ⟨178790735096259676581451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238387646795012902108601 178790735096259676581451)
            ·
              refine ⟨268186102644389514872177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178790735096259676581451 268186102644389514872177)
              ·
                refine ⟨201139576983292136154133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268186102644389514872177 201139576983292136154133)
                ·
                  refine ⟨9428417671091818882225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 201139576983292136154133 9428417671091818882225)
                  ·
                    rfl

theorem cell21_41314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_41314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41314 prefixEnd_41314 := by exact prefixLift 41314
  have htrace : WordTrace (prefixWord ++ tailWord_41314) baseStart_41314 baseEnd_41314 := by
    simpa [prefixWord, tailWord_41314, baseEnd_41314] using wordTrace_append hprefix tailTrace_41314
  have hstable : (prefixWord ++ tailWord_41314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41314).length < 2 ^ (prefixWord ++ tailWord_41314).sum := by decide
  have hdescent : baseEnd_41314 < baseStart_41314 := by decide
  rcases family_descends (prefixWord ++ tailWord_41314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41317 : List Nat := [1, 3, 1, 3, 1, 5, 1, 3, 3]
def baseStart_41317 : Nat := 118140960795 + 41317 * 2 ^ 59
def prefixEnd_41317 : Nat := 4983230072969 + 3 ^ 40 * 41317 * 2
def baseEnd_41317 : Nat := 9429102311964480332219

theorem tailTrace_41317 : CollatzResearch.WordTrace tailWord_41317 prefixEnd_41317 9429102311964480332219 := by
  unfold tailWord_41317
  simp only [CollatzResearch.WordTrace]
  refine ⟨1506954791323040226922205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1004636527548693484614803 1506954791323040226922205)
  ·
    refine ⟨565108046746140085095827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1506954791323040226922205 565108046746140085095827)
    ·
      refine ⟨847662070119210127643741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565108046746140085095827 847662070119210127643741)
      ·
        refine ⟨317873276294703797866403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 847662070119210127643741 317873276294703797866403)
        ·
          refine ⟨476809914442055696799605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317873276294703797866403 476809914442055696799605)
          ·
            refine ⟨44700929478942721574963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 476809914442055696799605 44700929478942721574963)
            ·
              refine ⟨67051394218414082362445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44700929478942721574963 67051394218414082362445)
              ·
                refine ⟨25144272831905280885917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67051394218414082362445 25144272831905280885917)
                ·
                  refine ⟨9429102311964480332219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25144272831905280885917 9429102311964480332219)
                  ·
                    rfl

theorem cell21_41317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_41317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41317 prefixEnd_41317 := by exact prefixLift 41317
  have htrace : WordTrace (prefixWord ++ tailWord_41317) baseStart_41317 baseEnd_41317 := by
    simpa [prefixWord, tailWord_41317, baseEnd_41317] using wordTrace_append hprefix tailTrace_41317
  have hstable : (prefixWord ++ tailWord_41317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41317).length < 2 ^ (prefixWord ++ tailWord_41317).sum := by decide
  have hdescent : baseEnd_41317 < baseStart_41317 := by decide
  rcases family_descends (prefixWord ++ tailWord_41317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41328 : List Nat := [2, 1, 1, 1, 4, 5, 7]
def baseStart_41328 : Nat := 118140960795 + 41328 * 2 ^ 59
def prefixEnd_41328 : Nat := 4983230072969 + 3 ^ 40 * 41328 * 2
def baseEnd_41328 : Nat := 1047956962425656183207

theorem tailTrace_41328 : CollatzResearch.WordTrace tailWord_41328 prefixEnd_41328 1047956962425656183207 := by
  unfold tailWord_41328
  simp only [CollatzResearch.WordTrace]
  refine ⟨753677997141594552786319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1004903996188792737048425 753677997141594552786319)
  ·
    refine ⟨1130516995712391829179479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 753677997141594552786319 1130516995712391829179479)
    ·
      refine ⟨1695775493568587743769219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1130516995712391829179479 1695775493568587743769219)
      ·
        refine ⟨2543663240352881615653829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695775493568587743769219 2543663240352881615653829)
        ·
          refine ⟨476936857566165302935093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2543663240352881615653829 476936857566165302935093)
          ·
            refine ⟨44712830396827997150165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 476936857566165302935093 44712830396827997150165)
            ·
              refine ⟨1047956962425656183207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 44712830396827997150165 1047956962425656183207)
              ·
                rfl

theorem cell21_41328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 7].length) (baseStart_41328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41328 prefixEnd_41328 := by exact prefixLift 41328
  have htrace : WordTrace (prefixWord ++ tailWord_41328) baseStart_41328 baseEnd_41328 := by
    simpa [prefixWord, tailWord_41328, baseEnd_41328] using wordTrace_append hprefix tailTrace_41328
  have hstable : (prefixWord ++ tailWord_41328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41328).length < 2 ^ (prefixWord ++ tailWord_41328).sum := by decide
  have hdescent : baseEnd_41328 < baseStart_41328 := by decide
  rcases family_descends (prefixWord ++ tailWord_41328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41334 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_41334 : Nat := 118140960795 + 41334 * 2 ^ 59
def prefixEnd_41334 : Nat := 4983230072969 + 3 ^ 40 * 41334 * 2
def baseEnd_41334 : Nat := 9432981943576228548851

theorem tailTrace_41334 : CollatzResearch.WordTrace tailWord_41334 prefixEnd_41334 9432981943576228548851 := by
  unfold tailWord_41334
  simp only [CollatzResearch.WordTrace]
  refine ⟨94223427016340758143191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1005049888174301420194037 94223427016340758143191)
  ·
    refine ⟨141335140524511137214787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94223427016340758143191 141335140524511137214787)
    ·
      refine ⟨212002710786766705822181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141335140524511137214787 212002710786766705822181)
      ·
        refine ⟨39750508272518757341659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212002710786766705822181 39750508272518757341659)
        ·
          refine ⟨59625762408778136012489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39750508272518757341659 59625762408778136012489)
          ·
            refine ⟨44719321806583602009367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59625762408778136012489 44719321806583602009367)
            ·
              refine ⟨67078982709875403014051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44719321806583602009367 67078982709875403014051)
              ·
                refine ⟨100618474064813104521077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67078982709875403014051 100618474064813104521077)
                ·
                  refine ⟨9432981943576228548851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100618474064813104521077 9432981943576228548851)
                  ·
                    rfl

theorem cell21_41334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_41334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41334 prefixEnd_41334 := by exact prefixLift 41334
  have htrace : WordTrace (prefixWord ++ tailWord_41334) baseStart_41334 baseEnd_41334 := by
    simpa [prefixWord, tailWord_41334, baseEnd_41334] using wordTrace_append hprefix tailTrace_41334
  have hstable : (prefixWord ++ tailWord_41334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41334).length < 2 ^ (prefixWord ++ tailWord_41334).sum := by decide
  have hdescent : baseEnd_41334 < baseStart_41334 := by decide
  rcases family_descends (prefixWord ++ tailWord_41334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41345 : List Nat := [1, 2, 4, 3, 1, 2, 2, 6]
def baseStart_41345 : Nat := 118140960795 + 41345 * 2 ^ 59
def prefixEnd_41345 : Nat := 4983230072969 + 3 ^ 40 * 41345 * 2
def baseEnd_41345 : Nat := 3145164097814217955165

theorem tailTrace_41345 : CollatzResearch.WordTrace tailWord_41345 prefixEnd_41345 3145164097814217955165 := by
  unfold tailWord_41345
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507976035221601008941489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1005317356814400672627659 1507976035221601008941489)
  ·
    refine ⟨1130982026416200756706117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1507976035221601008941489 1130982026416200756706117)
    ·
      refine ⟨212059129953037641882397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1130982026416200756706117 212059129953037641882397)
      ·
        refine ⟨79522173732389115705899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212059129953037641882397 79522173732389115705899)
        ·
          refine ⟨119283260598583673558849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79522173732389115705899 119283260598583673558849)
          ·
            refine ⟨89462445448937755169137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119283260598583673558849 89462445448937755169137)
            ·
              refine ⟨67096834086703316376853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89462445448937755169137 67096834086703316376853)
              ·
                refine ⟨3145164097814217955165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67096834086703316376853 3145164097814217955165)
                ·
                  rfl

theorem cell21_41345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 6].length) (baseStart_41345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41345 prefixEnd_41345 := by exact prefixLift 41345
  have htrace : WordTrace (prefixWord ++ tailWord_41345) baseStart_41345 baseEnd_41345 := by
    simpa [prefixWord, tailWord_41345, baseEnd_41345] using wordTrace_append hprefix tailTrace_41345
  have hstable : (prefixWord ++ tailWord_41345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41345).length < 2 ^ (prefixWord ++ tailWord_41345).sum := by decide
  have hdescent : baseEnd_41345 < baseStart_41345 := by decide
  rcases family_descends (prefixWord ++ tailWord_41345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41393 : List Nat := [1, 2, 2, 4, 1, 2, 4, 2, 3]
def baseStart_41393 : Nat := 118140960795 + 41393 * 2 ^ 59
def prefixEnd_41393 : Nat := 4983230072969 + 3 ^ 40 * 41393 * 2
def baseEnd_41393 : Nat := 9446446547405237065397

theorem tailTrace_41393 : CollatzResearch.WordTrace tailWord_41393 prefixEnd_41393 9446446547405237065397 := by
  unfold tailWord_41393
  simp only [CollatzResearch.WordTrace]
  refine ⟨1509726739047705206688833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1006484492698470137792555 1509726739047705206688833)
  ·
    refine ⟨1132295054285778905016625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1509726739047705206688833 1132295054285778905016625)
    ·
      refine ⟨849221290714334178762469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1132295054285778905016625 849221290714334178762469)
      ·
        refine ⟨159228992008937658517963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 849221290714334178762469 159228992008937658517963)
        ·
          refine ⟨238843488013406487776945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159228992008937658517963 238843488013406487776945)
          ·
            refine ⟨179132616010054865832709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238843488013406487776945 179132616010054865832709)
            ·
              refine ⟨33587365501885287343633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179132616010054865832709 33587365501885287343633)
              ·
                refine ⟨25190524126413965507725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33587365501885287343633 25190524126413965507725)
                ·
                  refine ⟨9446446547405237065397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25190524126413965507725 9446446547405237065397)
                  ·
                    rfl

theorem cell21_41393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 3].length) (baseStart_41393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41393 prefixEnd_41393 := by exact prefixLift 41393
  have htrace : WordTrace (prefixWord ++ tailWord_41393) baseStart_41393 baseEnd_41393 := by
    simpa [prefixWord, tailWord_41393, baseEnd_41393] using wordTrace_append hprefix tailTrace_41393
  have hstable : (prefixWord ++ tailWord_41393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41393).length < 2 ^ (prefixWord ++ tailWord_41393).sum := by decide
  have hdescent : baseEnd_41393 < baseStart_41393 := by decide
  rcases family_descends (prefixWord ++ tailWord_41393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41396 : List Nat := [2, 5, 2, 2, 2, 1, 1, 6]
def baseStart_41396 : Nat := 118140960795 + 41396 * 2 ^ 59
def prefixEnd_41396 : Nat := 4983230072969 + 3 ^ 40 * 41396 * 2
def baseEnd_41396 : Nat := 3149043729425966171797

theorem tailTrace_41396 : CollatzResearch.WordTrace tailWord_41396 prefixEnd_41396 3149043729425966171797 := by
  unfold tailWord_41396
  simp only [CollatzResearch.WordTrace]
  refine ⟨754918079018418359524021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1006557438691224479365361 754918079018418359524021)
  ·
    refine ⟨70773569907976721205377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 754918079018418359524021 70773569907976721205377)
    ·
      refine ⟨53080177430982540904033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70773569907976721205377 53080177430982540904033)
      ·
        refine ⟨39810133073236905678025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53080177430982540904033 39810133073236905678025)
        ·
          refine ⟨29857599804927679258519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39810133073236905678025 29857599804927679258519)
          ·
            refine ⟨44786399707391518887779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29857599804927679258519 44786399707391518887779)
            ·
              refine ⟨67179599561087278331669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44786399707391518887779 67179599561087278331669)
              ·
                refine ⟨3149043729425966171797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67179599561087278331669 3149043729425966171797)
                ·
                  rfl

theorem cell21_41396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 6].length) (baseStart_41396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41396 prefixEnd_41396 := by exact prefixLift 41396
  have htrace : WordTrace (prefixWord ++ tailWord_41396) baseStart_41396 baseEnd_41396 := by
    simpa [prefixWord, tailWord_41396, baseEnd_41396] using wordTrace_append hprefix tailTrace_41396
  have hstable : (prefixWord ++ tailWord_41396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41396).length < 2 ^ (prefixWord ++ tailWord_41396).sum := by decide
  have hdescent : baseEnd_41396 < baseStart_41396 := by decide
  rcases family_descends (prefixWord ++ tailWord_41396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41449 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 4]
def baseStart_41449 : Nat := 118140960795 + 41449 * 2 ^ 59
def prefixEnd_41449 : Nat := 4983230072969 + 3 ^ 40 * 41449 * 2
def baseEnd_41449 : Nat := 9459226510361584131949

theorem tailTrace_41449 : CollatzResearch.WordTrace tailWord_41449 prefixEnd_41449 9459226510361584131949 := by
  unfold tailWord_41449
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511769226844826770727401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1007846151229884513818267 1511769226844826770727401)
  ·
    refine ⟨1133826920133620078045551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1511769226844826770727401 1133826920133620078045551)
    ·
      refine ⟨1700740380200430117068327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1133826920133620078045551 1700740380200430117068327)
      ·
        refine ⟨2551110570300645175602491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700740380200430117068327 2551110570300645175602491)
        ·
          refine ⟨3826665855450967763403737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551110570300645175602491 3826665855450967763403737)
          ·
            refine ⟨2869999391588225822552803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3826665855450967763403737 2869999391588225822552803)
            ·
              refine ⟨4304999087382338733829205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869999391588225822552803 4304999087382338733829205)
              ·
                refine ⟨50449208055261782037061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4304999087382338733829205 50449208055261782037061)
                ·
                  refine ⟨9459226510361584131949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50449208055261782037061 9459226510361584131949)
                  ·
                    rfl

theorem cell21_41449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_41449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41449 prefixEnd_41449 := by exact prefixLift 41449
  have htrace : WordTrace (prefixWord ++ tailWord_41449) baseStart_41449 baseEnd_41449 := by
    simpa [prefixWord, tailWord_41449, baseEnd_41449] using wordTrace_append hprefix tailTrace_41449
  have hstable : (prefixWord ++ tailWord_41449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41449).length < 2 ^ (prefixWord ++ tailWord_41449).sum := by decide
  have hdescent : baseEnd_41449 < baseStart_41449 := by decide
  rcases family_descends (prefixWord ++ tailWord_41449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41517 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 4]
def baseStart_41517 : Nat := 118140960795 + 41517 * 2 ^ 59
def prefixEnd_41517 : Nat := 4983230072969 + 3 ^ 40 * 41517 * 2
def baseEnd_41517 : Nat := 9474745036808576998477

theorem tailTrace_41517 : CollatzResearch.WordTrace tailWord_41517 prefixEnd_41517 9474745036808576998477 := by
  unfold tailWord_41517
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514249390598474384202805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1009499593732316256135203 1514249390598474384202805)
  ·
    refine ⟨141960880368606973519013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1514249390598474384202805 141960880368606973519013)
    ·
      refine ⟨26617665069113807534815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141960880368606973519013 26617665069113807534815)
      ·
        refine ⟨39926497603670711302223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26617665069113807534815 39926497603670711302223)
        ·
          refine ⟨59889746405506066953335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39926497603670711302223 59889746405506066953335)
          ·
            refine ⟨89834619608259100430003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59889746405506066953335 89834619608259100430003)
            ·
              refine ⟨134751929412388650645005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89834619608259100430003 134751929412388650645005)
              ·
                refine ⟨50531973529645743991877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134751929412388650645005 50531973529645743991877)
                ·
                  refine ⟨9474745036808576998477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50531973529645743991877 9474745036808576998477)
                  ·
                    rfl

theorem cell21_41517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_41517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41517 prefixEnd_41517 := by exact prefixLift 41517
  have htrace : WordTrace (prefixWord ++ tailWord_41517) baseStart_41517 baseEnd_41517 := by
    simpa [prefixWord, tailWord_41517, baseEnd_41517] using wordTrace_append hprefix tailTrace_41517
  have hstable : (prefixWord ++ tailWord_41517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41517).length < 2 ^ (prefixWord ++ tailWord_41517).sum := by decide
  have hdescent : baseEnd_41517 < baseStart_41517 := by decide
  rcases family_descends (prefixWord ++ tailWord_41517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41573 : List Nat := [1, 3, 1, 3, 4, 2, 1, 6]
def baseStart_41573 : Nat := 118140960795 + 41573 * 2 ^ 59
def prefixEnd_41573 : Nat := 4983230072969 + 3 ^ 40 * 41573 * 2
def baseEnd_41573 : Nat := 3162508333254974688343

theorem tailTrace_41573 : CollatzResearch.WordTrace tailWord_41573 prefixEnd_41573 3162508333254974688343 := by
  unfold tailWord_41573
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516291878395595948241373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1010861252263730632160915 1516291878395595948241373)
  ·
    refine ⟨568609454398348480590515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1516291878395595948241373 568609454398348480590515)
    ·
      refine ⟨852914181597522720885773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568609454398348480590515 852914181597522720885773)
      ·
        refine ⟨319842818099071020332165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 852914181597522720885773 319842818099071020332165)
        ·
          refine ⟨59970528393575816312281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 319842818099071020332165 59970528393575816312281)
          ·
            refine ⟨44977896295181862234211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59970528393575816312281 44977896295181862234211)
            ·
              refine ⟨67466844442772793351317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44977896295181862234211 67466844442772793351317)
              ·
                refine ⟨3162508333254974688343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67466844442772793351317 3162508333254974688343)
                ·
                  rfl

theorem cell21_41573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 6].length) (baseStart_41573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41573 prefixEnd_41573 := by exact prefixLift 41573
  have htrace : WordTrace (prefixWord ++ tailWord_41573) baseStart_41573 baseEnd_41573 := by
    simpa [prefixWord, tailWord_41573, baseEnd_41573] using wordTrace_append hprefix tailTrace_41573
  have hstable : (prefixWord ++ tailWord_41573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41573).length < 2 ^ (prefixWord ++ tailWord_41573).sum := by decide
  have hdescent : baseEnd_41573 < baseStart_41573 := by decide
  rcases family_descends (prefixWord ++ tailWord_41573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41590 : List Nat := [5, 1, 1, 2, 3, 1, 3, 5]
def baseStart_41590 : Nat := 118140960795 + 41590 * 2 ^ 59
def prefixEnd_41590 : Nat := 4983230072969 + 3 ^ 40 * 41590 * 2
def baseEnd_41590 : Nat := 3163801543792224093887

theorem tailTrace_41590 : CollatzResearch.WordTrace tailWord_41590 prefixEnd_41590 3163801543792224093887 := by
  unfold tailWord_41590
  simp only [CollatzResearch.WordTrace]
  refine ⟨94806994958375490725639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1011274612889338567740149 94806994958375490725639)
  ·
    refine ⟨142210492437563236088459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94806994958375490725639 142210492437563236088459)
    ·
      refine ⟨213315738656344854132689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142210492437563236088459 213315738656344854132689)
      ·
        refine ⟨159986803992258640599517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213315738656344854132689 159986803992258640599517)
        ·
          refine ⟨59995051497096990224819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159986803992258640599517 59995051497096990224819)
          ·
            refine ⟨89992577245645485337229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59995051497096990224819 89992577245645485337229)
            ·
              refine ⟨33747216467117057001461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89992577245645485337229 33747216467117057001461)
              ·
                refine ⟨3163801543792224093887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33747216467117057001461 3163801543792224093887)
                ·
                  rfl

theorem cell21_41590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_41590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41590 prefixEnd_41590 := by exact prefixLift 41590
  have htrace : WordTrace (prefixWord ++ tailWord_41590) baseStart_41590 baseEnd_41590 := by
    simpa [prefixWord, tailWord_41590, baseEnd_41590] using wordTrace_append hprefix tailTrace_41590
  have hstable : (prefixWord ++ tailWord_41590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41590).length < 2 ^ (prefixWord ++ tailWord_41590).sum := by decide
  have hdescent : baseEnd_41590 < baseStart_41590 := by decide
  rcases family_descends (prefixWord ++ tailWord_41590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41601 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 6]
def baseStart_41601 : Nat := 118140960795 + 41601 * 2 ^ 59
def prefixEnd_41601 : Nat := 4983230072969 + 3 ^ 40 * 41601 * 2
def baseEnd_41601 : Nat := 9493914981243097598305

theorem tailTrace_41601 : CollatzResearch.WordTrace tailWord_41601 prefixEnd_41601 9493914981243097598305 := by
  unfold tailWord_41601
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517313122294156730260657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1011542081529437820173771 1517313122294156730260657)
  ·
    refine ⟨1137984841720617547695493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1517313122294156730260657 1137984841720617547695493)
    ·
      refine ⟨213372157822615790192905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1137984841720617547695493 213372157822615790192905)
      ·
        refine ⟨160029118366961842644679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213372157822615790192905 160029118366961842644679)
        ·
          refine ⟨240043677550442763967019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160029118366961842644679 240043677550442763967019)
          ·
            refine ⟨360065516325664145950529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240043677550442763967019 360065516325664145950529)
            ·
              refine ⟨270049137244248109462897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360065516325664145950529 270049137244248109462897)
              ·
                refine ⟨202536852933186082097173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270049137244248109462897 202536852933186082097173)
                ·
                  refine ⟨9493914981243097598305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 202536852933186082097173 9493914981243097598305)
                  ·
                    rfl

theorem cell21_41601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_41601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41601 prefixEnd_41601 := by exact prefixLift 41601
  have htrace : WordTrace (prefixWord ++ tailWord_41601) baseStart_41601 baseEnd_41601 := by
    simpa [prefixWord, tailWord_41601, baseEnd_41601] using wordTrace_append hprefix tailTrace_41601
  have hstable : (prefixWord ++ tailWord_41601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41601).length < 2 ^ (prefixWord ++ tailWord_41601).sum := by decide
  have hdescent : baseEnd_41601 < baseStart_41601 := by decide
  rcases family_descends (prefixWord ++ tailWord_41601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41604 : List Nat := [2, 3, 2, 1, 3, 1, 1, 5, 3]
def baseStart_41604 : Nat := 118140960795 + 41604 * 2 ^ 59
def prefixEnd_41604 : Nat := 4983230072969 + 3 ^ 40 * 41604 * 2
def baseEnd_41604 : Nat := 9494599622115759048299

theorem tailTrace_41604 : CollatzResearch.WordTrace tailWord_41604 prefixEnd_41604 9494599622115759048299 := by
  unfold tailWord_41604
  simp only [CollatzResearch.WordTrace]
  refine ⟨758711270641644121309933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1011615027522192161746577 758711270641644121309933)
  ·
    refine ⟨284516726490616545491225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 758711270641644121309933 284516726490616545491225)
    ·
      refine ⟨213387544867962409118419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284516726490616545491225 213387544867962409118419)
      ·
        refine ⟨320081317301943613677629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213387544867962409118419 320081317301943613677629)
        ·
          refine ⟨120030493988228855129111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320081317301943613677629 120030493988228855129111)
          ·
            refine ⟨180045740982343282693667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120030493988228855129111 180045740982343282693667)
            ·
              refine ⟨270068611473514924040501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180045740982343282693667 270068611473514924040501)
              ·
                refine ⟨25318932325642024128797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270068611473514924040501 25318932325642024128797)
                ·
                  refine ⟨9494599622115759048299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25318932325642024128797 9494599622115759048299)
                  ·
                    rfl

theorem cell21_41604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_41604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41604 prefixEnd_41604 := by exact prefixLift 41604
  have htrace : WordTrace (prefixWord ++ tailWord_41604) baseStart_41604 baseEnd_41604 := by
    simpa [prefixWord, tailWord_41604, baseEnd_41604] using wordTrace_append hprefix tailTrace_41604
  have hstable : (prefixWord ++ tailWord_41604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41604).length < 2 ^ (prefixWord ++ tailWord_41604).sum := by decide
  have hdescent : baseEnd_41604 < baseStart_41604 := by decide
  rcases family_descends (prefixWord ++ tailWord_41604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41618 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_41618 : Nat := 118140960795 + 41618 * 2 ^ 59
def prefixEnd_41618 : Nat := 4983230072969 + 3 ^ 40 * 41618 * 2
def baseEnd_41618 : Nat := 9497794612854845814937

theorem tailTrace_41618 : CollatzResearch.WordTrace tailWord_41618 prefixEnd_41618 9497794612854845814937 := by
  unfold tailWord_41618
  simp only [CollatzResearch.WordTrace]
  refine ⟨379483290808142158407377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1011955442155045755753005 379483290808142158407377)
  ·
    refine ⟨284612468106106618805533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 379483290808142158407377 284612468106106618805533)
    ·
      refine ⟨106729675539789982052075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 284612468106106618805533 106729675539789982052075)
      ·
        refine ⟨160094513309684973078113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106729675539789982052075 160094513309684973078113)
        ·
          refine ⟨120070884982263729808585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160094513309684973078113 120070884982263729808585)
          ·
            refine ⟨90053163736697797356439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120070884982263729808585 90053163736697797356439)
            ·
              refine ⟨135079745605046696034659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90053163736697797356439 135079745605046696034659)
              ·
                refine ⟨202619618407570044051989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135079745605046696034659 202619618407570044051989)
                ·
                  refine ⟨9497794612854845814937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 202619618407570044051989 9497794612854845814937)
                  ·
                    rfl

theorem cell21_41618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_41618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41618 prefixEnd_41618 := by exact prefixLift 41618
  have htrace : WordTrace (prefixWord ++ tailWord_41618) baseStart_41618 baseEnd_41618 := by
    simpa [prefixWord, tailWord_41618, baseEnd_41618] using wordTrace_append hprefix tailTrace_41618
  have hstable : (prefixWord ++ tailWord_41618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41618).length < 2 ^ (prefixWord ++ tailWord_41618).sum := by decide
  have hdescent : baseEnd_41618 < baseStart_41618 := by decide
  rcases family_descends (prefixWord ++ tailWord_41618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41649 : List Nat := [1, 2, 2, 6, 1, 1, 1, 7]
def baseStart_41649 : Nat := 118140960795 + 41649 * 2 ^ 59
def prefixEnd_41649 : Nat := 4983230072969 + 3 ^ 40 * 41649 * 2
def baseEnd_41649 : Nat := 3168289745068560266069

theorem tailTrace_41649 : CollatzResearch.WordTrace tailWord_41649 prefixEnd_41649 3168289745068560266069 := by
  unfold tailWord_41649
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519063826120260928008001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1012709217413507285338667 1519063826120260928008001)
  ·
    refine ⟨1139297869590195696006001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1519063826120260928008001 1139297869590195696006001)
    ·
      refine ⟨854473402192646772004501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1139297869590195696006001 854473402192646772004501)
      ·
        refine ⟨40053440727780317437711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 854473402192646772004501 40053440727780317437711)
        ·
          refine ⟨60080161091670476156567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40053440727780317437711 60080161091670476156567)
          ·
            refine ⟨90120241637505714234851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60080161091670476156567 90120241637505714234851)
            ·
              refine ⟨135180362456258571352277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90120241637505714234851 135180362456258571352277)
              ·
                refine ⟨3168289745068560266069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135180362456258571352277 3168289745068560266069)
                ·
                  rfl

theorem cell21_41649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 7].length) (baseStart_41649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41649 prefixEnd_41649 := by exact prefixLift 41649
  have htrace : WordTrace (prefixWord ++ tailWord_41649) baseStart_41649 baseEnd_41649 := by
    simpa [prefixWord, tailWord_41649, baseEnd_41649] using wordTrace_append hprefix tailTrace_41649
  have hstable : (prefixWord ++ tailWord_41649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41649).length < 2 ^ (prefixWord ++ tailWord_41649).sum := by decide
  have hdescent : baseEnd_41649 < baseStart_41649 := by decide
  rcases family_descends (prefixWord ++ tailWord_41649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41832 : List Nat := [2, 1, 4, 2, 1, 2, 3, 3, 3]
def baseStart_41832 : Nat := 118140960795 + 41832 * 2 ^ 59
def prefixEnd_41832 : Nat := 4983230072969 + 3 ^ 40 * 41832 * 2
def baseEnd_41832 : Nat := 9546632328438029247833

theorem tailTrace_41832 : CollatzResearch.WordTrace tailWord_41832 prefixEnd_41832 9546632328438029247833 := by
  unfold tailWord_41832
  simp only [CollatzResearch.WordTrace]
  refine ⟨762869192228641590959875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1017158922971522121279833 762869192228641590959875)
  ·
    refine ⟨1144303788342962386439813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 762869192228641590959875 1144303788342962386439813)
    ·
      refine ⟨214556960314305447457465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1144303788342962386439813 214556960314305447457465)
      ·
        refine ⟨160917720235729085593099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214556960314305447457465 160917720235729085593099)
        ·
          refine ⟨241376580353593628389649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160917720235729085593099 241376580353593628389649)
          ·
            refine ⟨181032435265195221292237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241376580353593628389649 181032435265195221292237)
            ·
              refine ⟨67887163224448207984589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181032435265195221292237 67887163224448207984589)
              ·
                refine ⟨25457686209168077994221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67887163224448207984589 25457686209168077994221)
                ·
                  refine ⟨9546632328438029247833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25457686209168077994221 9546632328438029247833)
                  ·
                    rfl

theorem cell21_41832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 3].length) (baseStart_41832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41832 prefixEnd_41832 := by exact prefixLift 41832
  have htrace : WordTrace (prefixWord ++ tailWord_41832) baseStart_41832 baseEnd_41832 := by
    simpa [prefixWord, tailWord_41832, baseEnd_41832] using wordTrace_append hprefix tailTrace_41832
  have hstable : (prefixWord ++ tailWord_41832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41832).length < 2 ^ (prefixWord ++ tailWord_41832).sum := by decide
  have hdescent : baseEnd_41832 < baseStart_41832 := by decide
  rcases family_descends (prefixWord ++ tailWord_41832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41846 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_41846 : Nat := 118140960795 + 41846 * 2 ^ 59
def prefixEnd_41846 : Nat := 4983230072969 + 3 ^ 40 * 41846 * 2
def baseEnd_41846 : Nat := 9549827319177116014471

theorem tailTrace_41846 : CollatzResearch.WordTrace tailWord_41846 prefixEnd_41846 9549827319177116014471 := by
  unfold tailWord_41846
  simp only [CollatzResearch.WordTrace]
  refine ⟨95390562900410223308087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1017499337604375715286261 95390562900410223308087)
  ·
    refine ⟨143085844350615334962131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95390562900410223308087 143085844350615334962131)
    ·
      refine ⟨214628766525923002443197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143085844350615334962131 214628766525923002443197)
      ·
        refine ⟨80485787447221125916199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214628766525923002443197 80485787447221125916199)
        ·
          refine ⟨120728681170831688874299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80485787447221125916199 120728681170831688874299)
          ·
            refine ⟨181093021756247533311449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120728681170831688874299 181093021756247533311449)
            ·
              refine ⟨135819766317185649983587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181093021756247533311449 135819766317185649983587)
              ·
                refine ⟨203729649475778474975381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135819766317185649983587 203729649475778474975381)
                ·
                  refine ⟨9549827319177116014471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 203729649475778474975381 9549827319177116014471)
                  ·
                    rfl

theorem cell21_41846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_41846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41846 prefixEnd_41846 := by exact prefixLift 41846
  have htrace : WordTrace (prefixWord ++ tailWord_41846) baseStart_41846 baseEnd_41846 := by
    simpa [prefixWord, tailWord_41846, baseEnd_41846] using wordTrace_append hprefix tailTrace_41846
  have hstable : (prefixWord ++ tailWord_41846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41846).length < 2 ^ (prefixWord ++ tailWord_41846).sum := by decide
  have hdescent : baseEnd_41846 < baseStart_41846 := by decide
  rcases family_descends (prefixWord ++ tailWord_41846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41863 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 4]
def baseStart_41863 : Nat := 118140960795 + 41863 * 2 ^ 59
def prefixEnd_41863 : Nat := 4983230072969 + 3 ^ 40 * 41863 * 2
def baseEnd_41863 : Nat := 9553706950788864231103

theorem tailTrace_41863 : CollatzResearch.WordTrace tailWord_41863 prefixEnd_41863 9553706950788864231103 := by
  unfold tailWord_41863
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526869047344975476298243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1017912698229983650865495 1526869047344975476298243)
  ·
    refine ⟨2290303571017463214447365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1526869047344975476298243 2290303571017463214447365)
    ·
      refine ⟨429431919565774352708881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2290303571017463214447365 429431919565774352708881)
      ·
        refine ⟨322073939674330764531661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429431919565774352708881 322073939674330764531661)
        ·
          refine ⟨120777727377874036699373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322073939674330764531661 120777727377874036699373)
          ·
            refine ⟨45291647766702763762265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120777727377874036699373 45291647766702763762265)
            ·
              refine ⟨33968735825027072821699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45291647766702763762265 33968735825027072821699)
              ·
                refine ⟨50953103737540609232549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33968735825027072821699 50953103737540609232549)
                ·
                  refine ⟨9553706950788864231103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50953103737540609232549 9553706950788864231103)
                  ·
                    rfl

theorem cell21_41863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 4].length) (baseStart_41863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41863 prefixEnd_41863 := by exact prefixLift 41863
  have htrace : WordTrace (prefixWord ++ tailWord_41863) baseStart_41863 baseEnd_41863 := by
    simpa [prefixWord, tailWord_41863, baseEnd_41863] using wordTrace_append hprefix tailTrace_41863
  have hstable : (prefixWord ++ tailWord_41863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41863).length < 2 ^ (prefixWord ++ tailWord_41863).sum := by decide
  have hdescent : baseEnd_41863 < baseStart_41863 := by decide
  rcases family_descends (prefixWord ++ tailWord_41863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41888 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_41888 : Nat := 118140960795 + 41888 * 2 ^ 59
def prefixEnd_41888 : Nat := 4983230072969 + 3 ^ 40 * 41888 * 2
def baseEnd_41888 : Nat := 9559412291394376314385

theorem tailTrace_41888 : CollatzResearch.WordTrace tailWord_41888 prefixEnd_41888 9559412291394376314385 := by
  unfold tailWord_41888
  simp only [CollatzResearch.WordTrace]
  refine ⟨763890436127202372979159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1018520581502936497305545 763890436127202372979159)
  ·
    refine ⟨1145835654190803559468739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 763890436127202372979159 1145835654190803559468739)
    ·
      refine ⟨1718753481286205339203109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1145835654190803559468739 1718753481286205339203109)
      ·
        refine ⟨322266277741163501100583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1718753481286205339203109 322266277741163501100583)
        ·
          refine ⟨483399416611745251650875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322266277741163501100583 483399416611745251650875)
          ·
            refine ⟨725099124917617877476313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483399416611745251650875 725099124917617877476313)
            ·
              refine ⟨543824343688213408107235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725099124917617877476313 543824343688213408107235)
              ·
                refine ⟨815736515532320112160853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543824343688213408107235 815736515532320112160853)
                ·
                  refine ⟨9559412291394376314385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 815736515532320112160853 9559412291394376314385)
                  ·
                    rfl

theorem cell21_41888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_41888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41888 prefixEnd_41888 := by exact prefixLift 41888
  have htrace : WordTrace (prefixWord ++ tailWord_41888) baseStart_41888 baseEnd_41888 := by
    simpa [prefixWord, tailWord_41888, baseEnd_41888] using wordTrace_append hprefix tailTrace_41888
  have hstable : (prefixWord ++ tailWord_41888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41888).length < 2 ^ (prefixWord ++ tailWord_41888).sum := by decide
  have hdescent : baseEnd_41888 < baseStart_41888 := by decide
  rcases family_descends (prefixWord ++ tailWord_41888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41967 : List Nat := [1, 1, 2, 1, 4, 3, 2, 4, 3]
def baseStart_41967 : Nat := 118140960795 + 41967 * 2 ^ 59
def prefixEnd_41967 : Nat := 4983230072969 + 3 ^ 40 * 41967 * 2
def baseEnd_41967 : Nat := 9577441167707794497557

theorem tailTrace_41967 : CollatzResearch.WordTrace tailWord_41967 prefixEnd_41967 9577441167707794497557 := by
  unfold tailWord_41967
  simp only [CollatzResearch.WordTrace]
  refine ⟨1530662238968201238084155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1020441492645467492056103 1530662238968201238084155)
  ·
    refine ⟨2295993358452301857126233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1530662238968201238084155 2295993358452301857126233)
    ·
      refine ⟨1721995018839226392844675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2295993358452301857126233 1721995018839226392844675)
      ·
        refine ⟨2582992528258839589267013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1721995018839226392844675 2582992528258839589267013)
        ·
          refine ⟨484311099048532422987565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2582992528258839589267013 484311099048532422987565)
          ·
            refine ⟨181616662143199658620337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 484311099048532422987565 181616662143199658620337)
            ·
              refine ⟨136212496607399743965253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181616662143199658620337 136212496607399743965253)
              ·
                refine ⟨25539843113887451993485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136212496607399743965253 25539843113887451993485)
                ·
                  refine ⟨9577441167707794497557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25539843113887451993485 9577441167707794497557)
                  ·
                    rfl

theorem cell21_41967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 3].length) (baseStart_41967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41967 prefixEnd_41967 := by exact prefixLift 41967
  have htrace : WordTrace (prefixWord ++ tailWord_41967) baseStart_41967 baseEnd_41967 := by
    simpa [prefixWord, tailWord_41967, baseEnd_41967] using wordTrace_append hprefix tailTrace_41967
  have hstable : (prefixWord ++ tailWord_41967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41967).length < 2 ^ (prefixWord ++ tailWord_41967).sum := by decide
  have hdescent : baseEnd_41967 < baseStart_41967 := by decide
  rcases family_descends (prefixWord ++ tailWord_41967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41995 : List Nat := [1, 1, 1, 1, 6, 3, 1, 7]
def baseStart_41995 : Nat := 118140960795 + 41995 * 2 ^ 59
def prefixEnd_41995 : Nat := 4983230072969 + 3 ^ 40 * 41995 * 2
def baseEnd_41995 : Nat := 3194610383061989343611

theorem tailTrace_41995 : CollatzResearch.WordTrace tailWord_41995 prefixEnd_41995 3194610383061989343611 := by
  unfold tailWord_41995
  simp only [CollatzResearch.WordTrace]
  refine ⟨1531683482866762020103439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1021122321911174680068959 1531683482866762020103439)
  ·
    refine ⟨2297525224300143030155159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1531683482866762020103439 2297525224300143030155159)
    ·
      refine ⟨3446287836450214545232739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2297525224300143030155159 3446287836450214545232739)
      ·
        refine ⟨5169431754675321817849109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446287836450214545232739 5169431754675321817849109)
        ·
          refine ⟨242317113500405710211677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5169431754675321817849109 242317113500405710211677)
          ·
            refine ⟨90868917562652141329379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242317113500405710211677 90868917562652141329379)
            ·
              refine ⟨136303376343978211994069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90868917562652141329379 136303376343978211994069)
              ·
                refine ⟨3194610383061989343611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 136303376343978211994069 3194610383061989343611)
                ·
                  rfl

theorem cell21_41995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 7].length) (baseStart_41995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_41995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_41995 prefixEnd_41995 := by exact prefixLift 41995
  have htrace : WordTrace (prefixWord ++ tailWord_41995) baseStart_41995 baseEnd_41995 := by
    simpa [prefixWord, tailWord_41995, baseEnd_41995] using wordTrace_append hprefix tailTrace_41995
  have hstable : (prefixWord ++ tailWord_41995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41995).length < 2 ^ (prefixWord ++ tailWord_41995).sum := by decide
  have hdescent : baseEnd_41995 < baseStart_41995 := by decide
  rcases family_descends (prefixWord ++ tailWord_41995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42009 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 7]
def baseStart_42009 : Nat := 118140960795 + 42009 * 2 ^ 59
def prefixEnd_42009 : Nat := 4983230072969 + 3 ^ 40 * 42009 * 2
def baseEnd_42009 : Nat := 9587026139925054797471

theorem tailTrace_42009 : CollatzResearch.WordTrace tailWord_42009 prefixEnd_42009 9587026139925054797471 := by
  unfold tailWord_42009
  simp only [CollatzResearch.WordTrace]
  refine ⟨1532194104816042411113081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1021462736544028274075387 1532194104816042411113081)
  ·
    refine ⟨1149145578612031808334811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1532194104816042411113081 1149145578612031808334811)
    ·
      refine ⟨1723718367918047712502217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149145578612031808334811 1723718367918047712502217)
      ·
        refine ⟨1292788775938535784376663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1723718367918047712502217 1292788775938535784376663)
        ·
          refine ⟨1939183163907803676564995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1292788775938535784376663 1939183163907803676564995)
          ·
            refine ⟨2908774745861705514847493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939183163907803676564995 2908774745861705514847493)
            ·
              refine ⟨545395264849069784033905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2908774745861705514847493 545395264849069784033905)
              ·
                refine ⟨409046448636802338025429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545395264849069784033905 409046448636802338025429)
                ·
                  refine ⟨9587026139925054797471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 409046448636802338025429 9587026139925054797471)
                  ·
                    rfl

theorem cell21_42009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_42009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42009 prefixEnd_42009 := by exact prefixLift 42009
  have htrace : WordTrace (prefixWord ++ tailWord_42009) baseStart_42009 baseEnd_42009 := by
    simpa [prefixWord, tailWord_42009, baseEnd_42009] using wordTrace_append hprefix tailTrace_42009
  have hstable : (prefixWord ++ tailWord_42009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42009).length < 2 ^ (prefixWord ++ tailWord_42009).sum := by decide
  have hdescent : baseEnd_42009 < baseStart_42009 := by decide
  rcases family_descends (prefixWord ++ tailWord_42009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42012 : List Nat := [2, 2, 3, 1, 4, 2, 7]
def baseStart_42012 : Nat := 118140960795 + 42012 * 2 ^ 59
def prefixEnd_42012 : Nat := 4983230072969 + 3 ^ 40 * 42012 * 2
def baseEnd_42012 : Nat := 1065301197866412916385

theorem tailTrace_42012 : CollatzResearch.WordTrace tailWord_42012 prefixEnd_42012 1065301197866412916385 := by
  unfold tailWord_42012
  simp only [CollatzResearch.WordTrace]
  refine ⟨766151761902586961736145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1021535682536782615648193 766151761902586961736145)
  ·
    refine ⟨574613821426940221302109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 766151761902586961736145 574613821426940221302109)
    ·
      refine ⟨215480183035102582988291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 574613821426940221302109 215480183035102582988291)
      ·
        refine ⟨323220274552653874482437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215480183035102582988291 323220274552653874482437)
        ·
          refine ⟨60603801478622601465457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323220274552653874482437 60603801478622601465457)
          ·
            refine ⟨45452851108966951099093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60603801478622601465457 45452851108966951099093)
            ·
              refine ⟨1065301197866412916385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45452851108966951099093 1065301197866412916385)
              ·
                rfl

theorem cell21_42012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 7].length) (baseStart_42012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42012 prefixEnd_42012 := by exact prefixLift 42012
  have htrace : WordTrace (prefixWord ++ tailWord_42012) baseStart_42012 baseEnd_42012 := by
    simpa [prefixWord, tailWord_42012, baseEnd_42012] using wordTrace_append hprefix tailTrace_42012
  have hstable : (prefixWord ++ tailWord_42012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42012).length < 2 ^ (prefixWord ++ tailWord_42012).sum := by decide
  have hdescent : baseEnd_42012 < baseStart_42012 := by decide
  rcases family_descends (prefixWord ++ tailWord_42012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42077 : List Nat := [1, 4, 4, 1, 2, 1, 1, 4, 3]
def baseStart_42077 : Nat := 118140960795 + 42077 * 2 ^ 59
def prefixEnd_42077 : Nat := 4983230072969 + 3 ^ 40 * 42077 * 2
def baseEnd_42077 : Nat := 9602544666372047663999

theorem tailTrace_42077 : CollatzResearch.WordTrace tailWord_42077 prefixEnd_42077 9602544666372047663999 := by
  unfold tailWord_42077
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534674268569690024588485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1023116179046460016392323 1534674268569690024588485)
  ·
    refine ⟨287751425356816879610341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1534674268569690024588485 287751425356816879610341)
    ·
      refine ⟨53953392254403164926939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287751425356816879610341 53953392254403164926939)
      ·
        refine ⟨80930088381604747390409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53953392254403164926939 80930088381604747390409)
        ·
          refine ⟨60697566286203560542807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80930088381604747390409 60697566286203560542807)
          ·
            refine ⟨91046349429305340814211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60697566286203560542807 91046349429305340814211)
            ·
              refine ⟨136569524143958011221317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91046349429305340814211 136569524143958011221317)
              ·
                refine ⟨25606785776992127103997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136569524143958011221317 25606785776992127103997)
                ·
                  refine ⟨9602544666372047663999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25606785776992127103997 9602544666372047663999)
                  ·
                    rfl

theorem cell21_42077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_42077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42077 prefixEnd_42077 := by exact prefixLift 42077
  have htrace : WordTrace (prefixWord ++ tailWord_42077) baseStart_42077 baseEnd_42077 := by
    simpa [prefixWord, tailWord_42077, baseEnd_42077] using wordTrace_append hprefix tailTrace_42077
  have hstable : (prefixWord ++ tailWord_42077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42077).length < 2 ^ (prefixWord ++ tailWord_42077).sum := by decide
  have hdescent : baseEnd_42077 < baseStart_42077 := by decide
  rcases family_descends (prefixWord ++ tailWord_42077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42209 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 4]
def baseStart_42209 : Nat := 118140960795 + 42209 * 2 ^ 59
def prefixEnd_42209 : Nat := 4983230072969 + 3 ^ 40 * 42209 * 2
def baseEnd_42209 : Nat := 9632668864769151463729

theorem tailTrace_42209 : CollatzResearch.WordTrace tailWord_42209 prefixEnd_42209 9632668864769151463729 := by
  unfold tailWord_42209
  simp only [CollatzResearch.WordTrace]
  refine ⟨1539488704091476568393681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1026325802727651045595787 1539488704091476568393681)
  ·
    refine ⟨1154616528068607426295261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1539488704091476568393681 1154616528068607426295261)
    ·
      refine ⟨432981198025727784860723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1154616528068607426295261 432981198025727784860723)
      ·
        refine ⟨649471797038591677291085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432981198025727784860723 649471797038591677291085)
        ·
          refine ⟨243551923889471878984157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 649471797038591677291085 243551923889471878984157)
          ·
            refine ⟨91331971458551954619059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243551923889471878984157 91331971458551954619059)
            ·
              refine ⟨136997957187827931928589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91331971458551954619059 136997957187827931928589)
              ·
                refine ⟨51374233945435474473221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136997957187827931928589 51374233945435474473221)
                ·
                  refine ⟨9632668864769151463729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51374233945435474473221 9632668864769151463729)
                  ·
                    rfl

theorem cell21_42209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_42209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42209 prefixEnd_42209 := by exact prefixLift 42209
  have htrace : WordTrace (prefixWord ++ tailWord_42209) baseStart_42209 baseEnd_42209 := by
    simpa [prefixWord, tailWord_42209, baseEnd_42209] using wordTrace_append hprefix tailTrace_42209
  have hstable : (prefixWord ++ tailWord_42209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42209).length < 2 ^ (prefixWord ++ tailWord_42209).sum := by decide
  have hdescent : baseEnd_42209 < baseStart_42209 := by decide
  rcases family_descends (prefixWord ++ tailWord_42209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42313 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 5]
def baseStart_42313 : Nat := 118140960795 + 42313 * 2 ^ 59
def prefixEnd_42313 : Nat := 4983230072969 + 3 ^ 40 * 42313 * 2
def baseEnd_42313 : Nat := 9656403081688081730183

theorem tailTrace_42313 : CollatzResearch.WordTrace tailWord_42313 prefixEnd_42313 9656403081688081730183 := by
  unfold tailWord_42313
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543281895714702330179593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1028854597143134886786395 1543281895714702330179593)
  ·
    refine ⟨1157461421786026747634695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1543281895714702330179593 1157461421786026747634695)
    ·
      refine ⟨1736192132679040121452043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1157461421786026747634695 1736192132679040121452043)
      ·
        refine ⟨2604288199018560182178065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736192132679040121452043 2604288199018560182178065)
        ·
          refine ⟨1953216149263920136633549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2604288199018560182178065 1953216149263920136633549)
          ·
            refine ⟨732456055973970051237581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1953216149263920136633549 732456055973970051237581)
            ·
              refine ⟨274671020990238769214093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 732456055973970051237581 274671020990238769214093)
              ·
                refine ⟨103001632871339538455285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274671020990238769214093 103001632871339538455285)
                ·
                  refine ⟨9656403081688081730183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103001632871339538455285 9656403081688081730183)
                  ·
                    rfl

theorem cell21_42313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_42313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42313 prefixEnd_42313 := by exact prefixLift 42313
  have htrace : WordTrace (prefixWord ++ tailWord_42313) baseStart_42313 baseEnd_42313 := by
    simpa [prefixWord, tailWord_42313, baseEnd_42313] using wordTrace_append hprefix tailTrace_42313
  have hstable : (prefixWord ++ tailWord_42313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42313).length < 2 ^ (prefixWord ++ tailWord_42313).sum := by decide
  have hdescent : baseEnd_42313 < baseStart_42313 := by decide
  rcases family_descends (prefixWord ++ tailWord_42313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42375 : List Nat := [1, 1, 4, 2, 2, 3, 2, 6]
def baseStart_42375 : Nat := 118140960795 + 42375 * 2 ^ 59
def prefixEnd_42375 : Nat := 4983230072969 + 3 ^ 40 * 42375 * 2
def baseEnd_42375 : Nat := 3223517442129917232241

theorem tailTrace_42375 : CollatzResearch.WordTrace tailWord_42375 prefixEnd_42375 3223517442129917232241 := by
  unfold tailWord_42375
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545543221490086918936579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1030362147660057945957719 1545543221490086918936579)
  ·
    refine ⟨2318314832235130378404869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1545543221490086918936579 2318314832235130378404869)
    ·
      refine ⟨434684031044086945950913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2318314832235130378404869 434684031044086945950913)
      ·
        refine ⟨326013023283065209463185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434684031044086945950913 326013023283065209463185)
        ·
          refine ⟨244509767462298907097389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326013023283065209463185 244509767462298907097389)
          ·
            refine ⟨91691162798362090161521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244509767462298907097389 91691162798362090161521)
            ·
              refine ⟨68768372098771567621141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91691162798362090161521 68768372098771567621141)
              ·
                refine ⟨3223517442129917232241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68768372098771567621141 3223517442129917232241)
                ·
                  rfl

theorem cell21_42375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 6].length) (baseStart_42375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42375 prefixEnd_42375 := by exact prefixLift 42375
  have htrace : WordTrace (prefixWord ++ tailWord_42375) baseStart_42375 baseEnd_42375 := by
    simpa [prefixWord, tailWord_42375, baseEnd_42375] using wordTrace_append hprefix tailTrace_42375
  have hstable : (prefixWord ++ tailWord_42375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42375).length < 2 ^ (prefixWord ++ tailWord_42375).sum := by decide
  have hdescent : baseEnd_42375 < baseStart_42375 := by decide
  rcases family_descends (prefixWord ++ tailWord_42375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42389 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 5]
def baseStart_42389 : Nat := 118140960795 + 42389 * 2 ^ 59
def prefixEnd_42389 : Nat := 4983230072969 + 3 ^ 40 * 42389 * 2
def baseEnd_42389 : Nat := 9673747317128838463361

theorem tailTrace_42389 : CollatzResearch.WordTrace tailWord_42389 prefixEnd_42389 9673747317128838463361 := by
  unfold tailWord_42389
  simp only [CollatzResearch.WordTrace]
  refine ⟨1546053843439367309946221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1030702562292911539964147 1546053843439367309946221)
  ·
    refine ⟨579770191289762741229833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1546053843439367309946221 579770191289762741229833)
    ·
      refine ⟨434827643467322055922375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 579770191289762741229833 434827643467322055922375)
      ·
        refine ⟨652241465200983083883563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434827643467322055922375 652241465200983083883563)
        ·
          refine ⟨978362197801474625825345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652241465200983083883563 978362197801474625825345)
          ·
            refine ⟨733771648351105969369009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978362197801474625825345 733771648351105969369009)
            ·
              refine ⟨550328736263329477026757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733771648351105969369009 550328736263329477026757)
              ·
                refine ⟨103186638049374276942517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 550328736263329477026757 103186638049374276942517)
                ·
                  refine ⟨9673747317128838463361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103186638049374276942517 9673747317128838463361)
                  ·
                    rfl

theorem cell21_42389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_42389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42389 prefixEnd_42389 := by exact prefixLift 42389
  have htrace : WordTrace (prefixWord ++ tailWord_42389) baseStart_42389 baseEnd_42389 := by
    simpa [prefixWord, tailWord_42389, baseEnd_42389] using wordTrace_append hprefix tailTrace_42389
  have hstable : (prefixWord ++ tailWord_42389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42389).length < 2 ^ (prefixWord ++ tailWord_42389).sum := by decide
  have hdescent : baseEnd_42389 < baseStart_42389 := by decide
  rcases family_descends (prefixWord ++ tailWord_42389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42482 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_42482 : Nat := 118140960795 + 42482 * 2 ^ 59
def prefixEnd_42482 : Nat := 4983230072969 + 3 ^ 40 * 42482 * 2
def baseEnd_42482 : Nat := 9694971184181343413171

theorem tailTrace_42482 : CollatzResearch.WordTrace tailWord_42482 prefixEnd_42482 9694971184181343413171 := by
  unfold tailWord_42482
  simp only [CollatzResearch.WordTrace]
  refine ⟨387361458025611048270425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1032963888068296128721133 387361458025611048270425)
  ·
    refine ⟨290521093519208286202819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 387361458025611048270425 290521093519208286202819)
    ·
      refine ⟨435781640278812429304229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290521093519208286202819 435781640278812429304229)
      ·
        refine ⟨81709057552277330494543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 435781640278812429304229 81709057552277330494543)
        ·
          refine ⟨122563586328415995741815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81709057552277330494543 122563586328415995741815)
          ·
            refine ⟨183845379492623993612723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122563586328415995741815 183845379492623993612723)
            ·
              refine ⟨275768069238935990419085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183845379492623993612723 275768069238935990419085)
              ·
                refine ⟨103413025964600996407157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275768069238935990419085 103413025964600996407157)
                ·
                  refine ⟨9694971184181343413171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103413025964600996407157 9694971184181343413171)
                  ·
                    rfl

theorem cell21_42482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_42482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42482 prefixEnd_42482 := by exact prefixLift 42482
  have htrace : WordTrace (prefixWord ++ tailWord_42482) baseStart_42482 baseEnd_42482 := by
    simpa [prefixWord, tailWord_42482, baseEnd_42482] using wordTrace_append hprefix tailTrace_42482
  have hstable : (prefixWord ++ tailWord_42482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42482).length < 2 ^ (prefixWord ++ tailWord_42482).sum := by decide
  have hdescent : baseEnd_42482 < baseStart_42482 := by decide
  rcases family_descends (prefixWord ++ tailWord_42482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42502 : List Nat := [6, 2, 1, 1, 2, 1, 1, 7]
def baseStart_42502 : Nat := 118140960795 + 42502 * 2 ^ 59
def prefixEnd_42502 : Nat := 4983230072969 + 3 ^ 40 * 42502 * 2
def baseEnd_42502 : Nat := 3233178485555251026599

theorem tailTrace_42502 : CollatzResearch.WordTrace tailWord_42502 prefixEnd_42502 3233178485555251026599 := by
  unfold tailWord_42502
  simp only [CollatzResearch.WordTrace]
  refine ⟨48442977875937112775305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1033450194686658405873173 48442977875937112775305)
  ·
    refine ⟨36332233406952834581479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48442977875937112775305 36332233406952834581479)
    ·
      refine ⟨54498350110429251872219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36332233406952834581479 54498350110429251872219)
      ·
        refine ⟨81747525165643877808329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54498350110429251872219 81747525165643877808329)
        ·
          refine ⟨61310643874232908356247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81747525165643877808329 61310643874232908356247)
          ·
            refine ⟨91965965811349362534371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61310643874232908356247 91965965811349362534371)
            ·
              refine ⟨137948948717024043801557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91965965811349362534371 137948948717024043801557)
              ·
                refine ⟨3233178485555251026599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 137948948717024043801557 3233178485555251026599)
                ·
                  rfl

theorem cell21_42502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_42502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42502 prefixEnd_42502 := by exact prefixLift 42502
  have htrace : WordTrace (prefixWord ++ tailWord_42502) baseStart_42502 baseEnd_42502 := by
    simpa [prefixWord, tailWord_42502, baseEnd_42502] using wordTrace_append hprefix tailTrace_42502
  have hstable : (prefixWord ++ tailWord_42502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42502).length < 2 ^ (prefixWord ++ tailWord_42502).sum := by decide
  have hdescent : baseEnd_42502 < baseStart_42502 := by decide
  rcases family_descends (prefixWord ++ tailWord_42502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42617 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 5]
def baseStart_42617 : Nat := 118140960795 + 42617 * 2 ^ 59
def prefixEnd_42617 : Nat := 4983230072969 + 3 ^ 40 * 42617 * 2
def baseEnd_42617 : Nat := 9725780023451108662895

theorem tailTrace_42617 : CollatzResearch.WordTrace tailWord_42617 prefixEnd_42617 9725780023451108662895 := by
  unfold tailWord_42617
  simp only [CollatzResearch.WordTrace]
  refine ⟨1554369686613362249246105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1036246457742241499497403 1554369686613362249246105)
  ·
    refine ⟨1165777264960021686934579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1554369686613362249246105 1165777264960021686934579)
    ·
      refine ⟨1748665897440032530401869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1165777264960021686934579 1748665897440032530401869)
      ·
        refine ⟨655749711540012198900701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1748665897440032530401869 655749711540012198900701)
        ·
          refine ⟨245906141827504574587763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 655749711540012198900701 245906141827504574587763)
          ·
            refine ⟨368859212741256861881645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245906141827504574587763 368859212741256861881645)
            ·
              refine ⟨138322204777971323205617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 368859212741256861881645 138322204777971323205617)
              ·
                refine ⟨103741653583478492404213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138322204777971323205617 103741653583478492404213)
                ·
                  refine ⟨9725780023451108662895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103741653583478492404213 9725780023451108662895)
                  ·
                    rfl

theorem cell21_42617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_42617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42617 prefixEnd_42617 := by exact prefixLift 42617
  have htrace : WordTrace (prefixWord ++ tailWord_42617) baseStart_42617 baseEnd_42617 := by
    simpa [prefixWord, tailWord_42617, baseEnd_42617] using wordTrace_append hprefix tailTrace_42617
  have hstable : (prefixWord ++ tailWord_42617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42617).length < 2 ^ (prefixWord ++ tailWord_42617).sum := by decide
  have hdescent : baseEnd_42617 < baseStart_42617 := by decide
  rcases family_descends (prefixWord ++ tailWord_42617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42648 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 6]
def baseStart_42648 : Nat := 118140960795 + 42648 * 2 ^ 59
def prefixEnd_42648 : Nat := 4983230072969 + 3 ^ 40 * 42648 * 2
def baseEnd_42648 : Nat := 9732854645801943646165

theorem tailTrace_42648 : CollatzResearch.WordTrace tailWord_42648 prefixEnd_42648 9732854645801943646165 := by
  unfold tailWord_42648
  simp only [CollatzResearch.WordTrace]
  refine ⟨777750174750527271812299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1037000233000703029083065 777750174750527271812299)
  ·
    refine ⟨1166625262125790907718449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 777750174750527271812299 1166625262125790907718449)
    ·
      refine ⟨874968946594343180788837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1166625262125790907718449 874968946594343180788837)
      ·
        refine ⟨164056677486439346397907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 874968946594343180788837 164056677486439346397907)
        ·
          refine ⟨246085016229659019596861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164056677486439346397907 246085016229659019596861)
          ·
            refine ⟨92281881086122132348823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246085016229659019596861 92281881086122132348823)
            ·
              refine ⟨138422821629183198523235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92281881086122132348823 138422821629183198523235)
              ·
                refine ⟨207634232443774797784853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138422821629183198523235 207634232443774797784853)
                ·
                  refine ⟨9732854645801943646165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 207634232443774797784853 9732854645801943646165)
                  ·
                    rfl

theorem cell21_42648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_42648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42648 prefixEnd_42648 := by exact prefixLift 42648
  have htrace : WordTrace (prefixWord ++ tailWord_42648) baseStart_42648 baseEnd_42648 := by
    simpa [prefixWord, tailWord_42648, baseEnd_42648] using wordTrace_append hprefix tailTrace_42648
  have hstable : (prefixWord ++ tailWord_42648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42648).length < 2 ^ (prefixWord ++ tailWord_42648).sum := by decide
  have hdescent : baseEnd_42648 < baseStart_42648 := by decide
  rcases family_descends (prefixWord ++ tailWord_42648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42679 : List Nat := [1, 1, 3, 1, 5, 1, 4, 5]
def baseStart_42679 : Nat := 118140960795 + 42679 * 2 ^ 59
def prefixEnd_42679 : Nat := 4983230072969 + 3 ^ 40 * 42679 * 2
def baseEnd_42679 : Nat := 3246643089384259543145

theorem tailTrace_42679 : CollatzResearch.WordTrace tailWord_42679 prefixEnd_42679 3246643089384259543145 := by
  unfold tailWord_42679
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556631012388746838003091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1037754008259164558668727 1556631012388746838003091)
  ·
    refine ⟨2334946518583120257004637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1556631012388746838003091 2334946518583120257004637)
    ·
      refine ⟨875604944468670096376739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2334946518583120257004637 875604944468670096376739)
      ·
        refine ⟨1313407416703005144565109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 875604944468670096376739 1313407416703005144565109)
        ·
          refine ⟨123131945315906732302979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1313407416703005144565109 123131945315906732302979)
          ·
            refine ⟨184697917973860098454469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123131945315906732302979 184697917973860098454469)
            ·
              refine ⟨34630859620098768460213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184697917973860098454469 34630859620098768460213)
              ·
                refine ⟨3246643089384259543145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34630859620098768460213 3246643089384259543145)
                ·
                  rfl

theorem cell21_42679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 5].length) (baseStart_42679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42679 prefixEnd_42679 := by exact prefixLift 42679
  have htrace : WordTrace (prefixWord ++ tailWord_42679) baseStart_42679 baseEnd_42679 := by
    simpa [prefixWord, tailWord_42679, baseEnd_42679] using wordTrace_append hprefix tailTrace_42679
  have hstable : (prefixWord ++ tailWord_42679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42679).length < 2 ^ (prefixWord ++ tailWord_42679).sum := by decide
  have hdescent : baseEnd_42679 < baseStart_42679 := by decide
  rcases family_descends (prefixWord ++ tailWord_42679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42716 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 4]
def baseStart_42716 : Nat := 118140960795 + 42716 * 2 ^ 59
def prefixEnd_42716 : Nat := 4983230072969 + 3 ^ 40 * 42716 * 2
def baseEnd_42716 : Nat := 9748373172248936512693

theorem tailTrace_42716 : CollatzResearch.WordTrace tailWord_42716 prefixEnd_42716 9748373172248936512693 := by
  unfold tailWord_42716
  simp only [CollatzResearch.WordTrace]
  refine ⟨778990256627351078550001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1038653675503134771400001 778990256627351078550001)
  ·
    refine ⟨584242692470513308912501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 778990256627351078550001 584242692470513308912501)
    ·
      refine ⟨54772752419110622710547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 584242692470513308912501 54772752419110622710547)
      ·
        refine ⟨82159128628665934065821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54772752419110622710547 82159128628665934065821)
        ·
          refine ⟨30809673235749725274683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82159128628665934065821 30809673235749725274683)
          ·
            refine ⟨46214509853624587912025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30809673235749725274683 46214509853624587912025)
            ·
              refine ⟨34660882390218440934019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46214509853624587912025 34660882390218440934019)
              ·
                refine ⟨51991323585327661401029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34660882390218440934019 51991323585327661401029)
                ·
                  refine ⟨9748373172248936512693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51991323585327661401029 9748373172248936512693)
                  ·
                    rfl

theorem cell21_42716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_42716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42716 prefixEnd_42716 := by exact prefixLift 42716
  have htrace : WordTrace (prefixWord ++ tailWord_42716) baseStart_42716 baseEnd_42716 := by
    simpa [prefixWord, tailWord_42716, baseEnd_42716] using wordTrace_append hprefix tailTrace_42716
  have hstable : (prefixWord ++ tailWord_42716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42716).length < 2 ^ (prefixWord ++ tailWord_42716).sum := by decide
  have hdescent : baseEnd_42716 < baseStart_42716 := by decide
  rcases family_descends (prefixWord ++ tailWord_42716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42724 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 4]
def baseStart_42724 : Nat := 118140960795 + 42724 * 2 ^ 59
def prefixEnd_42724 : Nat := 4983230072969 + 3 ^ 40 * 42724 * 2
def baseEnd_42724 : Nat := 9750198881242700379343

theorem tailTrace_42724 : CollatzResearch.WordTrace tailWord_42724 prefixEnd_42724 9750198881242700379343 := by
  unfold tailWord_42724
  simp only [CollatzResearch.WordTrace]
  refine ⟨779136148612859761695613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1038848198150479682260817 779136148612859761695613)
  ·
    refine ⟨292176055729822410635855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 779136148612859761695613 292176055729822410635855)
    ·
      refine ⟨438264083594733615953783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292176055729822410635855 438264083594733615953783)
      ·
        refine ⟨657396125392100423930675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438264083594733615953783 657396125392100423930675)
        ·
          refine ⟨986094188088150635896013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657396125392100423930675 986094188088150635896013)
          ·
            refine ⟨369785320533056488461005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 986094188088150635896013 369785320533056488461005)
            ·
              refine ⟨138669495199896183172877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369785320533056488461005 138669495199896183172877)
              ·
                refine ⟨52001060699961068689829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138669495199896183172877 52001060699961068689829)
                ·
                  refine ⟨9750198881242700379343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52001060699961068689829 9750198881242700379343)
                  ·
                    rfl

theorem cell21_42724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_42724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42724 prefixEnd_42724 := by exact prefixLift 42724
  have htrace : WordTrace (prefixWord ++ tailWord_42724) baseStart_42724 baseEnd_42724 := by
    simpa [prefixWord, tailWord_42724, baseEnd_42724] using wordTrace_append hprefix tailTrace_42724
  have hstable : (prefixWord ++ tailWord_42724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42724).length < 2 ^ (prefixWord ++ tailWord_42724).sum := by decide
  have hdescent : baseEnd_42724 < baseStart_42724 := by decide
  rcases family_descends (prefixWord ++ tailWord_42724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42738 : List Nat := [3, 2, 1, 3, 1, 1, 1, 9]
def baseStart_42738 : Nat := 118140960795 + 42738 * 2 ^ 59
def prefixEnd_42738 : Nat := 4983230072969 + 3 ^ 40 * 42738 * 2
def baseEnd_42738 : Nat := 3251131290660595715327

theorem tailTrace_42738 : CollatzResearch.WordTrace tailWord_42738 prefixEnd_42738 3251131290660595715327 := by
  unfold tailWord_42738
  simp only [CollatzResearch.WordTrace]
  refine ⟨389695729793749978600217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1039188612783333276267245 389695729793749978600217)
  ·
    refine ⟨292271797345312483950163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 389695729793749978600217 292271797345312483950163)
    ·
      refine ⟨438407696017968725925245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292271797345312483950163 438407696017968725925245)
      ·
        refine ⟨164402886006738272221967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438407696017968725925245 164402886006738272221967)
        ·
          refine ⟨246604329010107408332951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164402886006738272221967 246604329010107408332951)
          ·
            refine ⟨369906493515161112499427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246604329010107408332951 369906493515161112499427)
            ·
              refine ⟨554859740272741668749141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369906493515161112499427 554859740272741668749141)
              ·
                refine ⟨3251131290660595715327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 554859740272741668749141 3251131290660595715327)
                ·
                  rfl

theorem cell21_42738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_42738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42738 prefixEnd_42738 := by exact prefixLift 42738
  have htrace : WordTrace (prefixWord ++ tailWord_42738) baseStart_42738 baseEnd_42738 := by
    simpa [prefixWord, tailWord_42738, baseEnd_42738] using wordTrace_append hprefix tailTrace_42738
  have hstable : (prefixWord ++ tailWord_42738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42738).length < 2 ^ (prefixWord ++ tailWord_42738).sum := by decide
  have hdescent : baseEnd_42738 < baseStart_42738 := by decide
  rcases family_descends (prefixWord ++ tailWord_42738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42752 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_42752 : Nat := 118140960795 + 42752 * 2 ^ 59
def prefixEnd_42752 : Nat := 4983230072969 + 3 ^ 40 * 42752 * 2
def baseEnd_42752 : Nat := 9756588862720873912619

theorem tailTrace_42752 : CollatzResearch.WordTrace tailWord_42752 prefixEnd_42752 9756588862720873912619 := by
  unfold tailWord_42752
  simp only [CollatzResearch.WordTrace]
  refine ⟨779646770562140152705255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1039529027416186870273673 779646770562140152705255)
  ·
    refine ⟨1169470155843210229057883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 779646770562140152705255 1169470155843210229057883)
    ·
      refine ⟨1754205233764815343586825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1169470155843210229057883 1754205233764815343586825)
      ·
        refine ⟨1315653925323611507690119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1754205233764815343586825 1315653925323611507690119)
        ·
          refine ⟨1973480887985417261535179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315653925323611507690119 1973480887985417261535179)
          ·
            refine ⟨2960221331978125892302769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973480887985417261535179 2960221331978125892302769)
            ·
              refine ⟨2220165998983594419227077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2960221331978125892302769 2220165998983594419227077)
              ·
                refine ⟨416281124809423953605077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2220165998983594419227077 416281124809423953605077)
                ·
                  refine ⟨9756588862720873912619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 416281124809423953605077 9756588862720873912619)
                  ·
                    rfl

theorem cell21_42752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_42752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42752 prefixEnd_42752 := by exact prefixLift 42752
  have htrace : WordTrace (prefixWord ++ tailWord_42752) baseStart_42752 baseEnd_42752 := by
    simpa [prefixWord, tailWord_42752, baseEnd_42752] using wordTrace_append hprefix tailTrace_42752
  have hstable : (prefixWord ++ tailWord_42752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42752).length < 2 ^ (prefixWord ++ tailWord_42752).sum := by decide
  have hdescent : baseEnd_42752 < baseStart_42752 := by decide
  rcases family_descends (prefixWord ++ tailWord_42752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42803 : List Nat := [1, 1, 1, 2, 7, 1, 2, 3, 3]
def baseStart_42803 : Nat := 118140960795 + 42803 * 2 ^ 59
def prefixEnd_42803 : Nat := 4983230072969 + 3 ^ 40 * 42803 * 2
def baseEnd_42803 : Nat := 9768227757556118562515

theorem tailTrace_42803 : CollatzResearch.WordTrace tailWord_42803 prefixEnd_42803 9768227757556118562515 := by
  unfold tailWord_42803
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561153663939516015517063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1040769109293010677011375 1561153663939516015517063)
  ·
    refine ⟨2341730495909274023275595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1561153663939516015517063 2341730495909274023275595)
    ·
      refine ⟨3512595743863911034913393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2341730495909274023275595 3512595743863911034913393)
      ·
        refine ⟨2634446807897933276185045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3512595743863911034913393 2634446807897933276185045)
        ·
          refine ⟨61744847060107811160587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2634446807897933276185045 61744847060107811160587)
          ·
            refine ⟨92617270590161716740881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61744847060107811160587 92617270590161716740881)
            ·
              refine ⟨69462952942621287555661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92617270590161716740881 69462952942621287555661)
              ·
                refine ⟨26048607353482982833373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69462952942621287555661 26048607353482982833373)
                ·
                  refine ⟨9768227757556118562515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26048607353482982833373 9768227757556118562515)
                  ·
                    rfl

theorem cell21_42803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 3].length) (baseStart_42803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42803 prefixEnd_42803 := by exact prefixLift 42803
  have htrace : WordTrace (prefixWord ++ tailWord_42803) baseStart_42803 baseEnd_42803 := by
    simpa [prefixWord, tailWord_42803, baseEnd_42803] using wordTrace_append hprefix tailTrace_42803
  have hstable : (prefixWord ++ tailWord_42803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42803).length < 2 ^ (prefixWord ++ tailWord_42803).sum := by decide
  have hdescent : baseEnd_42803 < baseStart_42803 := by decide
  rcases family_descends (prefixWord ++ tailWord_42803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42949 : List Nat := [1, 3, 1, 1, 1, 1, 1, 12]
def baseStart_42949 : Nat := 118140960795 + 42949 * 2 ^ 59
def prefixEnd_42949 : Nat := 4983230072969 + 3 ^ 40 * 42949 * 2
def baseEnd_42949 : Nat := 3267182315564103042961

theorem tailTrace_42949 : CollatzResearch.WordTrace tailWord_42949 prefixEnd_42949 3267182315564103042961 := by
  unfold tailWord_42949
  simp only [CollatzResearch.WordTrace]
  refine ⟨1566478721410582950331901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1044319147607055300221267 1566478721410582950331901)
  ·
    refine ⟨587429520528968606374463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1566478721410582950331901 587429520528968606374463)
    ·
      refine ⟨881144280793452909561695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 587429520528968606374463 881144280793452909561695)
      ·
        refine ⟨1321716421190179364342543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881144280793452909561695 1321716421190179364342543)
        ·
          refine ⟨1982574631785269046513815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321716421190179364342543 1982574631785269046513815)
          ·
            refine ⟨2973861947677903569770723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982574631785269046513815 2973861947677903569770723)
            ·
              refine ⟨4460792921516855354656085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973861947677903569770723 4460792921516855354656085)
              ·
                refine ⟨3267182315564103042961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 4460792921516855354656085 3267182315564103042961)
                ·
                  rfl

theorem cell21_42949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 12].length) (baseStart_42949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42949 prefixEnd_42949 := by exact prefixLift 42949
  have htrace : WordTrace (prefixWord ++ tailWord_42949) baseStart_42949 baseEnd_42949 := by
    simpa [prefixWord, tailWord_42949, baseEnd_42949] using wordTrace_append hprefix tailTrace_42949
  have hstable : (prefixWord ++ tailWord_42949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42949).length < 2 ^ (prefixWord ++ tailWord_42949).sum := by decide
  have hdescent : baseEnd_42949 < baseStart_42949 := by decide
  rcases family_descends (prefixWord ++ tailWord_42949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42952 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 4]
def baseStart_42952 : Nat := 118140960795 + 42952 * 2 ^ 59
def prefixEnd_42952 : Nat := 4983230072969 + 3 ^ 40 * 42952 * 2
def baseEnd_42952 : Nat := 9802231587564970578877

theorem tailTrace_42952 : CollatzResearch.WordTrace tailWord_42952 prefixEnd_42952 9802231587564970578877 := by
  unfold tailWord_42952
  simp only [CollatzResearch.WordTrace]
  refine ⟨783294070199857231345555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1044392093599809641794073 783294070199857231345555)
  ·
    refine ⟨1174941105299785847018333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 783294070199857231345555 1174941105299785847018333)
    ·
      refine ⟨440602914487419692631875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1174941105299785847018333 440602914487419692631875)
      ·
        refine ⟨660904371731129538947813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440602914487419692631875 660904371731129538947813)
        ·
          refine ⟨123919569699586788552715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 660904371731129538947813 123919569699586788552715)
          ·
            refine ⟨185879354549380182829073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123919569699586788552715 185879354549380182829073)
            ·
              refine ⟨139409515912035137121805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185879354549380182829073 139409515912035137121805)
              ·
                refine ⟨52278568467013176420677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139409515912035137121805 52278568467013176420677)
                ·
                  refine ⟨9802231587564970578877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52278568467013176420677 9802231587564970578877)
                  ·
                    rfl

theorem cell21_42952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_42952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42952 prefixEnd_42952 := by exact prefixLift 42952
  have htrace : WordTrace (prefixWord ++ tailWord_42952) baseStart_42952 baseEnd_42952 := by
    simpa [prefixWord, tailWord_42952, baseEnd_42952] using wordTrace_append hprefix tailTrace_42952
  have hstable : (prefixWord ++ tailWord_42952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42952).length < 2 ^ (prefixWord ++ tailWord_42952).sum := by decide
  have hdescent : baseEnd_42952 < baseStart_42952 := by decide
  rcases family_descends (prefixWord ++ tailWord_42952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42980 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_42980 : Nat := 118140960795 + 42980 * 2 ^ 59
def prefixEnd_42980 : Nat := 4983230072969 + 3 ^ 40 * 42980 * 2
def baseEnd_42980 : Nat := 9808621569043144112153

theorem tailTrace_42980 : CollatzResearch.WordTrace tailWord_42980 prefixEnd_42980 9808621569043144112153 := by
  unfold tailWord_42980
  simp only [CollatzResearch.WordTrace]
  refine ⟨783804692149137622355197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1045072922865516829806929 783804692149137622355197)
  ·
    refine ⟨293926759555926608383199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 783804692149137622355197 293926759555926608383199)
    ·
      refine ⟨440890139333889912574799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293926759555926608383199 440890139333889912574799)
      ·
        refine ⟨661335209000834868862199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440890139333889912574799 661335209000834868862199)
        ·
          refine ⟨992002813501252303293299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661335209000834868862199 992002813501252303293299)
          ·
            refine ⟨1488004220251878454939949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992002813501252303293299 1488004220251878454939949)
            ·
              refine ⟨558001582594454420602481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1488004220251878454939949 558001582594454420602481)
              ·
                refine ⟨418501186945840815451861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558001582594454420602481 418501186945840815451861)
                ·
                  refine ⟨9808621569043144112153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 418501186945840815451861 9808621569043144112153)
                  ·
                    rfl

theorem cell21_42980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_42980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_42980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_42980 prefixEnd_42980 := by exact prefixLift 42980
  have htrace : WordTrace (prefixWord ++ tailWord_42980) baseStart_42980 baseEnd_42980 := by
    simpa [prefixWord, tailWord_42980, baseEnd_42980] using wordTrace_append hprefix tailTrace_42980
  have hstable : (prefixWord ++ tailWord_42980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42980).length < 2 ^ (prefixWord ++ tailWord_42980).sum := by decide
  have hdescent : baseEnd_42980 < baseStart_42980 := by decide
  rcases family_descends (prefixWord ++ tailWord_42980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43011 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 4]
def baseStart_43011 : Nat := 118140960795 + 43011 * 2 ^ 59
def prefixEnd_43011 : Nat := 4983230072969 + 3 ^ 40 * 43011 * 2
def baseEnd_43011 : Nat := 9815696191393979095423

theorem tailTrace_43011 : CollatzResearch.WordTrace tailWord_43011 prefixEnd_43011 9815696191393979095423 := by
  unfold tailWord_43011
  simp only [CollatzResearch.WordTrace]
  refine ⟨1568740047185967539088887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1045826698123978359392591 1568740047185967539088887)
  ·
    refine ⟨2353110070778951308633331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1568740047185967539088887 2353110070778951308633331)
    ·
      refine ⟨3529665106168426962949997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2353110070778951308633331 3529665106168426962949997)
      ·
        refine ⟨1323624414813160111106249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3529665106168426962949997 1323624414813160111106249)
        ·
          refine ⟨992718311109870083329687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1323624414813160111106249 992718311109870083329687)
          ·
            refine ⟨1489077466664805124994531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992718311109870083329687 1489077466664805124994531)
            ·
              refine ⟨2233616199997207687491797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489077466664805124994531 2233616199997207687491797)
              ·
                refine ⟨52350379687434555175589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2233616199997207687491797 52350379687434555175589)
                ·
                  refine ⟨9815696191393979095423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52350379687434555175589 9815696191393979095423)
                  ·
                    rfl

theorem cell21_43011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 4].length) (baseStart_43011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43011 prefixEnd_43011 := by exact prefixLift 43011
  have htrace : WordTrace (prefixWord ++ tailWord_43011) baseStart_43011 baseEnd_43011 := by
    simpa [prefixWord, tailWord_43011, baseEnd_43011] using wordTrace_append hprefix tailTrace_43011
  have hstable : (prefixWord ++ tailWord_43011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43011).length < 2 ^ (prefixWord ++ tailWord_43011).sum := by decide
  have hdescent : baseEnd_43011 < baseStart_43011 := by decide
  rcases family_descends (prefixWord ++ tailWord_43011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43048 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 5]
def baseStart_43048 : Nat := 118140960795 + 43048 * 2 ^ 59
def prefixEnd_43048 : Nat := 4983230072969 + 3 ^ 40 * 43048 * 2
def baseEnd_43048 : Nat := 9824140095490136978681

theorem tailTrace_43048 : CollatzResearch.WordTrace tailWord_43048 prefixEnd_43048 9824140095490136978681 := by
  unfold tailWord_43048
  simp only [CollatzResearch.WordTrace]
  refine ⟨785044774025961429092899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1046726365367948572123865 785044774025961429092899)
  ·
    refine ⟨1177567161038942143639349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 785044774025961429092899 1177567161038942143639349)
    ·
      refine ⟨110396921347400825966189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1177567161038942143639349 110396921347400825966189)
      ·
        refine ⟨41398845505275309737321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110396921347400825966189 41398845505275309737321)
        ·
          refine ⟨31049134128956482302991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41398845505275309737321 31049134128956482302991)
          ·
            refine ⟨46573701193434723454487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31049134128956482302991 46573701193434723454487)
            ·
              refine ⟨69860551790152085181731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46573701193434723454487 69860551790152085181731)
              ·
                refine ⟨104790827685228127772597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69860551790152085181731 104790827685228127772597)
                ·
                  refine ⟨9824140095490136978681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104790827685228127772597 9824140095490136978681)
                  ·
                    rfl

theorem cell21_43048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 5].length) (baseStart_43048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43048 prefixEnd_43048 := by exact prefixLift 43048
  have htrace : WordTrace (prefixWord ++ tailWord_43048) baseStart_43048 baseEnd_43048 := by
    simpa [prefixWord, tailWord_43048, baseEnd_43048] using wordTrace_append hprefix tailTrace_43048
  have hstable : (prefixWord ++ tailWord_43048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43048).length < 2 ^ (prefixWord ++ tailWord_43048).sum := by decide
  have hdescent : baseEnd_43048 < baseStart_43048 := by decide
  rcases family_descends (prefixWord ++ tailWord_43048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43104 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 4]
def baseStart_43104 : Nat := 118140960795 + 43104 * 2 ^ 59
def prefixEnd_43104 : Nat := 4983230072969 + 3 ^ 40 * 43104 * 2
def baseEnd_43104 : Nat := 9836920058446484045233

theorem tailTrace_43104 : CollatzResearch.WordTrace tailWord_43104 prefixEnd_43104 9836920058446484045233 := by
  unfold tailWord_43104
  simp only [CollatzResearch.WordTrace]
  refine ⟨786066017924522211112183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1048088023899362948149577 786066017924522211112183)
  ·
    refine ⟨1179099026886783316668275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 786066017924522211112183 1179099026886783316668275)
    ·
      refine ⟨1768648540330174975002413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1179099026886783316668275 1768648540330174975002413)
      ·
        refine ⟨663243202623815615625905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1768648540330174975002413 663243202623815615625905)
        ·
          refine ⟨497432401967861711719429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663243202623815615625905 497432401967861711719429)
          ·
            refine ⟨93268575368974070947393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 497432401967861711719429 93268575368974070947393)
            ·
              refine ⟨69951431526730553210545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93268575368974070947393 69951431526730553210545)
              ·
                refine ⟨52463573645047914907909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69951431526730553210545 52463573645047914907909)
                ·
                  refine ⟨9836920058446484045233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52463573645047914907909 9836920058446484045233)
                  ·
                    rfl

theorem cell21_43104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_43104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43104 prefixEnd_43104 := by exact prefixLift 43104
  have htrace : WordTrace (prefixWord ++ tailWord_43104) baseStart_43104 baseEnd_43104 := by
    simpa [prefixWord, tailWord_43104, baseEnd_43104] using wordTrace_append hprefix tailTrace_43104
  have hstable : (prefixWord ++ tailWord_43104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43104).length < 2 ^ (prefixWord ++ tailWord_43104).sum := by decide
  have hdescent : baseEnd_43104 < baseStart_43104 := by decide
  rcases family_descends (prefixWord ++ tailWord_43104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43132 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_43132 : Nat := 118140960795 + 43132 * 2 ^ 59
def prefixEnd_43132 : Nat := 4983230072969 + 3 ^ 40 * 43132 * 2
def baseEnd_43132 : Nat := 9843310039924657578509

theorem tailTrace_43132 : CollatzResearch.WordTrace tailWord_43132 prefixEnd_43132 9843310039924657578509 := by
  unfold tailWord_43132
  simp only [CollatzResearch.WordTrace]
  refine ⟨786576639873802602121825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1048768853165070136162433 786576639873802602121825)
  ·
    refine ⟨589932479905351951591369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 786576639873802602121825 589932479905351951591369)
    ·
      refine ⟨442449359929013963693527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 589932479905351951591369 442449359929013963693527)
      ·
        refine ⟨663674039893520945540291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442449359929013963693527 663674039893520945540291)
        ·
          refine ⟨995511059840281418310437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663674039893520945540291 995511059840281418310437)
          ·
            refine ⟨186658323720052765933207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 995511059840281418310437 186658323720052765933207)
            ·
              refine ⟨279987485580079148899811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186658323720052765933207 279987485580079148899811)
              ·
                refine ⟨419981228370118723349717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279987485580079148899811 419981228370118723349717)
                ·
                  refine ⟨9843310039924657578509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 419981228370118723349717 9843310039924657578509)
                  ·
                    rfl

theorem cell21_43132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_43132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43132 prefixEnd_43132 := by exact prefixLift 43132
  have htrace : WordTrace (prefixWord ++ tailWord_43132) baseStart_43132 baseEnd_43132 := by
    simpa [prefixWord, tailWord_43132, baseEnd_43132] using wordTrace_append hprefix tailTrace_43132
  have hstable : (prefixWord ++ tailWord_43132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43132).length < 2 ^ (prefixWord ++ tailWord_43132).sum := by decide
  have hdescent : baseEnd_43132 < baseStart_43132 := by decide
  rcases family_descends (prefixWord ++ tailWord_43132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43194 : List Nat := [3, 1, 1, 1, 2, 2, 6, 5]
def baseStart_43194 : Nat := 118140960795 + 43194 * 2 ^ 59
def prefixEnd_43194 : Nat := 4983230072969 + 3 ^ 40 * 43194 * 2
def baseEnd_43194 : Nat := 3285819761542109181683

theorem tailTrace_43194 : CollatzResearch.WordTrace tailWord_43194 prefixEnd_43194 3285819761542109181683 := by
  unfold tailWord_43194
  simp only [CollatzResearch.WordTrace]
  refine ⟨393853651380747448250159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1050276403681993195333757 393853651380747448250159)
  ·
    refine ⟨590780477071121172375239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 393853651380747448250159 590780477071121172375239)
    ·
      refine ⟨886170715606681758562859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590780477071121172375239 886170715606681758562859)
      ·
        refine ⟨1329256073410022637844289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886170715606681758562859 1329256073410022637844289)
        ·
          refine ⟨996942055057516978383217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1329256073410022637844289 996942055057516978383217)
          ·
            refine ⟨747706541293137733787413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 996942055057516978383217 747706541293137733787413)
            ·
              refine ⟨35048744123115831271285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 747706541293137733787413 35048744123115831271285)
              ·
                refine ⟨3285819761542109181683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35048744123115831271285 3285819761542109181683)
                ·
                  rfl

theorem cell21_43194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_43194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43194 prefixEnd_43194 := by exact prefixLift 43194
  have htrace : WordTrace (prefixWord ++ tailWord_43194) baseStart_43194 baseEnd_43194 := by
    simpa [prefixWord, tailWord_43194, baseEnd_43194] using wordTrace_append hprefix tailTrace_43194
  have hstable : (prefixWord ++ tailWord_43194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43194).length < 2 ^ (prefixWord ++ tailWord_43194).sum := by decide
  have hdescent : baseEnd_43194 < baseStart_43194 := by decide
  rcases family_descends (prefixWord ++ tailWord_43194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43225 : List Nat := [1, 2, 1, 2, 3, 1, 2, 6, 3]
def baseStart_43225 : Nat := 118140960795 + 43225 * 2 ^ 59
def prefixEnd_43225 : Nat := 4983230072969 + 3 ^ 40 * 43225 * 2
def baseEnd_43225 : Nat := 9864533906977162528319

theorem tailTrace_43225 : CollatzResearch.WordTrace tailWord_43225 prefixEnd_43225 9864533906977162528319 := by
  unfold tailWord_43225
  simp only [CollatzResearch.WordTrace]
  refine ⟨1576545268410682087379129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1051030178940454724919419 1576545268410682087379129)
  ·
    refine ⟨1182408951308011565534347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1576545268410682087379129 1182408951308011565534347)
    ·
      refine ⟨1773613426962017348301521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1182408951308011565534347 1773613426962017348301521)
      ·
        refine ⟨1330210070221513011226141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1773613426962017348301521 1330210070221513011226141)
        ·
          refine ⟨498828776333067379209803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1330210070221513011226141 498828776333067379209803)
          ·
            refine ⟨748243164499601068814705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498828776333067379209803 748243164499601068814705)
            ·
              refine ⟨561182373374700801611029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748243164499601068814705 561182373374700801611029)
              ·
                refine ⟨26305423751939100075517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 561182373374700801611029 26305423751939100075517)
                ·
                  refine ⟨9864533906977162528319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26305423751939100075517 9864533906977162528319)
                  ·
                    rfl

theorem cell21_43225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 3].length) (baseStart_43225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43225 prefixEnd_43225 := by exact prefixLift 43225
  have htrace : WordTrace (prefixWord ++ tailWord_43225) baseStart_43225 baseEnd_43225 := by
    simpa [prefixWord, tailWord_43225, baseEnd_43225] using wordTrace_append hprefix tailTrace_43225
  have hstable : (prefixWord ++ tailWord_43225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43225).length < 2 ^ (prefixWord ++ tailWord_43225).sum := by decide
  have hdescent : baseEnd_43225 < baseStart_43225 := by decide
  rcases family_descends (prefixWord ++ tailWord_43225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43228 : List Nat := [2, 2, 5, 2, 1, 1, 2, 6]
def baseStart_43228 : Nat := 118140960795 + 43228 * 2 ^ 59
def prefixEnd_43228 : Nat := 4983230072969 + 3 ^ 40 * 43228 * 2
def baseEnd_43228 : Nat := 3288406182616607992771

theorem tailTrace_43228 : CollatzResearch.WordTrace tailWord_43228 prefixEnd_43228 3288406182616607992771 := by
  unfold tailWord_43228
  simp only [CollatzResearch.WordTrace]
  refine ⟨788327343699906799869169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1051103124933209066492225 788327343699906799869169)
  ·
    refine ⟨591245507774930099901877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 788327343699906799869169 591245507774930099901877)
    ·
      refine ⟨55429266353899696865801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 591245507774930099901877 55429266353899696865801)
      ·
        refine ⟨41571949765424772649351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55429266353899696865801 41571949765424772649351)
        ·
          refine ⟨62357924648137158974027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41571949765424772649351 62357924648137158974027)
          ·
            refine ⟨93536886972205738461041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62357924648137158974027 93536886972205738461041)
            ·
              refine ⟨70152665229154303845781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93536886972205738461041 70152665229154303845781)
              ·
                refine ⟨3288406182616607992771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70152665229154303845781 3288406182616607992771)
                ·
                  rfl

theorem cell21_43228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_43228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43228 prefixEnd_43228 := by exact prefixLift 43228
  have htrace : WordTrace (prefixWord ++ tailWord_43228) baseStart_43228 baseEnd_43228 := by
    simpa [prefixWord, tailWord_43228, baseEnd_43228] using wordTrace_append hprefix tailTrace_43228
  have hstable : (prefixWord ++ tailWord_43228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43228).length < 2 ^ (prefixWord ++ tailWord_43228).sum := by decide
  have hdescent : baseEnd_43228 < baseStart_43228 := by decide
  rcases family_descends (prefixWord ++ tailWord_43228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43301 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 5]
def baseStart_43301 : Nat := 118140960795 + 43301 * 2 ^ 59
def prefixEnd_43301 : Nat := 4983230072969 + 3 ^ 40 * 43301 * 2
def baseEnd_43301 : Nat := 9881878142417919261497

theorem tailTrace_43301 : CollatzResearch.WordTrace tailWord_43301 prefixEnd_43301 9881878142417919261497 := by
  unfold tailWord_43301
  simp only [CollatzResearch.WordTrace]
  refine ⟨1579317216135347067145757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1052878144090231378097171 1579317216135347067145757)
  ·
    refine ⟨592243956050755150179659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1579317216135347067145757 592243956050755150179659)
    ·
      refine ⟨888365934076132725269489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592243956050755150179659 888365934076132725269489)
      ·
        refine ⟨666274450557099543952117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 888365934076132725269489 666274450557099543952117)
        ·
          refine ⟨62463229739728082245511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 666274450557099543952117 62463229739728082245511)
          ·
            refine ⟨93694844609592123368267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62463229739728082245511 93694844609592123368267)
            ·
              refine ⟨140542266914388185052401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93694844609592123368267 140542266914388185052401)
              ·
                refine ⟨105406700185791138789301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140542266914388185052401 105406700185791138789301)
                ·
                  refine ⟨9881878142417919261497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105406700185791138789301 9881878142417919261497)
                  ·
                    rfl

theorem cell21_43301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_43301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43301 prefixEnd_43301 := by exact prefixLift 43301
  have htrace : WordTrace (prefixWord ++ tailWord_43301) baseStart_43301 baseEnd_43301 := by
    simpa [prefixWord, tailWord_43301, baseEnd_43301] using wordTrace_append hprefix tailTrace_43301
  have hstable : (prefixWord ++ tailWord_43301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43301).length < 2 ^ (prefixWord ++ tailWord_43301).sum := by decide
  have hdescent : baseEnd_43301 < baseStart_43301 := by decide
  rcases family_descends (prefixWord ++ tailWord_43301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43349 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 4]
def baseStart_43349 : Nat := 118140960795 + 43349 * 2 ^ 59
def prefixEnd_43349 : Nat := 4983230072969 + 3 ^ 40 * 43349 * 2
def baseEnd_43349 : Nat := 9892832396380502461399

theorem tailTrace_43349 : CollatzResearch.WordTrace tailWord_43349 prefixEnd_43349 9892832396380502461399 := by
  unfold tailWord_43349
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581067919961451264893101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1054045279974300843262067 1581067919961451264893101)
  ·
    refine ⟨592900469985544224334913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1581067919961451264893101 592900469985544224334913)
    ·
      refine ⟨444675352489158168251185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 592900469985544224334913 444675352489158168251185)
      ·
        refine ⟨333506514366868626188389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444675352489158168251185 333506514366868626188389)
        ·
          refine ⟨62532471443787867410323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333506514366868626188389 62532471443787867410323)
          ·
            refine ⟨93798707165681801115485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62532471443787867410323 93798707165681801115485)
            ·
              refine ⟨35174515187130675418307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93798707165681801115485 35174515187130675418307)
              ·
                refine ⟨52761772780696013127461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35174515187130675418307 52761772780696013127461)
                ·
                  refine ⟨9892832396380502461399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52761772780696013127461 9892832396380502461399)
                  ·
                    rfl

theorem cell21_43349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_43349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43349 prefixEnd_43349 := by exact prefixLift 43349
  have htrace : WordTrace (prefixWord ++ tailWord_43349) baseStart_43349 baseEnd_43349 := by
    simpa [prefixWord, tailWord_43349, baseEnd_43349] using wordTrace_append hprefix tailTrace_43349
  have hstable : (prefixWord ++ tailWord_43349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43349).length < 2 ^ (prefixWord ++ tailWord_43349).sum := by decide
  have hdescent : baseEnd_43349 < baseStart_43349 := by decide
  rcases family_descends (prefixWord ++ tailWord_43349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43450 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_43450 : Nat := 118140960795 + 43450 * 2 ^ 59
def prefixEnd_43450 : Nat := 4983230072969 + 3 ^ 40 * 43450 * 2
def baseEnd_43450 : Nat := 9915881972426771277859

theorem tailTrace_43450 : CollatzResearch.WordTrace tailWord_43450 prefixEnd_43450 9915881972426771277859 := by
  unfold tailWord_43450
  simp only [CollatzResearch.WordTrace]
  refine ⟨396187923148886378579951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1056501128397030342879869 396187923148886378579951)
  ·
    refine ⟨594281884723329567869927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 396187923148886378579951 594281884723329567869927)
    ·
      refine ⟨891422827084994351804891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 594281884723329567869927 891422827084994351804891)
      ·
        refine ⟨1337134240627491527707337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891422827084994351804891 1337134240627491527707337)
        ·
          refine ⟨1002850680470618645780503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1337134240627491527707337 1002850680470618645780503)
          ·
            refine ⟨1504276020705927968670755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002850680470618645780503 1504276020705927968670755)
            ·
              refine ⟨2256414031058891953006133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504276020705927968670755 2256414031058891953006133)
              ·
                refine ⟨211538815411771120594325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2256414031058891953006133 211538815411771120594325)
                ·
                  refine ⟨9915881972426771277859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 211538815411771120594325 9915881972426771277859)
                  ·
                    rfl

theorem cell21_43450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_43450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43450 prefixEnd_43450 := by exact prefixLift 43450
  have htrace : WordTrace (prefixWord ++ tailWord_43450) baseStart_43450 baseEnd_43450 := by
    simpa [prefixWord, tailWord_43450, baseEnd_43450] using wordTrace_append hprefix tailTrace_43450
  have hstable : (prefixWord ++ tailWord_43450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43450).length < 2 ^ (prefixWord ++ tailWord_43450).sum := by decide
  have hdescent : baseEnd_43450 < baseStart_43450 := by decide
  rcases family_descends (prefixWord ++ tailWord_43450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43501 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 4]
def baseStart_43501 : Nat := 118140960795 + 43501 * 2 ^ 59
def prefixEnd_43501 : Nat := 4983230072969 + 3 ^ 40 * 43501 * 2
def baseEnd_43501 : Nat := 9927520867262015927755

theorem tailTrace_43501 : CollatzResearch.WordTrace tailWord_43501 prefixEnd_43501 9927520867262015927755 := by
  unfold tailWord_43501
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586611815410781224426357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1057741210273854149617571 1586611815410781224426357)
  ·
    refine ⟨148744857694760739789971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1586611815410781224426357 148744857694760739789971)
    ·
      refine ⟨223117286542141109684957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148744857694760739789971 223117286542141109684957)
      ·
        refine ⟨83668982453302916131859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223117286542141109684957 83668982453302916131859)
        ·
          refine ⟨125503473679954374197789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83668982453302916131859 125503473679954374197789)
          ·
            refine ⟨47063802629982890324171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125503473679954374197789 47063802629982890324171)
            ·
              refine ⟨70595703944974335486257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47063802629982890324171 70595703944974335486257)
              ·
                refine ⟨52946777958730751614693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70595703944974335486257 52946777958730751614693)
                ·
                  refine ⟨9927520867262015927755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52946777958730751614693 9927520867262015927755)
                  ·
                    rfl

theorem cell21_43501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_43501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43501 prefixEnd_43501 := by exact prefixLift 43501
  have htrace : WordTrace (prefixWord ++ tailWord_43501) baseStart_43501 baseEnd_43501 := by
    simpa [prefixWord, tailWord_43501, baseEnd_43501] using wordTrace_append hprefix tailTrace_43501
  have hstable : (prefixWord ++ tailWord_43501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43501).length < 2 ^ (prefixWord ++ tailWord_43501).sum := by decide
  have hdescent : baseEnd_43501 < baseStart_43501 := by decide
  rcases family_descends (prefixWord ++ tailWord_43501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43512 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 5]
def baseStart_43512 : Nat := 118140960795 + 43512 * 2 ^ 59
def prefixEnd_43512 : Nat := 4983230072969 + 3 ^ 40 * 43512 * 2
def baseEnd_43512 : Nat := 9930031217128441244399

theorem tailTrace_43512 : CollatzResearch.WordTrace tailWord_43512 prefixEnd_43512 9930031217128441244399 := by
  unfold tailWord_43512
  simp only [CollatzResearch.WordTrace]
  refine ⟨793506509185465051538395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1058008678913953402051193 793506509185465051538395)
  ·
    refine ⟨1190259763778197577307593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 793506509185465051538395 1190259763778197577307593)
    ·
      refine ⟨892694822833648182980695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1190259763778197577307593 892694822833648182980695)
      ·
        refine ⟨1339042234250472274471043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892694822833648182980695 1339042234250472274471043)
        ·
          refine ⟨2008563351375708411706565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339042234250472274471043 2008563351375708411706565)
          ·
            refine ⟨376605628382945327194981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2008563351375708411706565 376605628382945327194981)
            ·
              refine ⟨70613555321802248849059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 376605628382945327194981 70613555321802248849059)
              ·
                refine ⟨105920332982703373273589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70613555321802248849059 105920332982703373273589)
                ·
                  refine ⟨9930031217128441244399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105920332982703373273589 9930031217128441244399)
                  ·
                    rfl

theorem cell21_43512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_43512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43512 prefixEnd_43512 := by exact prefixLift 43512
  have htrace : WordTrace (prefixWord ++ tailWord_43512) baseStart_43512 baseEnd_43512 := by
    simpa [prefixWord, tailWord_43512, baseEnd_43512] using wordTrace_append hprefix tailTrace_43512
  have hstable : (prefixWord ++ tailWord_43512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43512).length < 2 ^ (prefixWord ++ tailWord_43512).sum := by decide
  have hdescent : baseEnd_43512 < baseStart_43512 := by decide
  rcases family_descends (prefixWord ++ tailWord_43512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43574 : List Nat := [5, 1, 2, 1, 2, 1, 1, 8]
def baseStart_43574 : Nat := 118140960795 + 43574 * 2 ^ 59
def prefixEnd_43574 : Nat := 4983230072969 + 3 ^ 40 * 43574 * 2
def baseEnd_43574 : Nat := 3314726820610037070313

theorem tailTrace_43574 : CollatzResearch.WordTrace tailWord_43574 prefixEnd_43574 3314726820610037070313 := by
  unfold tailWord_43574
  simp only [CollatzResearch.WordTrace]
  refine ⟨99329646509144668239611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1059516229430876461222517 99329646509144668239611)
  ·
    refine ⟨148994469763717002359417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99329646509144668239611 148994469763717002359417)
    ·
      refine ⟨111745852322787751769563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148994469763717002359417 111745852322787751769563)
      ·
        refine ⟨167618778484181627654345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111745852322787751769563 167618778484181627654345)
        ·
          refine ⟨125714083863136220740759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167618778484181627654345 125714083863136220740759)
          ·
            refine ⟨188571125794704331111139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125714083863136220740759 188571125794704331111139)
            ·
              refine ⟨282856688692056496666709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188571125794704331111139 282856688692056496666709)
              ·
                refine ⟨3314726820610037070313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 282856688692056496666709 3314726820610037070313)
                ·
                  rfl

theorem cell21_43574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_43574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43574 prefixEnd_43574 := by exact prefixLift 43574
  have htrace : WordTrace (prefixWord ++ tailWord_43574) baseStart_43574 baseEnd_43574 := by
    simpa [prefixWord, tailWord_43574, baseEnd_43574] using wordTrace_append hprefix tailTrace_43574
  have hstable : (prefixWord ++ tailWord_43574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43574).length < 2 ^ (prefixWord ++ tailWord_43574).sum := by decide
  have hdescent : baseEnd_43574 < baseStart_43574 := by decide
  rcases family_descends (prefixWord ++ tailWord_43574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43614 : List Nat := [4, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_43614 : Nat := 118140960795 + 43614 * 2 ^ 59
def prefixEnd_43614 : Nat := 4983230072969 + 3 ^ 40 * 43614 * 2
def baseEnd_43614 : Nat := 9953309006798930544191

theorem tailTrace_43614 : CollatzResearch.WordTrace tailWord_43614 prefixEnd_43614 9953309006798930544191 := by
  unfold tailWord_43614
  simp only [CollatzResearch.WordTrace]
  refine ⟨198841658000175190411237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1060488842667601015526597 198841658000175190411237)
  ·
    refine ⟨37282810875032848202107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198841658000175190411237 37282810875032848202107)
    ·
      refine ⟨55924216312549272303161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37282810875032848202107 55924216312549272303161)
      ·
        refine ⟨41943162234411954227371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55924216312549272303161 41943162234411954227371)
        ·
          refine ⟨62914743351617931341057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41943162234411954227371 62914743351617931341057)
          ·
            refine ⟨47186057513713448505793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62914743351617931341057 47186057513713448505793)
            ·
              refine ⟨35389543135285086379345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47186057513713448505793 35389543135285086379345)
              ·
                refine ⟨26542157351463814784509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35389543135285086379345 26542157351463814784509)
                ·
                  refine ⟨9953309006798930544191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26542157351463814784509 9953309006798930544191)
                  ·
                    rfl

theorem cell21_43614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_43614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43614 prefixEnd_43614 := by exact prefixLift 43614
  have htrace : WordTrace (prefixWord ++ tailWord_43614) baseStart_43614 baseEnd_43614 := by
    simpa [prefixWord, tailWord_43614, baseEnd_43614] using wordTrace_append hprefix tailTrace_43614
  have hstable : (prefixWord ++ tailWord_43614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43614).length < 2 ^ (prefixWord ++ tailWord_43614).sum := by decide
  have hdescent : baseEnd_43614 < baseStart_43614 := by decide
  rcases family_descends (prefixWord ++ tailWord_43614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43619 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 4]
def baseStart_43619 : Nat := 118140960795 + 43619 * 2 ^ 59
def prefixEnd_43619 : Nat := 4983230072969 + 3 ^ 40 * 43619 * 2
def baseEnd_43619 : Nat := 9954450074920032960847

theorem tailTrace_43619 : CollatzResearch.WordTrace tailWord_43619 prefixEnd_43619 9954450074920032960847 := by
  unfold tailWord_43619
  simp only [CollatzResearch.WordTrace]
  refine ⟨1590915628983287377221911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1060610419322191584814607 1590915628983287377221911)
  ·
    refine ⟨2386373443474931065832867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1590915628983287377221911 2386373443474931065832867)
    ·
      refine ⟨3579560165212396598749301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2386373443474931065832867 3579560165212396598749301)
      ·
        refine ⟨335583765488662181132747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3579560165212396598749301 335583765488662181132747)
        ·
          refine ⟨503375648232993271699121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335583765488662181132747 503375648232993271699121)
          ·
            refine ⟨377531736174744953774341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503375648232993271699121 377531736174744953774341)
            ·
              refine ⟨70787200532764678832689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 377531736174744953774341 70787200532764678832689)
              ·
                refine ⟨53090400399573509124517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70787200532764678832689 53090400399573509124517)
                ·
                  refine ⟨9954450074920032960847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53090400399573509124517 9954450074920032960847)
                  ·
                    rfl

theorem cell21_43619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 4].length) (baseStart_43619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43619 prefixEnd_43619 := by exact prefixLift 43619
  have htrace : WordTrace (prefixWord ++ tailWord_43619) baseStart_43619 baseEnd_43619 := by
    simpa [prefixWord, tailWord_43619, baseEnd_43619] using wordTrace_append hprefix tailTrace_43619
  have hstable : (prefixWord ++ tailWord_43619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43619).length < 2 ^ (prefixWord ++ tailWord_43619).sum := by decide
  have hdescent : baseEnd_43619 < baseStart_43619 := by decide
  rcases family_descends (prefixWord ++ tailWord_43619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43681 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 5]
def baseStart_43681 : Nat := 118140960795 + 43681 * 2 ^ 59
def prefixEnd_43681 : Nat := 4983230072969 + 3 ^ 40 * 43681 * 2
def baseEnd_43681 : Nat := 9968599319621702927387

theorem tailTrace_43681 : CollatzResearch.WordTrace tailWord_43681 prefixEnd_43681 9968599319621702927387 := by
  unfold tailWord_43681
  simp only [CollatzResearch.WordTrace]
  refine ⟨1593176954758671965978897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1062117969839114643985931 1593176954758671965978897)
  ·
    refine ⟨1194882716069003974484173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1593176954758671965978897 1194882716069003974484173)
    ·
      refine ⟨448081018525876490431565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1194882716069003974484173 448081018525876490431565)
      ·
        refine ⟨168030381947203683911837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448081018525876490431565 168030381947203683911837)
        ·
          refine ⟨63011393230201381466939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168030381947203683911837 63011393230201381466939)
          ·
            refine ⟨94517089845302072200409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63011393230201381466939 94517089845302072200409)
            ·
              refine ⟨70887817383976554150307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94517089845302072200409 70887817383976554150307)
              ·
                refine ⟨106331726075964831225461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70887817383976554150307 106331726075964831225461)
                ·
                  refine ⟨9968599319621702927387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106331726075964831225461 9968599319621702927387)
                  ·
                    rfl

theorem cell21_43681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_43681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43681 prefixEnd_43681 := by exact prefixLift 43681
  have htrace : WordTrace (prefixWord ++ tailWord_43681) baseStart_43681 baseEnd_43681 := by
    simpa [prefixWord, tailWord_43681, baseEnd_43681] using wordTrace_append hprefix tailTrace_43681
  have hstable : (prefixWord ++ tailWord_43681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43681).length < 2 ^ (prefixWord ++ tailWord_43681).sum := by decide
  have hdescent : baseEnd_43681 < baseStart_43681 := by decide
  rcases family_descends (prefixWord ++ tailWord_43681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43709 : List Nat := [1, 4, 1, 2, 1, 4, 1, 7]
def baseStart_43709 : Nat := 118140960795 + 43709 * 2 ^ 59
def prefixEnd_43709 : Nat := 4983230072969 + 3 ^ 40 * 43709 * 2
def baseEnd_43709 : Nat := 3324996433699958820221

theorem tailTrace_43709 : CollatzResearch.WordTrace tailWord_43709 prefixEnd_43709 3324996433699958820221 := by
  unfold tailWord_43709
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594198198657232747998181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1062798799104821831998787 1594198198657232747998181)
  ·
    refine ⟨298912162248231140249659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1594198198657232747998181 298912162248231140249659)
    ·
      refine ⟨448368243372346710374489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298912162248231140249659 448368243372346710374489)
      ·
        refine ⟨336276182529260032780867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448368243372346710374489 336276182529260032780867)
        ·
          refine ⟨504414273793890049171301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336276182529260032780867 504414273793890049171301)
          ·
            refine ⟨94577676336354384219619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 504414273793890049171301 94577676336354384219619)
            ·
              refine ⟨141866514504531576329429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94577676336354384219619 141866514504531576329429)
              ·
                refine ⟨3324996433699958820221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 141866514504531576329429 3324996433699958820221)
                ·
                  rfl

theorem cell21_43709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 7].length) (baseStart_43709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43709 prefixEnd_43709 := by exact prefixLift 43709
  have htrace : WordTrace (prefixWord ++ tailWord_43709) baseStart_43709 baseEnd_43709 := by
    simpa [prefixWord, tailWord_43709, baseEnd_43709] using wordTrace_append hprefix tailTrace_43709
  have hstable : (prefixWord ++ tailWord_43709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43709).length < 2 ^ (prefixWord ++ tailWord_43709).sum := by decide
  have hdescent : baseEnd_43709 < baseStart_43709 := by decide
  rcases family_descends (prefixWord ++ tailWord_43709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43768 : List Nat := [2, 1, 2, 1, 1, 2, 3, 9]
def baseStart_43768 : Nat := 118140960795 + 43768 * 2 ^ 59
def prefixEnd_43768 : Nat := 4983230072969 + 3 ^ 40 * 43768 * 2
def baseEnd_43768 : Nat := 3329484634976294992403

theorem tailTrace_43768 : CollatzResearch.WordTrace tailWord_43768 prefixEnd_43768 3329484634976294992403 := by
  unfold tailWord_43768
  simp only [CollatzResearch.WordTrace]
  refine ⟨798175052721742912197979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1064233403628990549597305 798175052721742912197979)
  ·
    refine ⟨1197262579082614368296969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 798175052721742912197979 1197262579082614368296969)
    ·
      refine ⟨897946934311960776222727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1197262579082614368296969 897946934311960776222727)
      ·
        refine ⟨1346920401467941164334091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897946934311960776222727 1346920401467941164334091)
        ·
          refine ⟨2020380602201911746501137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346920401467941164334091 2020380602201911746501137)
          ·
            refine ⟨1515285451651433809875853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2020380602201911746501137 1515285451651433809875853)
            ·
              refine ⟨568232044369287678703445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1515285451651433809875853 568232044369287678703445)
              ·
                refine ⟨3329484634976294992403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 568232044369287678703445 3329484634976294992403)
                ·
                  rfl

theorem cell21_43768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_43768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43768 prefixEnd_43768 := by exact prefixLift 43768
  have htrace : WordTrace (prefixWord ++ tailWord_43768) baseStart_43768 baseEnd_43768 := by
    simpa [prefixWord, tailWord_43768, baseEnd_43768] using wordTrace_append hprefix tailTrace_43768
  have hstable : (prefixWord ++ tailWord_43768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43768).length < 2 ^ (prefixWord ++ tailWord_43768).sum := by decide
  have hdescent : baseEnd_43768 < baseStart_43768 := by decide
  rcases family_descends (prefixWord ++ tailWord_43768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43816 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_43816 : Nat := 118140960795 + 43816 * 2 ^ 59
def prefixEnd_43816 : Nat := 4983230072969 + 3 ^ 40 * 43816 * 2
def baseEnd_43816 : Nat := 9999408158891468177111

theorem tailTrace_43816 : CollatzResearch.WordTrace tailWord_43816 prefixEnd_43816 9999408158891468177111 := by
  unfold tailWord_43816
  simp only [CollatzResearch.WordTrace]
  refine ⟨799050404634795011071651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1065400539513060014762201 799050404634795011071651)
  ·
    refine ⟨1198575606952192516607477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 799050404634795011071651 1198575606952192516607477)
    ·
      refine ⟨112366463151768048431951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1198575606952192516607477 112366463151768048431951)
      ·
        refine ⟨168549694727652072647927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112366463151768048431951 168549694727652072647927)
        ·
          refine ⟨252824542091478108971891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168549694727652072647927 252824542091478108971891)
          ·
            refine ⟨379236813137217163457837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252824542091478108971891 379236813137217163457837)
            ·
              refine ⟨142213804926456436296689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379236813137217163457837 142213804926456436296689)
              ·
                refine ⟨106660353694842327222517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142213804926456436296689 106660353694842327222517)
                ·
                  refine ⟨9999408158891468177111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106660353694842327222517 9999408158891468177111)
                  ·
                    rfl

theorem cell21_43816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_43816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43816 prefixEnd_43816 := by exact prefixLift 43816
  have htrace : WordTrace (prefixWord ++ tailWord_43816) baseStart_43816 baseEnd_43816 := by
    simpa [prefixWord, tailWord_43816, baseEnd_43816] using wordTrace_append hprefix tailTrace_43816
  have hstable : (prefixWord ++ tailWord_43816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43816).length < 2 ^ (prefixWord ++ tailWord_43816).sum := by decide
  have hdescent : baseEnd_43816 < baseStart_43816 := by decide
  rcases family_descends (prefixWord ++ tailWord_43816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43937 : List Nat := [1, 2, 3, 4, 1, 1, 2, 7]
def baseStart_43937 : Nat := 118140960795 + 43937 * 2 ^ 59
def prefixEnd_43937 : Nat := 4983230072969 + 3 ^ 40 * 43937 * 2
def baseEnd_43937 : Nat := 3342340669140715553399

theorem tailTrace_43937 : CollatzResearch.WordTrace tailWord_43937 prefixEnd_43937 3342340669140715553399 := by
  unfold tailWord_43937
  simp only [CollatzResearch.WordTrace]
  refine ⟨1602514041831227687298065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1068342694554151791532043 1602514041831227687298065)
  ·
    refine ⟨1201885531373420765473549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1602514041831227687298065 1201885531373420765473549)
    ·
      refine ⟨450707074265032787052581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1201885531373420765473549 450707074265032787052581)
      ·
        refine ⟨84507576424693647572359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 450707074265032787052581 84507576424693647572359)
        ·
          refine ⟨126761364637040471358539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84507576424693647572359 126761364637040471358539)
          ·
            refine ⟨190142046955560707037809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126761364637040471358539 190142046955560707037809)
            ·
              refine ⟨142606535216670530278357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190142046955560707037809 142606535216670530278357)
              ·
                refine ⟨3342340669140715553399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 142606535216670530278357 3342340669140715553399)
                ·
                  rfl

theorem cell21_43937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 7].length) (baseStart_43937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_43937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_43937 prefixEnd_43937 := by exact prefixLift 43937
  have htrace : WordTrace (prefixWord ++ tailWord_43937) baseStart_43937 baseEnd_43937 := by
    simpa [prefixWord, tailWord_43937, baseEnd_43937] using wordTrace_append hprefix tailTrace_43937
  have hstable : (prefixWord ++ tailWord_43937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43937).length < 2 ^ (prefixWord ++ tailWord_43937).sum := by decide
  have hdescent : baseEnd_43937 < baseStart_43937 := by decide
  rcases family_descends (prefixWord ++ tailWord_43937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44002 : List Nat := [3, 3, 3, 1, 1, 1, 1, 5, 3]
def baseStart_44002 : Nat := 118140960795 + 44002 * 2 ^ 59
def prefixEnd_44002 : Nat := 4983230072969 + 3 ^ 40 * 44002 * 2
def baseEnd_44002 : Nat := 10041855892996478076731

theorem tailTrace_44002 : CollatzResearch.WordTrace tailWord_44002 prefixEnd_44002 10041855892996478076731 := by
  unfold tailWord_44002
  simp only [CollatzResearch.WordTrace]
  refine ⟨401221196648935947103565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1069923191063829192276173 401221196648935947103565)
  ·
    refine ⟨150457948743350980163837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 401221196648935947103565 150457948743350980163837)
    ·
      refine ⟨56421730778756617561439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150457948743350980163837 56421730778756617561439)
      ·
        refine ⟨84632596168134926342159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56421730778756617561439 84632596168134926342159)
        ·
          refine ⟨126948894252202389513239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84632596168134926342159 126948894252202389513239)
          ·
            refine ⟨190423341378303584269859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126948894252202389513239 190423341378303584269859)
            ·
              refine ⟨285635012067455376404789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190423341378303584269859 285635012067455376404789)
              ·
                refine ⟨26778282381323941537949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 285635012067455376404789 26778282381323941537949)
                ·
                  refine ⟨10041855892996478076731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26778282381323941537949 10041855892996478076731)
                  ·
                    rfl

theorem cell21_44002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_44002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44002 prefixEnd_44002 := by exact prefixLift 44002
  have htrace : WordTrace (prefixWord ++ tailWord_44002) baseStart_44002 baseEnd_44002 := by
    simpa [prefixWord, tailWord_44002, baseEnd_44002] using wordTrace_append hprefix tailTrace_44002
  have hstable : (prefixWord ++ tailWord_44002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44002).length < 2 ^ (prefixWord ++ tailWord_44002).sum := by decide
  have hdescent : baseEnd_44002 < baseStart_44002 := by decide
  rcases family_descends (prefixWord ++ tailWord_44002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44078 : List Nat := [4, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_44078 : Nat := 118140960795 + 44078 * 2 ^ 59
def prefixEnd_44078 : Nat := 4983230072969 + 3 ^ 40 * 44078 * 2
def baseEnd_44078 : Nat := 10059200128437234809909

theorem tailTrace_44078 : CollatzResearch.WordTrace tailWord_44078 prefixEnd_44078 10059200128437234809909 := by
  unfold tailWord_44078
  simp only [CollatzResearch.WordTrace]
  refine ⟨200957091790051096022611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1071771156213605845453925 200957091790051096022611)
  ·
    refine ⟨301435637685076644033917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200957091790051096022611 301435637685076644033917)
    ·
      refine ⟨113038364131903741512719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 301435637685076644033917 113038364131903741512719)
      ·
        refine ⟨169557546197855612269079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113038364131903741512719 169557546197855612269079)
        ·
          refine ⟨254336319296783418403619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169557546197855612269079 254336319296783418403619)
          ·
            refine ⟨381504478945175127605429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254336319296783418403619 381504478945175127605429)
            ·
              refine ⟨35766044901110168213009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 381504478945175127605429 35766044901110168213009)
              ·
                refine ⟨26824533675832626159757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35766044901110168213009 26824533675832626159757)
                ·
                  refine ⟨10059200128437234809909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26824533675832626159757 10059200128437234809909)
                  ·
                    rfl

theorem cell21_44078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_44078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44078 prefixEnd_44078 := by exact prefixLift 44078
  have htrace : WordTrace (prefixWord ++ tailWord_44078) baseStart_44078 baseEnd_44078 := by
    simpa [prefixWord, tailWord_44078, baseEnd_44078] using wordTrace_append hprefix tailTrace_44078
  have hstable : (prefixWord ++ tailWord_44078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44078).length < 2 ^ (prefixWord ++ tailWord_44078).sum := by decide
  have hdescent : baseEnd_44078 < baseStart_44078 := by decide
  rcases family_descends (prefixWord ++ tailWord_44078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44089 : List Nat := [1, 2, 1, 5, 2, 2, 2, 6]
def baseStart_44089 : Nat := 118140960795 + 44089 * 2 ^ 59
def prefixEnd_44089 : Nat := 4983230072969 + 3 ^ 40 * 44089 * 2
def baseEnd_44089 : Nat := 3353903492767886708851

theorem tailTrace_44089 : CollatzResearch.WordTrace tailWord_44089 prefixEnd_44089 3353903492767886708851 := by
  unfold tailWord_44089
  simp only [CollatzResearch.WordTrace]
  refine ⟨1608057937280557646831321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1072038624853705097887547 1608057937280557646831321)
  ·
    refine ⟨1206043452960418235123491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1608057937280557646831321 1206043452960418235123491)
    ·
      refine ⟨1809065179440627352685237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1206043452960418235123491 1809065179440627352685237)
      ·
        refine ⟨169599860572558814314241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1809065179440627352685237 169599860572558814314241)
        ·
          refine ⟨127199895429419110735681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169599860572558814314241 127199895429419110735681)
          ·
            refine ⟨95399921572064333051761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127199895429419110735681 95399921572064333051761)
            ·
              refine ⟨71549941179048249788821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95399921572064333051761 71549941179048249788821)
              ·
                refine ⟨3353903492767886708851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71549941179048249788821 3353903492767886708851)
                ·
                  rfl

theorem cell21_44089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 6].length) (baseStart_44089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44089 prefixEnd_44089 := by exact prefixLift 44089
  have htrace : WordTrace (prefixWord ++ tailWord_44089) baseStart_44089 baseEnd_44089 := by
    simpa [prefixWord, tailWord_44089, baseEnd_44089] using wordTrace_append hprefix tailTrace_44089
  have hstable : (prefixWord ++ tailWord_44089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44089).length < 2 ^ (prefixWord ++ tailWord_44089).sum := by decide
  have hdescent : baseEnd_44089 < baseStart_44089 := by decide
  rcases family_descends (prefixWord ++ tailWord_44089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44092 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 4]
def baseStart_44092 : Nat := 118140960795 + 44092 * 2 ^ 59
def prefixEnd_44092 : Nat := 4983230072969 + 3 ^ 40 * 44092 * 2
def baseEnd_44092 : Nat := 10062395119176321576547

theorem tailTrace_44092 : CollatzResearch.WordTrace tailWord_44092 prefixEnd_44092 10062395119176321576547 := by
  unfold tailWord_44092
  simp only [CollatzResearch.WordTrace]
  refine ⟨804083678134844579595265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1072111570846459439460353 804083678134844579595265)
  ·
    refine ⟨603062758601133434696449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 804083678134844579595265 603062758601133434696449)
    ·
      refine ⟨452297068950850076022337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 603062758601133434696449 452297068950850076022337)
      ·
        refine ⟨339222801713137557016753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452297068950850076022337 339222801713137557016753)
        ·
          refine ⟨254417101284853167762565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339222801713137557016753 254417101284853167762565)
          ·
            refine ⟨47703206490909968955481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 254417101284853167762565 47703206490909968955481)
            ·
              refine ⟨35777404868182476716611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47703206490909968955481 35777404868182476716611)
              ·
                refine ⟨53666107302273715074917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35777404868182476716611 53666107302273715074917)
                ·
                  refine ⟨10062395119176321576547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53666107302273715074917 10062395119176321576547)
                  ·
                    rfl

theorem cell21_44092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_44092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44092 prefixEnd_44092 := by exact prefixLift 44092
  have htrace : WordTrace (prefixWord ++ tailWord_44092) baseStart_44092 baseEnd_44092 := by
    simpa [prefixWord, tailWord_44092, baseEnd_44092] using wordTrace_append hprefix tailTrace_44092
  have hstable : (prefixWord ++ tailWord_44092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44092).length < 2 ^ (prefixWord ++ tailWord_44092).sum := by decide
  have hdescent : baseEnd_44092 < baseStart_44092 := by decide
  rcases family_descends (prefixWord ++ tailWord_44092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44120 : List Nat := [2, 1, 2, 2, 1, 3, 2, 5, 3]
def baseStart_44120 : Nat := 118140960795 + 44120 * 2 ^ 59
def prefixEnd_44120 : Nat := 4983230072969 + 3 ^ 40 * 44120 * 2
def baseEnd_44120 : Nat := 10068785100654495109823

theorem tailTrace_44120 : CollatzResearch.WordTrace tailWord_44120 prefixEnd_44120 10068785100654495109823 := by
  unfold tailWord_44120
  simp only [CollatzResearch.WordTrace]
  refine ⟨804594300084124970604907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1072792400112166627473209 804594300084124970604907)
  ·
    refine ⟨1206891450126187455907361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 804594300084124970604907 1206891450126187455907361)
    ·
      refine ⟨905168587594640591930521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1206891450126187455907361 905168587594640591930521)
      ·
        refine ⟨678876440695980443947891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 905168587594640591930521 678876440695980443947891)
        ·
          refine ⟨1018314661043970665921837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678876440695980443947891 1018314661043970665921837)
          ·
            refine ⟨381867997891488999720689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1018314661043970665921837 381867997891488999720689)
            ·
              refine ⟨286400998418616749790517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381867997891488999720689 286400998418616749790517)
              ·
                refine ⟨26850093601745320292861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286400998418616749790517 26850093601745320292861)
                ·
                  refine ⟨10068785100654495109823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26850093601745320292861 10068785100654495109823)
                  ·
                    rfl

theorem cell21_44120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 3].length) (baseStart_44120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44120 prefixEnd_44120 := by exact prefixLift 44120
  have htrace : WordTrace (prefixWord ++ tailWord_44120) baseStart_44120 baseEnd_44120 := by
    simpa [prefixWord, tailWord_44120, baseEnd_44120] using wordTrace_append hprefix tailTrace_44120
  have hstable : (prefixWord ++ tailWord_44120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44120).length < 2 ^ (prefixWord ++ tailWord_44120).sum := by decide
  have hdescent : baseEnd_44120 < baseStart_44120 := by decide
  rcases family_descends (prefixWord ++ tailWord_44120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44137 : List Nat := [1, 2, 1, 1, 1, 6, 4, 2, 3]
def baseStart_44137 : Nat := 118140960795 + 44137 * 2 ^ 59
def prefixEnd_44137 : Nat := 4983230072969 + 3 ^ 40 * 44137 * 2
def baseEnd_44137 : Nat := 10072664732266243326455

theorem tailTrace_44137 : CollatzResearch.WordTrace tailWord_44137 prefixEnd_44137 10072664732266243326455 := by
  unfold tailWord_44137
  simp only [CollatzResearch.WordTrace]
  refine ⟨1609808641106661844578665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1073205760737774563052443 1609808641106661844578665)
  ·
    refine ⟨1207356480829996383433999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1609808641106661844578665 1207356480829996383433999)
    ·
      refine ⟨1811034721244994575150999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1207356480829996383433999 1811034721244994575150999)
      ·
        refine ⟨2716552081867491862726499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1811034721244994575150999 2716552081867491862726499)
        ·
          refine ⟨4074828122801237794089749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716552081867491862726499 4074828122801237794089749)
          ·
            refine ⟨191007568256308021597957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4074828122801237794089749 191007568256308021597957)
            ·
              refine ⟨35813919048057754049617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191007568256308021597957 35813919048057754049617)
              ·
                refine ⟨26860439286043315537213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35813919048057754049617 26860439286043315537213)
                ·
                  refine ⟨10072664732266243326455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26860439286043315537213 10072664732266243326455)
                  ·
                    rfl

theorem cell21_44137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 3].length) (baseStart_44137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44137 prefixEnd_44137 := by exact prefixLift 44137
  have htrace : WordTrace (prefixWord ++ tailWord_44137) baseStart_44137 baseEnd_44137 := by
    simpa [prefixWord, tailWord_44137, baseEnd_44137] using wordTrace_append hprefix tailTrace_44137
  have hstable : (prefixWord ++ tailWord_44137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44137).length < 2 ^ (prefixWord ++ tailWord_44137).sum := by decide
  have hdescent : baseEnd_44137 < baseStart_44137 := by decide
  rcases family_descends (prefixWord ++ tailWord_44137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44196 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 5]
def baseStart_44196 : Nat := 118140960795 + 44196 * 2 ^ 59
def prefixEnd_44196 : Nat := 4983230072969 + 3 ^ 40 * 44196 * 2
def baseEnd_44196 : Nat := 10086129336095251843001

theorem tailTrace_44196 : CollatzResearch.WordTrace tailWord_44196 prefixEnd_44196 10086129336095251843001 := by
  unfold tailWord_44196
  simp only [CollatzResearch.WordTrace]
  refine ⟨805980273946457460488221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1074640365261943280650961 805980273946457460488221)
  ·
    refine ⟨302242602729921547683083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 805980273946457460488221 302242602729921547683083)
    ·
      refine ⟨453363904094882321524625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302242602729921547683083 453363904094882321524625)
      ·
        refine ⟨340022928071161741143469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453363904094882321524625 340022928071161741143469)
        ·
          refine ⟨127508598026685652928801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340022928071161741143469 127508598026685652928801)
          ·
            refine ⟨95631448520014239696601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127508598026685652928801 95631448520014239696601)
            ·
              refine ⟨71723586390010679772451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95631448520014239696601 71723586390010679772451)
              ·
                refine ⟨107585379585016019658677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71723586390010679772451 107585379585016019658677)
                ·
                  refine ⟨10086129336095251843001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107585379585016019658677 10086129336095251843001)
                  ·
                    rfl

theorem cell21_44196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_44196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44196 prefixEnd_44196 := by exact prefixLift 44196
  have htrace : WordTrace (prefixWord ++ tailWord_44196) baseStart_44196 baseEnd_44196 := by
    simpa [prefixWord, tailWord_44196, baseEnd_44196] using wordTrace_append hprefix tailTrace_44196
  have hstable : (prefixWord ++ tailWord_44196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44196).length < 2 ^ (prefixWord ++ tailWord_44196).sum := by decide
  have hdescent : baseEnd_44196 < baseStart_44196 := by decide
  rcases family_descends (prefixWord ++ tailWord_44196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44255 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 5]
def baseStart_44255 : Nat := 118140960795 + 44255 * 2 ^ 59
def prefixEnd_44255 : Nat := 4983230072969 + 3 ^ 40 * 44255 * 2
def baseEnd_44255 : Nat := 10099593939924260359547

theorem tailTrace_44255 : CollatzResearch.WordTrace tailWord_44255 prefixEnd_44255 10099593939924260359547 := by
  unfold tailWord_44255
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614112454679167997374219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1076074969786111998249479 1614112454679167997374219)
  ·
    refine ⟨2421168682018751996061329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1614112454679167997374219 2421168682018751996061329)
    ·
      refine ⟨1815876511514063997045997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2421168682018751996061329 1815876511514063997045997)
      ·
        refine ⟨680953691817773998892249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1815876511514063997045997 680953691817773998892249)
        ·
          refine ⟨510715268863330499169187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680953691817773998892249 510715268863330499169187)
          ·
            refine ⟨766072903294995748753781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510715268863330499169187 766072903294995748753781)
            ·
              refine ⟨71819334683905851445667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 766072903294995748753781 71819334683905851445667)
              ·
                refine ⟨107729002025858777168501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71819334683905851445667 107729002025858777168501)
                ·
                  refine ⟨10099593939924260359547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107729002025858777168501 10099593939924260359547)
                  ·
                    rfl

theorem cell21_44255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 5].length) (baseStart_44255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44255 prefixEnd_44255 := by exact prefixLift 44255
  have htrace : WordTrace (prefixWord ++ tailWord_44255) baseStart_44255 baseEnd_44255 := by
    simpa [prefixWord, tailWord_44255, baseEnd_44255] using wordTrace_append hprefix tailTrace_44255
  have hstable : (prefixWord ++ tailWord_44255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44255).length < 2 ^ (prefixWord ++ tailWord_44255).sum := by decide
  have hdescent : baseEnd_44255 < baseStart_44255 := by decide
  rcases family_descends (prefixWord ++ tailWord_44255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44261 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 4]
def baseStart_44261 : Nat := 118140960795 + 44261 * 2 ^ 59
def prefixEnd_44261 : Nat := 4983230072969 + 3 ^ 40 * 44261 * 2
def baseEnd_44261 : Nat := 10100963221669583259535

theorem tailTrace_44261 : CollatzResearch.WordTrace tailWord_44261 prefixEnd_44261 10100963221669583259535 := by
  unfold tailWord_44261
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614331292657431022092637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1076220861771620681395091 1614331292657431022092637)
  ·
    refine ⟨605374234746536633284739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1614331292657431022092637 605374234746536633284739)
    ·
      refine ⟨908061352119804949927109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605374234746536633284739 908061352119804949927109)
      ·
        refine ⟨170261503522463428111333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 908061352119804949927109 170261503522463428111333)
        ·
          refine ⟨31924031910461892770875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170261503522463428111333 31924031910461892770875)
          ·
            refine ⟨47886047865692839156313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31924031910461892770875 47886047865692839156313)
            ·
              refine ⟨35914535899269629367235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47886047865692839156313 35914535899269629367235)
              ·
                refine ⟨53871803848904444050853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35914535899269629367235 53871803848904444050853)
                ·
                  refine ⟨10100963221669583259535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53871803848904444050853 10100963221669583259535)
                  ·
                    rfl

theorem cell21_44261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_44261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44261 prefixEnd_44261 := by exact prefixLift 44261
  have htrace : WordTrace (prefixWord ++ tailWord_44261) baseStart_44261 baseEnd_44261 := by
    simpa [prefixWord, tailWord_44261, baseEnd_44261] using wordTrace_append hprefix tailTrace_44261
  have hstable : (prefixWord ++ tailWord_44261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44261).length < 2 ^ (prefixWord ++ tailWord_44261).sum := by decide
  have hdescent : baseEnd_44261 < baseStart_44261 := by decide
  rcases family_descends (prefixWord ++ tailWord_44261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44317 : List Nat := [1, 4, 2, 3, 1, 1, 3, 6]
def baseStart_44317 : Nat := 118140960795 + 44317 * 2 ^ 59
def prefixEnd_44317 : Nat := 4983230072969 + 3 ^ 40 * 44317 * 2
def baseEnd_44317 : Nat := 3371247728208643442029

theorem tailTrace_44317 : CollatzResearch.WordTrace tailWord_44317 prefixEnd_44317 3371247728208643442029 := by
  unfold tailWord_44317
  simp only [CollatzResearch.WordTrace]
  refine ⟨1616373780454552586131205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1077582520303035057420803 1616373780454552586131205)
  ·
    refine ⟨303070083835228609899601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1616373780454552586131205 303070083835228609899601)
    ·
      refine ⟨227302562876421457424701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303070083835228609899601 227302562876421457424701)
      ·
        refine ⟨85238461078658046534263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227302562876421457424701 85238461078658046534263)
        ·
          refine ⟨127857691617987069801395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85238461078658046534263 127857691617987069801395)
          ·
            refine ⟨191786537426980604702093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127857691617987069801395 191786537426980604702093)
            ·
              refine ⟨71919951535117726763285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191786537426980604702093 71919951535117726763285)
              ·
                refine ⟨3371247728208643442029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71919951535117726763285 3371247728208643442029)
                ·
                  rfl

theorem cell21_44317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 6].length) (baseStart_44317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44317 prefixEnd_44317 := by exact prefixLift 44317
  have htrace : WordTrace (prefixWord ++ tailWord_44317) baseStart_44317 baseEnd_44317 := by
    simpa [prefixWord, tailWord_44317, baseEnd_44317] using wordTrace_append hprefix tailTrace_44317
  have hstable : (prefixWord ++ tailWord_44317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44317).length < 2 ^ (prefixWord ++ tailWord_44317).sum := by decide
  have hdescent : baseEnd_44317 < baseStart_44317 := by decide
  rcases family_descends (prefixWord ++ tailWord_44317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44348 : List Nat := [2, 2, 2, 2, 1, 3, 1, 5, 3]
def baseStart_44348 : Nat := 118140960795 + 44348 * 2 ^ 59
def prefixEnd_44348 : Nat := 4983230072969 + 3 ^ 40 * 44348 * 2
def baseEnd_44348 : Nat := 10120817806976765309357

theorem tailTrace_44348 : CollatzResearch.WordTrace tailWord_44348 prefixEnd_44348 10120817806976765309357 := by
  unfold tailWord_44348
  simp only [CollatzResearch.WordTrace]
  refine ⟨808752221671122440254849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1078336295561496587006465 808752221671122440254849)
  ·
    refine ⟨606564166253341830191137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 808752221671122440254849 606564166253341830191137)
    ·
      refine ⟨454923124690006372643353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 606564166253341830191137 454923124690006372643353)
      ·
        refine ⟨341192343517504779482515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454923124690006372643353 341192343517504779482515)
        ·
          refine ⟨511788515276257169223773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341192343517504779482515 511788515276257169223773)
          ·
            refine ⟨191920693228596438458915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 511788515276257169223773 191920693228596438458915)
            ·
              refine ⟨287881039842894657688373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191920693228596438458915 287881039842894657688373)
              ·
                refine ⟨26988847485271374158285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287881039842894657688373 26988847485271374158285)
                ·
                  refine ⟨10120817806976765309357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26988847485271374158285 10120817806976765309357)
                  ·
                    rfl

theorem cell21_44348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_44348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44348 prefixEnd_44348 := by exact prefixLift 44348
  have htrace : WordTrace (prefixWord ++ tailWord_44348) baseStart_44348 baseEnd_44348 := by
    simpa [prefixWord, tailWord_44348, baseEnd_44348] using wordTrace_append hprefix tailTrace_44348
  have hstable : (prefixWord ++ tailWord_44348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44348).length < 2 ^ (prefixWord ++ tailWord_44348).sum := by decide
  have hdescent : baseEnd_44348 < baseStart_44348 := by decide
  rcases family_descends (prefixWord ++ tailWord_44348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44421 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 6]
def baseStart_44421 : Nat := 118140960795 + 44421 * 2 ^ 59
def prefixEnd_44421 : Nat := 4983230072969 + 3 ^ 40 * 44421 * 2
def baseEnd_44421 : Nat := 10137477401544860592541

theorem tailTrace_44421 : CollatzResearch.WordTrace tailWord_44421 prefixEnd_44421 10137477401544860592541 := by
  unfold tailWord_44421
  simp only [CollatzResearch.WordTrace]
  refine ⟨1620166972077778347917117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1080111314718518898611411 1620166972077778347917117)
  ·
    refine ⟨607562614529166880468919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1620166972077778347917117 607562614529166880468919)
    ·
      refine ⟨911343921793750320703379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607562614529166880468919 911343921793750320703379)
      ·
        refine ⟨1367015882690625481055069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911343921793750320703379 1367015882690625481055069)
        ·
          refine ⟨512630956008984555395651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1367015882690625481055069 512630956008984555395651)
          ·
            refine ⟨768946434013476833093477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512630956008984555395651 768946434013476833093477)
            ·
              refine ⟨144177456377526906205027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 768946434013476833093477 144177456377526906205027)
              ·
                refine ⟨216266184566290359307541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144177456377526906205027 216266184566290359307541)
                ·
                  refine ⟨10137477401544860592541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 216266184566290359307541 10137477401544860592541)
                  ·
                    rfl

theorem cell21_44421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_44421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44421 prefixEnd_44421 := by exact prefixLift 44421
  have htrace : WordTrace (prefixWord ++ tailWord_44421) baseStart_44421 baseEnd_44421 := by
    simpa [prefixWord, tailWord_44421, baseEnd_44421] using wordTrace_append hprefix tailTrace_44421
  have hstable : (prefixWord ++ tailWord_44421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44421).length < 2 ^ (prefixWord ++ tailWord_44421).sum := by decide
  have hdescent : baseEnd_44421 < baseStart_44421 := by decide
  rcases family_descends (prefixWord ++ tailWord_44421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44424 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 5]
def baseStart_44424 : Nat := 118140960795 + 44424 * 2 ^ 59
def prefixEnd_44424 : Nat := 4983230072969 + 3 ^ 40 * 44424 * 2
def baseEnd_44424 : Nat := 10138162042417522042535

theorem tailTrace_44424 : CollatzResearch.WordTrace tailWord_44424 prefixEnd_44424 10138162042417522042535 := by
  unfold tailWord_44424
  simp only [CollatzResearch.WordTrace]
  refine ⟨810138195533454930138163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1080184260711273240184217 810138195533454930138163)
  ·
    refine ⟨1215207293300182395207245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810138195533454930138163 1215207293300182395207245)
    ·
      refine ⟨455702734987568398202717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1215207293300182395207245 455702734987568398202717)
      ·
        refine ⟨170888525620338149326019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455702734987568398202717 170888525620338149326019)
        ·
          refine ⟨256332788430507223989029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170888525620338149326019 256332788430507223989029)
          ·
            refine ⟨48062397830720104497943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256332788430507223989029 48062397830720104497943)
            ·
              refine ⟨72093596746080156746915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48062397830720104497943 72093596746080156746915)
              ·
                refine ⟨108140395119120235120373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72093596746080156746915 108140395119120235120373)
                ·
                  refine ⟨10138162042417522042535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108140395119120235120373 10138162042417522042535)
                  ·
                    rfl

theorem cell21_44424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_44424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44424 prefixEnd_44424 := by exact prefixLift 44424
  have htrace : WordTrace (prefixWord ++ tailWord_44424) baseStart_44424 baseEnd_44424 := by
    simpa [prefixWord, tailWord_44424, baseEnd_44424] using wordTrace_append hprefix tailTrace_44424
  have hstable : (prefixWord ++ tailWord_44424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44424).length < 2 ^ (prefixWord ++ tailWord_44424).sum := by decide
  have hdescent : baseEnd_44424 < baseStart_44424 := by decide
  rcases family_descends (prefixWord ++ tailWord_44424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44466 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_44466 : Nat := 118140960795 + 44466 * 2 ^ 59
def prefixEnd_44466 : Nat := 4983230072969 + 3 ^ 40 * 44466 * 2
def baseEnd_44466 : Nat := 10147747014634782342449

theorem tailTrace_44466 : CollatzResearch.WordTrace tailWord_44466 prefixEnd_44466 10147747014634782342449 := by
  unfold tailWord_44466
  simp only [CollatzResearch.WordTrace]
  refine ⟨405452064228687758326313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1081205504609834022203501 405452064228687758326313)
  ·
    refine ⟨304089048171515818744735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 405452064228687758326313 304089048171515818744735)
    ·
      refine ⟨456133572257273728117103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304089048171515818744735 456133572257273728117103)
      ·
        refine ⟨684200358385910592175655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456133572257273728117103 684200358385910592175655)
        ·
          refine ⟨1026300537578865888263483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684200358385910592175655 1026300537578865888263483)
          ·
            refine ⟨1539450806368298832395225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026300537578865888263483 1539450806368298832395225)
            ·
              refine ⟨1154588104776224124296419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539450806368298832395225 1154588104776224124296419)
              ·
                refine ⟨1731882157164336186444629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154588104776224124296419 1731882157164336186444629)
                ·
                  refine ⟨10147747014634782342449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1731882157164336186444629 10147747014634782342449)
                  ·
                    rfl

theorem cell21_44466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_44466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44466 prefixEnd_44466 := by exact prefixLift 44466
  have htrace : WordTrace (prefixWord ++ tailWord_44466) baseStart_44466 baseEnd_44466 := by
    simpa [prefixWord, tailWord_44466, baseEnd_44466] using wordTrace_append hprefix tailTrace_44466
  have hstable : (prefixWord ++ tailWord_44466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44466).length < 2 ^ (prefixWord ++ tailWord_44466).sum := by decide
  have hdescent : baseEnd_44466 < baseStart_44466 := by decide
  rcases family_descends (prefixWord ++ tailWord_44466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44500 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 5]
def baseStart_44500 : Nat := 118140960795 + 44500 * 2 ^ 59
def prefixEnd_44500 : Nat := 4983230072969 + 3 ^ 40 * 44500 * 2
def baseEnd_44500 : Nat := 10155506277858278775713

theorem tailTrace_44500 : CollatzResearch.WordTrace tailWord_44500 prefixEnd_44500 10155506277858278775713 := by
  unfold tailWord_44500
  simp only [CollatzResearch.WordTrace]
  refine ⟨811524169395787420021477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1082032225861049893361969 811524169395787420021477)
  ·
    refine ⟨152160781761710141254027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 811524169395787420021477 152160781761710141254027)
    ·
      refine ⟨228241172642565211881041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152160781761710141254027 228241172642565211881041)
      ·
        refine ⟨171180879481923908910781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228241172642565211881041 171180879481923908910781)
        ·
          refine ⟨64192829805721465841543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171180879481923908910781 64192829805721465841543)
          ·
            refine ⟨96289244708582198762315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64192829805721465841543 96289244708582198762315)
            ·
              refine ⟨144433867062873298143473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96289244708582198762315 144433867062873298143473)
              ·
                refine ⟨108325400297154973607605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144433867062873298143473 108325400297154973607605)
                ·
                  refine ⟨10155506277858278775713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108325400297154973607605 10155506277858278775713)
                  ·
                    rfl

theorem cell21_44500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_44500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44500 prefixEnd_44500 := by exact prefixLift 44500
  have htrace : WordTrace (prefixWord ++ tailWord_44500) baseStart_44500 baseEnd_44500 := by
    simpa [prefixWord, tailWord_44500, baseEnd_44500] using wordTrace_append hprefix tailTrace_44500
  have hstable : (prefixWord ++ tailWord_44500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44500).length < 2 ^ (prefixWord ++ tailWord_44500).sum := by decide
  have hdescent : baseEnd_44500 < baseStart_44500 := by decide
  rcases family_descends (prefixWord ++ tailWord_44500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44517 : List Nat := [1, 3, 1, 5, 1, 2, 2, 3, 3]
def baseStart_44517 : Nat := 118140960795 + 44517 * 2 ^ 59
def prefixEnd_44517 : Nat := 4983230072969 + 3 ^ 40 * 44517 * 2
def baseEnd_44517 : Nat := 10159385909470026992345

theorem tailTrace_44517 : CollatzResearch.WordTrace tailWord_44517 prefixEnd_44517 10159385909470026992345 := by
  unfold tailWord_44517
  simp only [CollatzResearch.WordTrace]
  refine ⟨1623668379729986743411805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1082445586486657828941203 1623668379729986743411805)
  ·
    refine ⟨608875642398745028779427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1623668379729986743411805 608875642398745028779427)
    ·
      refine ⟨913313463598117543169141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 608875642398745028779427 913313463598117543169141)
      ·
        refine ⟨85623137212323519672107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 913313463598117543169141 85623137212323519672107)
        ·
          refine ⟨128434705818485279508161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85623137212323519672107 128434705818485279508161)
          ·
            refine ⟨96326029363863959631121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128434705818485279508161 96326029363863959631121)
            ·
              refine ⟨72244522022897969723341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96326029363863959631121 72244522022897969723341)
              ·
                refine ⟨27091695758586738646253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72244522022897969723341 27091695758586738646253)
                ·
                  refine ⟨10159385909470026992345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27091695758586738646253 10159385909470026992345)
                  ·
                    rfl

theorem cell21_44517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_44517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44517 prefixEnd_44517 := by exact prefixLift 44517
  have htrace : WordTrace (prefixWord ++ tailWord_44517) baseStart_44517 baseEnd_44517 := by
    simpa [prefixWord, tailWord_44517, baseEnd_44517] using wordTrace_append hprefix tailTrace_44517
  have hstable : (prefixWord ++ tailWord_44517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44517).length < 2 ^ (prefixWord ++ tailWord_44517).sum := by decide
  have hdescent : baseEnd_44517 < baseStart_44517 := by decide
  rcases family_descends (prefixWord ++ tailWord_44517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44548 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 4]
def baseStart_44548 : Nat := 118140960795 + 44548 * 2 ^ 59
def prefixEnd_44548 : Nat := 4983230072969 + 3 ^ 40 * 44548 * 2
def baseEnd_44548 : Nat := 10166460531820861975615

theorem tailTrace_44548 : CollatzResearch.WordTrace tailWord_44548 prefixEnd_44548 10166460531820861975615 := by
  unfold tailWord_44548
  simp only [CollatzResearch.WordTrace]
  refine ⟨812399521308839518895149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1083199361745119358526865 812399521308839518895149)
  ·
    refine ⟨304649820490814819585681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 812399521308839518895149 304649820490814819585681)
    ·
      refine ⟨228487365368111114689261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304649820490814819585681 228487365368111114689261)
      ·
        refine ⟨85682762013041668008473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228487365368111114689261 85682762013041668008473)
        ·
          refine ⟨64262071509781251006355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85682762013041668008473 64262071509781251006355)
          ·
            refine ⟨96393107264671876509533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64262071509781251006355 96393107264671876509533)
            ·
              refine ⟨36147415224251953691075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96393107264671876509533 36147415224251953691075)
              ·
                refine ⟨54221122836377930536613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36147415224251953691075 54221122836377930536613)
                ·
                  refine ⟨10166460531820861975615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54221122836377930536613 10166460531820861975615)
                  ·
                    rfl

theorem cell21_44548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_44548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44548 prefixEnd_44548 := by exact prefixLift 44548
  have htrace : WordTrace (prefixWord ++ tailWord_44548) baseStart_44548 baseEnd_44548 := by
    simpa [prefixWord, tailWord_44548, baseEnd_44548] using wordTrace_append hprefix tailTrace_44548
  have hstable : (prefixWord ++ tailWord_44548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44548).length < 2 ^ (prefixWord ++ tailWord_44548).sum := by decide
  have hdescent : baseEnd_44548 < baseStart_44548 := by decide
  rcases family_descends (prefixWord ++ tailWord_44548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44573 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 8]
def baseStart_44573 : Nat := 118140960795 + 44573 * 2 ^ 59
def prefixEnd_44573 : Nat := 4983230072969 + 3 ^ 40 * 44573 * 2
def baseEnd_44573 : Nat := 10172165872426374058897

theorem tailTrace_44573 : CollatzResearch.WordTrace tailWord_44573 prefixEnd_44573 10172165872426374058897 := by
  unfold tailWord_44573
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625710867527108307450373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1083807245018072204966915 1625710867527108307450373)
  ·
    refine ⟨304820787661332807646945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1625710867527108307450373 304820787661332807646945)
    ·
      refine ⟨228615590745999605735209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 304820787661332807646945 228615590745999605735209)
      ·
        refine ⟨171461693059499704301407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228615590745999605735209 171461693059499704301407)
        ·
          refine ⟨257192539589249556452111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171461693059499704301407 257192539589249556452111)
          ·
            refine ⟨385788809383874334678167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257192539589249556452111 385788809383874334678167)
            ·
              refine ⟨578683214075811502017251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385788809383874334678167 578683214075811502017251)
              ·
                refine ⟨868024821113717253025877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578683214075811502017251 868024821113717253025877)
                ·
                  refine ⟨10172165872426374058897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 868024821113717253025877 10172165872426374058897)
                  ·
                    rfl

theorem cell21_44573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_44573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44573 prefixEnd_44573 := by exact prefixLift 44573
  have htrace : WordTrace (prefixWord ++ tailWord_44573) baseStart_44573 baseEnd_44573 := by
    simpa [prefixWord, tailWord_44573, baseEnd_44573] using wordTrace_append hprefix tailTrace_44573
  have hstable : (prefixWord ++ tailWord_44573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44573).length < 2 ^ (prefixWord ++ tailWord_44573).sum := by decide
  have hdescent : baseEnd_44573 < baseStart_44573 := by decide
  rcases family_descends (prefixWord ++ tailWord_44573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44590 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_44590 : Nat := 118140960795 + 44590 * 2 ^ 59
def prefixEnd_44590 : Nat := 4983230072969 + 3 ^ 40 * 44590 * 2
def baseEnd_44590 : Nat := 10176045504038122275529

theorem tailTrace_44590 : CollatzResearch.WordTrace tailWord_44590 prefixEnd_44590 10176045504038122275529 := by
  unfold tailWord_44590
  simp only [CollatzResearch.WordTrace]
  refine ⟨203291363558190026352403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1084220605643680140546149 203291363558190026352403)
  ·
    refine ⟨304937045337285039528605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203291363558190026352403 304937045337285039528605)
    ·
      refine ⟨114351392001481889823227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304937045337285039528605 114351392001481889823227)
      ·
        refine ⟨171527088002222834734841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114351392001481889823227 171527088002222834734841)
        ·
          refine ⟨128645316001667126051131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171527088002222834734841 128645316001667126051131)
          ·
            refine ⟨192967974002500689076697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128645316001667126051131 192967974002500689076697)
            ·
              refine ⟨144725980501875516807523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192967974002500689076697 144725980501875516807523)
              ·
                refine ⟨217088970752813275211285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144725980501875516807523 217088970752813275211285)
                ·
                  refine ⟨10176045504038122275529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 217088970752813275211285 10176045504038122275529)
                  ·
                    rfl

theorem cell21_44590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_44590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44590 prefixEnd_44590 := by exact prefixLift 44590
  have htrace : WordTrace (prefixWord ++ tailWord_44590) baseStart_44590 baseEnd_44590 := by
    simpa [prefixWord, tailWord_44590, baseEnd_44590] using wordTrace_append hprefix tailTrace_44590
  have hstable : (prefixWord ++ tailWord_44590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44590).length < 2 ^ (prefixWord ++ tailWord_44590).sum := by decide
  have hdescent : baseEnd_44590 < baseStart_44590 := by decide
  rcases family_descends (prefixWord ++ tailWord_44590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44607 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 4]
def baseStart_44607 : Nat := 118140960795 + 44607 * 2 ^ 59
def prefixEnd_44607 : Nat := 4983230072969 + 3 ^ 40 * 44607 * 2
def baseEnd_44607 : Nat := 10179925135649870492161

theorem tailTrace_44607 : CollatzResearch.WordTrace tailWord_44607 prefixEnd_44607 10179925135649870492161 := by
  unfold tailWord_44607
  simp only [CollatzResearch.WordTrace]
  refine ⟨1626950949403932114188075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1084633966269288076125383 1626950949403932114188075)
  ·
    refine ⟨2440426424105898171282113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1626950949403932114188075 2440426424105898171282113)
    ·
      refine ⟨1830319818079423628461585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2440426424105898171282113 1830319818079423628461585)
      ·
        refine ⟨1372739863559567721346189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1830319818079423628461585 1372739863559567721346189)
        ·
          refine ⟨514777448834837895504821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1372739863559567721346189 514777448834837895504821)
          ·
            refine ⟨48260385828266052703577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 514777448834837895504821 48260385828266052703577)
            ·
              refine ⟨36195289371199539527683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48260385828266052703577 36195289371199539527683)
              ·
                refine ⟨54292934056799309291525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36195289371199539527683 54292934056799309291525)
                ·
                  refine ⟨10179925135649870492161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54292934056799309291525 10179925135649870492161)
                  ·
                    rfl

theorem cell21_44607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 4].length) (baseStart_44607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44607 prefixEnd_44607 := by exact prefixLift 44607
  have htrace : WordTrace (prefixWord ++ tailWord_44607) baseStart_44607 baseEnd_44607 := by
    simpa [prefixWord, tailWord_44607, baseEnd_44607] using wordTrace_append hprefix tailTrace_44607
  have hstable : (prefixWord ++ tailWord_44607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44607).length < 2 ^ (prefixWord ++ tailWord_44607).sum := by decide
  have hdescent : baseEnd_44607 < baseStart_44607 := by decide
  rcases family_descends (prefixWord ++ tailWord_44607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44618 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_44618 : Nat := 118140960795 + 44618 * 2 ^ 59
def prefixEnd_44618 : Nat := 4983230072969 + 3 ^ 40 * 44618 * 2
def baseEnd_44618 : Nat := 10182435485516295808805

theorem tailTrace_44618 : CollatzResearch.WordTrace tailWord_44618 prefixEnd_44618 10182435485516295808805 := by
  unfold tailWord_44618
  simp only [CollatzResearch.WordTrace]
  refine ⟨406838038091020248209627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1084901434909387328559005 406838038091020248209627)
  ·
    refine ⟨610257057136530372314441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 406838038091020248209627 610257057136530372314441)
    ·
      refine ⟨457692792852397779235831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 610257057136530372314441 457692792852397779235831)
      ·
        refine ⟨686539189278596668853747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457692792852397779235831 686539189278596668853747)
        ·
          refine ⟨1029808783917895003280621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686539189278596668853747 1029808783917895003280621)
          ·
            refine ⟨386178293969210626230233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1029808783917895003280621 386178293969210626230233)
            ·
              refine ⟨289633720476907969672675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386178293969210626230233 289633720476907969672675)
              ·
                refine ⟨434450580715361954509013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289633720476907969672675 434450580715361954509013)
                ·
                  refine ⟨10182435485516295808805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 434450580715361954509013 10182435485516295808805)
                  ·
                    rfl

theorem cell21_44618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_44618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44618 prefixEnd_44618 := by exact prefixLift 44618
  have htrace : WordTrace (prefixWord ++ tailWord_44618) baseStart_44618 baseEnd_44618 := by
    simpa [prefixWord, tailWord_44618, baseEnd_44618] using wordTrace_append hprefix tailTrace_44618
  have hstable : (prefixWord ++ tailWord_44618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44618).length < 2 ^ (prefixWord ++ tailWord_44618).sum := by decide
  have hdescent : baseEnd_44618 < baseStart_44618 := by decide
  rcases family_descends (prefixWord ++ tailWord_44618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44649 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 4]
def baseStart_44649 : Nat := 118140960795 + 44649 * 2 ^ 59
def prefixEnd_44649 : Nat := 4983230072969 + 3 ^ 40 * 44649 * 2
def baseEnd_44649 : Nat := 10189510107867130792075

theorem tailTrace_44649 : CollatzResearch.WordTrace tailWord_44649 prefixEnd_44649 10189510107867130792075 := by
  unfold tailWord_44649
  simp only [CollatzResearch.WordTrace]
  refine ⟨1628482815251773287217001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1085655210167848858144667 1628482815251773287217001)
  ·
    refine ⟨1221362111438829965412751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1628482815251773287217001 1221362111438829965412751)
    ·
      refine ⟨1832043167158244948119127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1221362111438829965412751 1832043167158244948119127)
      ·
        refine ⟨2748064750737367422178691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1832043167158244948119127 2748064750737367422178691)
        ·
          refine ⟨4122097126106051133268037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2748064750737367422178691 4122097126106051133268037)
          ·
            refine ⟨772893211144884587487757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4122097126106051133268037 772893211144884587487757)
            ·
              refine ⟨289834954179331720307909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 772893211144884587487757 289834954179331720307909)
              ·
                refine ⟨54344053908624697557733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 289834954179331720307909 54344053908624697557733)
                ·
                  refine ⟨10189510107867130792075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54344053908624697557733 10189510107867130792075)
                  ·
                    rfl

theorem cell21_44649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_44649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44649 prefixEnd_44649 := by exact prefixLift 44649
  have htrace : WordTrace (prefixWord ++ tailWord_44649) baseStart_44649 baseEnd_44649 := by
    simpa [prefixWord, tailWord_44649, baseEnd_44649] using wordTrace_append hprefix tailTrace_44649
  have hstable : (prefixWord ++ tailWord_44649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44649).length < 2 ^ (prefixWord ++ tailWord_44649).sum := by decide
  have hdescent : baseEnd_44649 < baseStart_44649 := by decide
  rcases family_descends (prefixWord ++ tailWord_44649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44700 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 4]
def baseStart_44700 : Nat := 118140960795 + 44700 * 2 ^ 59
def prefixEnd_44700 : Nat := 4983230072969 + 3 ^ 40 * 44700 * 2
def baseEnd_44700 : Nat := 10201149002702375441971

theorem tailTrace_44700 : CollatzResearch.WordTrace tailWord_44700 prefixEnd_44700 10201149002702375441971 := by
  unfold tailWord_44700
  simp only [CollatzResearch.WordTrace]
  refine ⟨815171469033504498661777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1086895292044672664882369 815171469033504498661777)
  ·
    refine ⟨611378601775128373996333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 815171469033504498661777 611378601775128373996333)
    ·
      refine ⟨229266975665673140248625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 611378601775128373996333 229266975665673140248625)
      ·
        refine ⟨171950231749254855186469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229266975665673140248625 171950231749254855186469)
        ·
          refine ⟨32240668452985285347463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171950231749254855186469 32240668452985285347463)
          ·
            refine ⟨48361002679477928021195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32240668452985285347463 48361002679477928021195)
            ·
              refine ⟨72541504019216892031793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48361002679477928021195 72541504019216892031793)
              ·
                refine ⟨54406128014412669023845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72541504019216892031793 54406128014412669023845)
                ·
                  refine ⟨10201149002702375441971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54406128014412669023845 10201149002702375441971)
                  ·
                    rfl

theorem cell21_44700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_44700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44700 prefixEnd_44700 := by exact prefixLift 44700
  have htrace : WordTrace (prefixWord ++ tailWord_44700) baseStart_44700 baseEnd_44700 := by
    simpa [prefixWord, tailWord_44700, baseEnd_44700] using wordTrace_append hprefix tailTrace_44700
  have hstable : (prefixWord ++ tailWord_44700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44700).length < 2 ^ (prefixWord ++ tailWord_44700).sum := by decide
  have hdescent : baseEnd_44700 < baseStart_44700 := by decide
  rcases family_descends (prefixWord ++ tailWord_44700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44756 : List Nat := [2, 4, 1, 3, 1, 1, 9]
def baseStart_44756 : Nat := 118140960795 + 44756 * 2 ^ 59
def prefixEnd_44756 : Nat := 4983230072969 + 3 ^ 40 * 44756 * 2
def baseEnd_44756 : Nat := 1134880996184302500947

theorem tailTrace_44756 : CollatzResearch.WordTrace tailWord_44756 prefixEnd_44756 1134880996184302500947 := by
  unfold tailWord_44756
  simp only [CollatzResearch.WordTrace]
  refine ⟨816192712932065280681061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1088256950576087040908081 816192712932065280681061)
  ·
    refine ⟨153036133674762240127699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 816192712932065280681061 153036133674762240127699)
    ·
      refine ⟨229554200512143360191549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153036133674762240127699 229554200512143360191549)
      ·
        refine ⟨86082825192053760071831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229554200512143360191549 86082825192053760071831)
        ·
          refine ⟨129124237788080640107747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86082825192053760071831 129124237788080640107747)
          ·
            refine ⟨193686356682120960161621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129124237788080640107747 193686356682120960161621)
            ·
              refine ⟨1134880996184302500947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 193686356682120960161621 1134880996184302500947)
              ·
                rfl

theorem cell21_44756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 9].length) (baseStart_44756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44756 prefixEnd_44756 := by exact prefixLift 44756
  have htrace : WordTrace (prefixWord ++ tailWord_44756) baseStart_44756 baseEnd_44756 := by
    simpa [prefixWord, tailWord_44756, baseEnd_44756] using wordTrace_append hprefix tailTrace_44756
  have hstable : (prefixWord ++ tailWord_44756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44756).length < 2 ^ (prefixWord ++ tailWord_44756).sum := by decide
  have hdescent : baseEnd_44756 < baseStart_44756 := by decide
  rcases family_descends (prefixWord ++ tailWord_44756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44784 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_44784 : Nat := 118140960795 + 44784 * 2 ^ 59
def prefixEnd_44784 : Nat := 4983230072969 + 3 ^ 40 * 44784 * 2
def baseEnd_44784 : Nat := 10220318947136896041799

theorem tailTrace_44784 : CollatzResearch.WordTrace tailWord_44784 prefixEnd_44784 10220318947136896041799 := by
  unfold tailWord_44784
  simp only [CollatzResearch.WordTrace]
  refine ⟨816703334881345671690703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1088937779841794228920937 816703334881345671690703)
  ·
    refine ⟨1225055002322018507536055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 816703334881345671690703 1225055002322018507536055)
    ·
      refine ⟨1837582503483027761304083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1225055002322018507536055 1837582503483027761304083)
      ·
        refine ⟨2756373755224541641956125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1837582503483027761304083 2756373755224541641956125)
        ·
          refine ⟨1033640158209203115733547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2756373755224541641956125 1033640158209203115733547)
          ·
            refine ⟨1550460237313804673600321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033640158209203115733547 1550460237313804673600321)
            ·
              refine ⟨1162845177985353505200241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550460237313804673600321 1162845177985353505200241)
              ·
                refine ⟨872133883489015128900181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162845177985353505200241 872133883489015128900181)
                ·
                  refine ⟨10220318947136896041799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 872133883489015128900181 10220318947136896041799)
                  ·
                    rfl

theorem cell21_44784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_44784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44784 prefixEnd_44784 := by exact prefixLift 44784
  have htrace : WordTrace (prefixWord ++ tailWord_44784) baseStart_44784 baseEnd_44784 := by
    simpa [prefixWord, tailWord_44784, baseEnd_44784] using wordTrace_append hprefix tailTrace_44784
  have hstable : (prefixWord ++ tailWord_44784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44784).length < 2 ^ (prefixWord ++ tailWord_44784).sum := by decide
  have hdescent : baseEnd_44784 < baseStart_44784 := by decide
  rcases family_descends (prefixWord ++ tailWord_44784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44813 : List Nat := [1, 7, 2, 1, 1, 2, 2, 2, 3]
def baseStart_44813 : Nat := 118140960795 + 44813 * 2 ^ 59
def prefixEnd_44813 : Nat := 4983230072969 + 3 ^ 40 * 44813 * 2
def baseEnd_44813 : Nat := 10226937142239290058407

theorem tailTrace_44813 : CollatzResearch.WordTrace tailWord_44813 prefixEnd_44813 10226937142239290058407 := by
  unfold tailWord_44813
  simp only [CollatzResearch.WordTrace]
  refine ⟨1634464386657629296187093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1089642924438419530791395 1634464386657629296187093)
  ·
    refine ⟨38307759062288186629385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 1634464386657629296187093 38307759062288186629385)
    ·
      refine ⟨28730819296716139972039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38307759062288186629385 28730819296716139972039)
      ·
        refine ⟨43096228945074209958059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28730819296716139972039 43096228945074209958059)
        ·
          refine ⟨64644343417611314937089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43096228945074209958059 64644343417611314937089)
          ·
            refine ⟨48483257563208486202817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64644343417611314937089 48483257563208486202817)
            ·
              refine ⟨36362443172406364652113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48483257563208486202817 36362443172406364652113)
              ·
                refine ⟨27271832379304773489085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36362443172406364652113 27271832379304773489085)
                ·
                  refine ⟨10226937142239290058407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27271832379304773489085 10226937142239290058407)
                  ·
                    rfl

theorem cell21_44813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_44813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44813 prefixEnd_44813 := by exact prefixLift 44813
  have htrace : WordTrace (prefixWord ++ tailWord_44813) baseStart_44813 baseEnd_44813 := by
    simpa [prefixWord, tailWord_44813, baseEnd_44813] using wordTrace_append hprefix tailTrace_44813
  have hstable : (prefixWord ++ tailWord_44813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44813).length < 2 ^ (prefixWord ++ tailWord_44813).sum := by decide
  have hdescent : baseEnd_44813 < baseStart_44813 := by decide
  rcases family_descends (prefixWord ++ tailWord_44813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44821 : List Nat := [1, 3, 2, 1, 2, 5, 2, 2, 3]
def baseStart_44821 : Nat := 118140960795 + 44821 * 2 ^ 59
def prefixEnd_44821 : Nat := 4983230072969 + 3 ^ 40 * 44821 * 2
def baseEnd_44821 : Nat := 10228762851233053925057

theorem tailTrace_44821 : CollatzResearch.WordTrace tailWord_44821 prefixEnd_44821 10228762851233053925057 := by
  unfold tailWord_44821
  simp only [CollatzResearch.WordTrace]
  refine ⟨1634756170628646662478317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1089837447085764441652211 1634756170628646662478317)
  ·
    refine ⟨613033563985742498429369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1634756170628646662478317 613033563985742498429369)
    ·
      refine ⟨459775172989306873822027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 613033563985742498429369 459775172989306873822027)
      ·
        refine ⟨689662759483960310733041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459775172989306873822027 689662759483960310733041)
        ·
          refine ⟨517247069612970233049781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689662759483960310733041 517247069612970233049781)
          ·
            refine ⟨48491912776215959348417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 517247069612970233049781 48491912776215959348417)
            ·
              refine ⟨36368934582161969511313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48491912776215959348417 36368934582161969511313)
              ·
                refine ⟨27276700936621477133485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36368934582161969511313 27276700936621477133485)
                ·
                  refine ⟨10228762851233053925057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27276700936621477133485 10228762851233053925057)
                  ·
                    rfl

theorem cell21_44821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_44821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44821 prefixEnd_44821 := by exact prefixLift 44821
  have htrace : WordTrace (prefixWord ++ tailWord_44821) baseStart_44821 baseEnd_44821 := by
    simpa [prefixWord, tailWord_44821, baseEnd_44821] using wordTrace_append hprefix tailTrace_44821
  have hstable : (prefixWord ++ tailWord_44821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44821).length < 2 ^ (prefixWord ++ tailWord_44821).sum := by decide
  have hdescent : baseEnd_44821 < baseStart_44821 := by decide
  rcases family_descends (prefixWord ++ tailWord_44821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44908 : List Nat := [2, 2, 1, 1, 4, 2, 4, 5]
def baseStart_44908 : Nat := 118140960795 + 44908 * 2 ^ 59
def prefixEnd_44908 : Nat := 4983230072969 + 3 ^ 40 * 44908 * 2
def baseEnd_44908 : Nat := 3416205812180078658293

theorem tailTrace_44908 : CollatzResearch.WordTrace tailWord_44908 prefixEnd_44908 3416205812180078658293 := by
  unfold tailWord_44908
  simp only [CollatzResearch.WordTrace]
  refine ⟨818964660656730260447689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1091952880875640347263585 818964660656730260447689)
  ·
    refine ⟨614223495492547695335767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 818964660656730260447689 614223495492547695335767)
    ·
      refine ⟨921335243238821543003651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614223495492547695335767 921335243238821543003651)
      ·
        refine ⟨1382002864858232314505477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921335243238821543003651 1382002864858232314505477)
        ·
          refine ⟨259125537160918558969777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1382002864858232314505477 259125537160918558969777)
          ·
            refine ⟨194344152870688919227333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259125537160918558969777 194344152870688919227333)
            ·
              refine ⟨36439528663254172355125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194344152870688919227333 36439528663254172355125)
              ·
                refine ⟨3416205812180078658293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36439528663254172355125 3416205812180078658293)
                ·
                  rfl

theorem cell21_44908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_44908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_44908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_44908 prefixEnd_44908 := by exact prefixLift 44908
  have htrace : WordTrace (prefixWord ++ tailWord_44908) baseStart_44908 baseEnd_44908 := by
    simpa [prefixWord, tailWord_44908, baseEnd_44908] using wordTrace_append hprefix tailTrace_44908
  have hstable : (prefixWord ++ tailWord_44908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44908).length < 2 ^ (prefixWord ++ tailWord_44908).sum := by decide
  have hdescent : baseEnd_44908 < baseStart_44908 := by decide
  rcases family_descends (prefixWord ++ tailWord_44908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45046 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_45046 : Nat := 118140960795 + 45046 * 2 ^ 59
def prefixEnd_45046 : Nat := 4983230072969 + 3 ^ 40 * 45046 * 2
def baseEnd_45046 : Nat := 10280110916682662674597

theorem tailTrace_45046 : CollatzResearch.WordTrace tailWord_45046 prefixEnd_45046 10280110916682662674597 := by
  unfold tailWord_45046
  simp only [CollatzResearch.WordTrace]
  refine ⟨102685162175844380588687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1095308396542340059612661 102685162175844380588687)
  ·
    refine ⟨154027743263766570883031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102685162175844380588687 154027743263766570883031)
    ·
      refine ⟨231041614895649856324547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154027743263766570883031 231041614895649856324547)
      ·
        refine ⟨346562422343474784486821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231041614895649856324547 346562422343474784486821)
        ·
          refine ⟨64980454189401522091279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346562422343474784486821 64980454189401522091279)
          ·
            refine ⟨97470681284102283136919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64980454189401522091279 97470681284102283136919)
            ·
              refine ⟨146206021926153424705379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97470681284102283136919 146206021926153424705379)
              ·
                refine ⟨219309032889230137058069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146206021926153424705379 219309032889230137058069)
                ·
                  refine ⟨10280110916682662674597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 219309032889230137058069 10280110916682662674597)
                  ·
                    rfl

theorem cell21_45046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_45046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45046 prefixEnd_45046 := by exact prefixLift 45046
  have htrace : WordTrace (prefixWord ++ tailWord_45046) baseStart_45046 baseEnd_45046 := by
    simpa [prefixWord, tailWord_45046, baseEnd_45046] using wordTrace_append hprefix tailTrace_45046
  have hstable : (prefixWord ++ tailWord_45046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45046).length < 2 ^ (prefixWord ++ tailWord_45046).sum := by decide
  have hdescent : baseEnd_45046 < baseStart_45046 := by decide
  rcases family_descends (prefixWord ++ tailWord_45046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45077 : List Nat := [1, 3, 2, 1, 5, 2, 2, 5]
def baseStart_45077 : Nat := 118140960795 + 45077 * 2 ^ 59
def prefixEnd_45077 : Nat := 4983230072969 + 3 ^ 40 * 45077 * 2
def baseEnd_45077 : Nat := 3429061846344499219289

theorem tailTrace_45077 : CollatzResearch.WordTrace tailWord_45077 prefixEnd_45077 3429061846344499219289 := by
  unfold tailWord_45077
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644093257701202383797485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1096062171800801589198323 1644093257701202383797485)
  ·
    refine ⟨616534971637950893924057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1644093257701202383797485 616534971637950893924057)
    ·
      refine ⟨462401228728463170443043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 616534971637950893924057 462401228728463170443043)
      ·
        refine ⟨693601843092694755664565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462401228728463170443043 693601843092694755664565)
        ·
          refine ⟨65025172789940133343553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 693601843092694755664565 65025172789940133343553)
          ·
            refine ⟨48768879592455100007665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65025172789940133343553 48768879592455100007665)
            ·
              refine ⟨36576659694341325005749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48768879592455100007665 36576659694341325005749)
              ·
                refine ⟨3429061846344499219289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36576659694341325005749 3429061846344499219289)
                ·
                  rfl

theorem cell21_45077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 5].length) (baseStart_45077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45077 prefixEnd_45077 := by exact prefixLift 45077
  have htrace : WordTrace (prefixWord ++ tailWord_45077) baseStart_45077 baseEnd_45077 := by
    simpa [prefixWord, tailWord_45077, baseEnd_45077] using wordTrace_append hprefix tailTrace_45077
  have hstable : (prefixWord ++ tailWord_45077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45077).length < 2 ^ (prefixWord ++ tailWord_45077).sum := by decide
  have hdescent : baseEnd_45077 < baseStart_45077 := by decide
  rcases family_descends (prefixWord ++ tailWord_45077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45167 : List Nat := [1, 1, 2, 1, 3, 5, 1, 4, 3]
def baseStart_45167 : Nat := 118140960795 + 45167 * 2 ^ 59
def prefixEnd_45167 : Nat := 4983230072969 + 3 ^ 40 * 45167 * 2
def baseEnd_45167 : Nat := 10307724765213341157683

theorem tailTrace_45167 : CollatzResearch.WordTrace tailWord_45167 prefixEnd_45167 10307724765213341157683 := by
  unfold tailWord_45167
  simp only [CollatzResearch.WordTrace]
  refine ⟨1647375827375147754573755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1098250551583431836382503 1647375827375147754573755)
  ·
    refine ⟨2471063741062721631860633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1647375827375147754573755 2471063741062721631860633)
    ·
      refine ⟨1853297805797041223895475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2471063741062721631860633 1853297805797041223895475)
      ·
        refine ⟨2779946708695561835843213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853297805797041223895475 2779946708695561835843213)
        ·
          refine ⟨1042480015760835688441205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2779946708695561835843213 1042480015760835688441205)
          ·
            refine ⟨97732501477578345791363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1042480015760835688441205 97732501477578345791363)
            ·
              refine ⟨146598752216367518687045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97732501477578345791363 146598752216367518687045)
              ·
                refine ⟨27487266040568909753821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146598752216367518687045 27487266040568909753821)
                ·
                  refine ⟨10307724765213341157683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27487266040568909753821 10307724765213341157683)
                  ·
                    rfl

theorem cell21_45167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 3].length) (baseStart_45167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45167 prefixEnd_45167 := by exact prefixLift 45167
  have htrace : WordTrace (prefixWord ++ tailWord_45167) baseStart_45167 baseEnd_45167 := by
    simpa [prefixWord, tailWord_45167, baseEnd_45167] using wordTrace_append hprefix tailTrace_45167
  have hstable : (prefixWord ++ tailWord_45167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45167).length < 2 ^ (prefixWord ++ tailWord_45167).sum := by decide
  have hdescent : baseEnd_45167 < baseStart_45167 := by decide
  rcases family_descends (prefixWord ++ tailWord_45167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45181 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 4]
def baseStart_45181 : Nat := 118140960795 + 45181 * 2 ^ 59
def prefixEnd_45181 : Nat := 4983230072969 + 3 ^ 40 * 45181 * 2
def baseEnd_45181 : Nat := 10310919755952427924321

theorem tailTrace_45181 : CollatzResearch.WordTrace tailWord_45181 prefixEnd_45181 10310919755952427924321 := by
  unfold tailWord_45181
  simp only [CollatzResearch.WordTrace]
  refine ⟨1647886449324428145583397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1098590966216285430388931 1647886449324428145583397)
  ·
    refine ⟨308978709248330277296887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1647886449324428145583397 308978709248330277296887)
    ·
      refine ⟨463468063872495415945331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308978709248330277296887 463468063872495415945331)
      ·
        refine ⟨695202095808743123917997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463468063872495415945331 695202095808743123917997)
        ·
          refine ⟨260700785928278671469249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 695202095808743123917997 260700785928278671469249)
          ·
            refine ⟨195525589446209003601937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260700785928278671469249 195525589446209003601937)
            ·
              refine ⟨146644192084656752701453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195525589446209003601937 146644192084656752701453)
              ·
                refine ⟨54991572031746282263045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146644192084656752701453 54991572031746282263045)
                ·
                  refine ⟨10310919755952427924321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54991572031746282263045 10310919755952427924321)
                  ·
                    rfl

theorem cell21_45181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_45181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45181 prefixEnd_45181 := by exact prefixLift 45181
  have htrace : WordTrace (prefixWord ++ tailWord_45181) baseStart_45181 baseEnd_45181 := by
    simpa [prefixWord, tailWord_45181, baseEnd_45181] using wordTrace_append hprefix tailTrace_45181
  have hstable : (prefixWord ++ tailWord_45181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45181).length < 2 ^ (prefixWord ++ tailWord_45181).sum := by decide
  have hdescent : baseEnd_45181 < baseStart_45181 := by decide
  rcases family_descends (prefixWord ++ tailWord_45181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45246 : List Nat := [4, 2, 1, 1, 5, 1, 2, 5]
def baseStart_45246 : Nat := 118140960795 + 45246 * 2 ^ 59
def prefixEnd_45246 : Nat := 4983230072969 + 3 ^ 40 * 45246 * 2
def baseEnd_45246 : Nat := 3441917880508919780285

theorem tailTrace_45246 : CollatzResearch.WordTrace tailWord_45246 prefixEnd_45246 3441917880508919780285 := by
  unfold tailWord_45246
  simp only [CollatzResearch.WordTrace]
  refine ⟨206282149261118030837449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1100171462725962831133061 206282149261118030837449)
  ·
    refine ⟨154711611945838523128087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206282149261118030837449 154711611945838523128087)
    ·
      refine ⟨232067417918757784692131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154711611945838523128087 232067417918757784692131)
      ·
        refine ⟨348101126878136677038197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232067417918757784692131 348101126878136677038197)
        ·
          refine ⟨32634480644825313472331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 348101126878136677038197 32634480644825313472331)
          ·
            refine ⟨48951720967237970208497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32634480644825313472331 48951720967237970208497)
            ·
              refine ⟨36713790725428477656373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48951720967237970208497 36713790725428477656373)
              ·
                refine ⟨3441917880508919780285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36713790725428477656373 3441917880508919780285)
                ·
                  rfl

theorem cell21_45246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_45246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45246 prefixEnd_45246 := by exact prefixLift 45246
  have htrace : WordTrace (prefixWord ++ tailWord_45246) baseStart_45246 baseEnd_45246 := by
    simpa [prefixWord, tailWord_45246, baseEnd_45246] using wordTrace_append hprefix tailTrace_45246
  have hstable : (prefixWord ++ tailWord_45246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45246).length < 2 ^ (prefixWord ++ tailWord_45246).sum := by decide
  have hdescent : baseEnd_45246 < baseStart_45246 := by decide
  rcases family_descends (prefixWord ++ tailWord_45246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45277 : List Nat := [1, 4, 3, 2, 1, 2, 3, 2, 3]
def baseStart_45277 : Nat := 118140960795 + 45277 * 2 ^ 59
def prefixEnd_45277 : Nat := 4983230072969 + 3 ^ 40 * 45277 * 2
def baseEnd_45277 : Nat := 10332828263877594324125

theorem tailTrace_45277 : CollatzResearch.WordTrace tailWord_45277 prefixEnd_45277 10332828263877594324125 := by
  unfold tailWord_45277
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651387856976636541078085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1100925237984424360718723 1651387856976636541078085)
  ·
    refine ⟨309635223183119351452141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1651387856976636541078085 309635223183119351452141)
    ·
      refine ⟨116113208693669756794553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309635223183119351452141 116113208693669756794553)
      ·
        refine ⟨87084906520252317595915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116113208693669756794553 87084906520252317595915)
        ·
          refine ⟨130627359780378476393873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87084906520252317595915 130627359780378476393873)
          ·
            refine ⟨97970519835283857295405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130627359780378476393873 97970519835283857295405)
            ·
              refine ⟨36738944938231446485777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97970519835283857295405 36738944938231446485777)
              ·
                refine ⟨27554208703673584864333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36738944938231446485777 27554208703673584864333)
                ·
                  refine ⟨10332828263877594324125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27554208703673584864333 10332828263877594324125)
                  ·
                    rfl

theorem cell21_45277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_45277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45277 prefixEnd_45277 := by exact prefixLift 45277
  have htrace : WordTrace (prefixWord ++ tailWord_45277) baseStart_45277 baseEnd_45277 := by
    simpa [prefixWord, tailWord_45277, baseEnd_45277] using wordTrace_append hprefix tailTrace_45277
  have hstable : (prefixWord ++ tailWord_45277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45277).length < 2 ^ (prefixWord ++ tailWord_45277).sum := by decide
  have hdescent : baseEnd_45277 < baseStart_45277 := by decide
  rcases family_descends (prefixWord ++ tailWord_45277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45302 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_45302 : Nat := 118140960795 + 45302 * 2 ^ 59
def prefixEnd_45302 : Nat := 4983230072969 + 3 ^ 40 * 45302 * 2
def baseEnd_45302 : Nat := 10338533604483106407407

theorem tailTrace_45302 : CollatzResearch.WordTrace tailWord_45302 prefixEnd_45302 10338533604483106407407 := by
  unfold tailWord_45302
  simp only [CollatzResearch.WordTrace]
  refine ⟨103268730117879113171135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1101533121257377207158773 103268730117879113171135)
  ·
    refine ⟨154903095176818669756703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103268730117879113171135 154903095176818669756703)
    ·
      refine ⟨232354642765228004635055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154903095176818669756703 232354642765228004635055)
      ·
        refine ⟨348531964147842006952583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232354642765228004635055 348531964147842006952583)
        ·
          refine ⟨522797946221763010428875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348531964147842006952583 522797946221763010428875)
          ·
            refine ⟨784196919332644515643313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522797946221763010428875 784196919332644515643313)
            ·
              refine ⟨588147689499483386732485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784196919332644515643313 588147689499483386732485)
              ·
                refine ⟨110277691781153135012341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 588147689499483386732485 110277691781153135012341)
                ·
                  refine ⟨10338533604483106407407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110277691781153135012341 10338533604483106407407)
                  ·
                    rfl

theorem cell21_45302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_45302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45302 prefixEnd_45302 := by exact prefixLift 45302
  have htrace : WordTrace (prefixWord ++ tailWord_45302) baseStart_45302 baseEnd_45302 := by
    simpa [prefixWord, tailWord_45302, baseEnd_45302] using wordTrace_append hprefix tailTrace_45302
  have hstable : (prefixWord ++ tailWord_45302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45302).length < 2 ^ (prefixWord ++ tailWord_45302).sum := by decide
  have hdescent : baseEnd_45302 < baseStart_45302 := by decide
  rcases family_descends (prefixWord ++ tailWord_45302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45392 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 6]
def baseStart_45392 : Nat := 118140960795 + 45392 * 2 ^ 59
def prefixEnd_45392 : Nat := 4983230072969 + 3 ^ 40 * 45392 * 2
def baseEnd_45392 : Nat := 10359072830662949907223

theorem tailTrace_45392 : CollatzResearch.WordTrace tailWord_45392 prefixEnd_45392 10359072830662949907223 := by
  unfold tailWord_45392
  simp only [CollatzResearch.WordTrace]
  refine ⟨827791125780005590757215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1103721501040007454342953 827791125780005590757215)
  ·
    refine ⟨1241686688670008386135823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 827791125780005590757215 1241686688670008386135823)
    ·
      refine ⟨1862530033005012579203735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1241686688670008386135823 1862530033005012579203735)
      ·
        refine ⟨2793795049507518868805603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1862530033005012579203735 2793795049507518868805603)
        ·
          refine ⟨4190692574261278303208405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2793795049507518868805603 4190692574261278303208405)
          ·
            refine ⟨98219357209248710231447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4190692574261278303208405 98219357209248710231447)
            ·
              refine ⟨147329035813873065347171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98219357209248710231447 147329035813873065347171)
              ·
                refine ⟨220993553720809598020757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147329035813873065347171 220993553720809598020757)
                ·
                  refine ⟨10359072830662949907223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 220993553720809598020757 10359072830662949907223)
                  ·
                    rfl

theorem cell21_45392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_45392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45392 prefixEnd_45392 := by exact prefixLift 45392
  have htrace : WordTrace (prefixWord ++ tailWord_45392) baseStart_45392 baseEnd_45392 := by
    simpa [prefixWord, tailWord_45392, baseEnd_45392] using wordTrace_append hprefix tailTrace_45392
  have hstable : (prefixWord ++ tailWord_45392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45392).length < 2 ^ (prefixWord ++ tailWord_45392).sum := by decide
  have hdescent : baseEnd_45392 < baseStart_45392 := by decide
  rcases family_descends (prefixWord ++ tailWord_45392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45460 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 4]
def baseStart_45460 : Nat := 118140960795 + 45460 * 2 ^ 59
def prefixEnd_45460 : Nat := 4983230072969 + 3 ^ 40 * 45460 * 2
def baseEnd_45460 : Nat := 10374591357109942773751

theorem tailTrace_45460 : CollatzResearch.WordTrace tailWord_45460 prefixEnd_45460 10374591357109942773751 := by
  unfold tailWord_45460
  simp only [CollatzResearch.WordTrace]
  refine ⟨829031207656829397494917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1105374943542439196659889 829031207656829397494917)
  ·
    refine ⟨155443351435655512030297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 829031207656829397494917 155443351435655512030297)
    ·
      refine ⟨116582513576741634022723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155443351435655512030297 116582513576741634022723)
      ·
        refine ⟨174873770365112451034085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116582513576741634022723 174873770365112451034085)
        ·
          refine ⟨32788831943458584568891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174873770365112451034085 32788831943458584568891)
          ·
            refine ⟨49183247915187876853337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32788831943458584568891 49183247915187876853337)
            ·
              refine ⟨36887435936390907640003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49183247915187876853337 36887435936390907640003)
              ·
                refine ⟨55331153904586361460005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36887435936390907640003 55331153904586361460005)
                ·
                  refine ⟨10374591357109942773751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55331153904586361460005 10374591357109942773751)
                  ·
                    rfl

theorem cell21_45460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_45460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45460 prefixEnd_45460 := by exact prefixLift 45460
  have htrace : WordTrace (prefixWord ++ tailWord_45460) baseStart_45460 baseEnd_45460 := by
    simpa [prefixWord, tailWord_45460, baseEnd_45460] using wordTrace_append hprefix tailTrace_45460
  have hstable : (prefixWord ++ tailWord_45460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45460).length < 2 ^ (prefixWord ++ tailWord_45460).sum := by decide
  have hdescent : baseEnd_45460 < baseStart_45460 := by decide
  rcases family_descends (prefixWord ++ tailWord_45460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45516 : List Nat := [2, 2, 1, 4, 3, 2, 1, 6]
def baseStart_45516 : Nat := 118140960795 + 45516 * 2 ^ 59
def prefixEnd_45516 : Nat := 4983230072969 + 3 ^ 40 * 45516 * 2
def baseEnd_45516 : Nat := 3462457106688763280101

theorem tailTrace_45516 : CollatzResearch.WordTrace tailWord_45516 prefixEnd_45516 3462457106688763280101 := by
  unfold tailWord_45516
  simp only [CollatzResearch.WordTrace]
  refine ⟨830052451555390179514201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1106736602073853572685601 830052451555390179514201)
  ·
    refine ⟨622539338666542634635651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 830052451555390179514201 622539338666542634635651)
    ·
      refine ⟨933809007999813951953477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622539338666542634635651 933809007999813951953477)
      ·
        refine ⟨175089188999965115991277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 933809007999813951953477 175089188999965115991277)
        ·
          refine ⟨65658445874986918496729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175089188999965115991277 65658445874986918496729)
          ·
            refine ⟨49243834406240188872547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65658445874986918496729 49243834406240188872547)
            ·
              refine ⟨73865751609360283308821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49243834406240188872547 73865751609360283308821)
              ·
                refine ⟨3462457106688763280101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73865751609360283308821 3462457106688763280101)
                ·
                  rfl

theorem cell21_45516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_45516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45516 prefixEnd_45516 := by exact prefixLift 45516
  have htrace : WordTrace (prefixWord ++ tailWord_45516) baseStart_45516 baseEnd_45516 := by
    simpa [prefixWord, tailWord_45516, baseEnd_45516] using wordTrace_append hprefix tailTrace_45516
  have hstable : (prefixWord ++ tailWord_45516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45516).length < 2 ^ (prefixWord ++ tailWord_45516).sum := by decide
  have hdescent : baseEnd_45516 < baseStart_45516 := by decide
  rcases family_descends (prefixWord ++ tailWord_45516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45527 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 10]
def baseStart_45527 : Nat := 118140960795 + 45527 * 2 ^ 59
def prefixEnd_45527 : Nat := 4983230072969 + 3 ^ 40 * 45527 * 2
def baseEnd_45527 : Nat := 10389881669932715156947

theorem tailTrace_45527 : CollatzResearch.WordTrace tailWord_45527 prefixEnd_45527 10389881669932715156947 := by
  unfold tailWord_45527
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660506106070929237678835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1107004070713952825119223 1660506106070929237678835)
  ·
    refine ⟨2490759159106393856518253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1660506106070929237678835 2490759159106393856518253)
    ·
      refine ⟨934034684664897696194345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2490759159106393856518253 934034684664897696194345)
      ·
        refine ⟨700526013498673272145759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 934034684664897696194345 700526013498673272145759)
        ·
          refine ⟨1050789020248009908218639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700526013498673272145759 1050789020248009908218639)
          ·
            refine ⟨1576183530372014862327959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050789020248009908218639 1576183530372014862327959)
            ·
              refine ⟨2364275295558022293491939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1576183530372014862327959 2364275295558022293491939)
              ·
                refine ⟨3546412943337033440237909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364275295558022293491939 3546412943337033440237909)
                ·
                  refine ⟨10389881669932715156947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 3546412943337033440237909 10389881669932715156947)
                  ·
                    rfl

theorem cell21_45527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_45527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45527 prefixEnd_45527 := by exact prefixLift 45527
  have htrace : WordTrace (prefixWord ++ tailWord_45527) baseStart_45527 baseEnd_45527 := by
    simpa [prefixWord, tailWord_45527, baseEnd_45527] using wordTrace_append hprefix tailTrace_45527
  have hstable : (prefixWord ++ tailWord_45527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45527).length < 2 ^ (prefixWord ++ tailWord_45527).sum := by decide
  have hdescent : baseEnd_45527 < baseStart_45527 := by decide
  rcases family_descends (prefixWord ++ tailWord_45527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45589 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 5]
def baseStart_45589 : Nat := 118140960795 + 45589 * 2 ^ 59
def prefixEnd_45589 : Nat := 4983230072969 + 3 ^ 40 * 45589 * 2
def baseEnd_45589 : Nat := 10404030914634385123487

theorem tailTrace_45589 : CollatzResearch.WordTrace tailWord_45589 prefixEnd_45589 10404030914634385123487 := by
  unfold tailWord_45589
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662767431846313826435821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1108511621230875884290547 1662767431846313826435821)
  ·
    refine ⟨623537786942367684913433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1662767431846313826435821 623537786942367684913433)
    ·
      refine ⟨467653340206775763685075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 623537786942367684913433 467653340206775763685075)
      ·
        refine ⟨701480010310163645527613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467653340206775763685075 701480010310163645527613)
        ·
          refine ⟨263055003866311367072855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 701480010310163645527613 263055003866311367072855)
          ·
            refine ⟨394582505799467050609283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263055003866311367072855 394582505799467050609283)
            ·
              refine ⟨591873758699200575913925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394582505799467050609283 591873758699200575913925)
              ·
                refine ⟨110976329756100107983861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591873758699200575913925 110976329756100107983861)
                ·
                  refine ⟨10404030914634385123487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110976329756100107983861 10404030914634385123487)
                  ·
                    rfl

theorem cell21_45589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_45589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45589 prefixEnd_45589 := by exact prefixLift 45589
  have htrace : WordTrace (prefixWord ++ tailWord_45589) baseStart_45589 baseEnd_45589 := by
    simpa [prefixWord, tailWord_45589, baseEnd_45589] using wordTrace_append hprefix tailTrace_45589
  have hstable : (prefixWord ++ tailWord_45589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45589).length < 2 ^ (prefixWord ++ tailWord_45589).sum := by decide
  have hdescent : baseEnd_45589 < baseStart_45589 := by decide
  rcases family_descends (prefixWord ++ tailWord_45589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45592 : List Nat := [2, 1, 2, 3, 3, 3, 2, 5]
def baseStart_45592 : Nat := 118140960795 + 45592 * 2 ^ 59
def prefixEnd_45592 : Nat := 4983230072969 + 3 ^ 40 * 45592 * 2
def baseEnd_45592 : Nat := 3468238518502348857827

theorem tailTrace_45592 : CollatzResearch.WordTrace tailWord_45592 prefixEnd_45592 3468238518502348857827 := by
  unfold tailWord_45592
  simp only [CollatzResearch.WordTrace]
  refine ⟨831438425417722669397515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1108584567223630225863353 831438425417722669397515)
  ·
    refine ⟨1247157638126584004096273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 831438425417722669397515 1247157638126584004096273)
    ·
      refine ⟨935368228594938003072205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1247157638126584004096273 935368228594938003072205)
      ·
        refine ⟨350763085723101751152077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 935368228594938003072205 350763085723101751152077)
        ·
          refine ⟨131536157146163156682029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350763085723101751152077 131536157146163156682029)
          ·
            refine ⟨49326058929811183755761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131536157146163156682029 49326058929811183755761)
            ·
              refine ⟨36994544197358387816821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49326058929811183755761 36994544197358387816821)
              ·
                refine ⟨3468238518502348857827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36994544197358387816821 3468238518502348857827)
                ·
                  rfl

theorem cell21_45592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_45592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45592 prefixEnd_45592 := by exact prefixLift 45592
  have htrace : WordTrace (prefixWord ++ tailWord_45592) baseStart_45592 baseEnd_45592 := by
    simpa [prefixWord, tailWord_45592, baseEnd_45592] using wordTrace_append hprefix tailTrace_45592
  have hstable : (prefixWord ++ tailWord_45592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45592).length < 2 ^ (prefixWord ++ tailWord_45592).sum := by decide
  have hdescent : baseEnd_45592 < baseStart_45592 := by decide
  rcases family_descends (prefixWord ++ tailWord_45592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45623 : List Nat := [1, 1, 3, 1, 2, 3, 5, 2, 3]
def baseStart_45623 : Nat := 118140960795 + 45623 * 2 ^ 59
def prefixEnd_45623 : Nat := 4983230072969 + 3 ^ 40 * 45623 * 2
def baseEnd_45623 : Nat := 10411790177857881556751

theorem tailTrace_45623 : CollatzResearch.WordTrace tailWord_45623 prefixEnd_45623 10411790177857881556751 := by
  unfold tailWord_45623
  simp only [CollatzResearch.WordTrace]
  refine ⟨1664007513723137633173523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1109338342482091755449015 1664007513723137633173523)
  ·
    refine ⟨2496011270584706449760285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1664007513723137633173523 2496011270584706449760285)
    ·
      refine ⟨936004226469264918660107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2496011270584706449760285 936004226469264918660107)
      ·
        refine ⟨1404006339703897377990161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936004226469264918660107 1404006339703897377990161)
        ·
          refine ⟨1053004754777923033492621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1404006339703897377990161 1053004754777923033492621)
          ·
            refine ⟨394876783041721137559733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1053004754777923033492621 394876783041721137559733)
            ·
              refine ⟨37019698410161356646225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 394876783041721137559733 37019698410161356646225)
              ·
                refine ⟨27764773807621017484669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37019698410161356646225 27764773807621017484669)
                ·
                  refine ⟨10411790177857881556751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27764773807621017484669 10411790177857881556751)
                  ·
                    rfl

theorem cell21_45623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 3].length) (baseStart_45623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45623 prefixEnd_45623 := by exact prefixLift 45623
  have htrace : WordTrace (prefixWord ++ tailWord_45623) baseStart_45623 baseEnd_45623 := by
    simpa [prefixWord, tailWord_45623, baseEnd_45623] using wordTrace_append hprefix tailTrace_45623
  have hstable : (prefixWord ++ tailWord_45623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45623).length < 2 ^ (prefixWord ++ tailWord_45623).sum := by decide
  have hdescent : baseEnd_45623 < baseStart_45623 := by decide
  rcases family_descends (prefixWord ++ tailWord_45623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45637 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 4]
def baseStart_45637 : Nat := 118140960795 + 45637 * 2 ^ 59
def prefixEnd_45637 : Nat := 4983230072969 + 3 ^ 40 * 45637 * 2
def baseEnd_45637 : Nat := 10414985168596968323389

theorem tailTrace_45637 : CollatzResearch.WordTrace tailWord_45637 prefixEnd_45637 10414985168596968323389 := by
  unfold tailWord_45637
  simp only [CollatzResearch.WordTrace]
  refine ⟨1664518135672418024183165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1109678757114945349455443 1664518135672418024183165)
  ·
    refine ⟨624194300877156759068687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1664518135672418024183165 624194300877156759068687)
    ·
      refine ⟨936291451315735138603031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 624194300877156759068687 936291451315735138603031)
      ·
        refine ⟨1404437176973602707904547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936291451315735138603031 1404437176973602707904547)
        ·
          refine ⟨2106655765460404061856821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404437176973602707904547 2106655765460404061856821)
          ·
            refine ⟨197498978011912880799077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2106655765460404061856821 197498978011912880799077)
            ·
              refine ⟨37031058377233665149827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197498978011912880799077 37031058377233665149827)
              ·
                refine ⟨55546587565850497724741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37031058377233665149827 55546587565850497724741)
                ·
                  refine ⟨10414985168596968323389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55546587565850497724741 10414985168596968323389)
                  ·
                    rfl

theorem cell21_45637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_45637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45637 prefixEnd_45637 := by exact prefixLift 45637
  have htrace : WordTrace (prefixWord ++ tailWord_45637) baseStart_45637 baseEnd_45637 := by
    simpa [prefixWord, tailWord_45637, baseEnd_45637] using wordTrace_append hprefix tailTrace_45637
  have hstable : (prefixWord ++ tailWord_45637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45637).length < 2 ^ (prefixWord ++ tailWord_45637).sum := by decide
  have hdescent : baseEnd_45637 < baseStart_45637 := by decide
  rcases family_descends (prefixWord ++ tailWord_45637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45679 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 6]
def baseStart_45679 : Nat := 118140960795 + 45679 * 2 ^ 59
def prefixEnd_45679 : Nat := 4983230072969 + 3 ^ 40 * 45679 * 2
def baseEnd_45679 : Nat := 10424570140814228623303

theorem tailTrace_45679 : CollatzResearch.WordTrace tailWord_45679 prefixEnd_45679 10424570140814228623303 := by
  unfold tailWord_45679
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666050001520259197212091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1110700001013506131474727 1666050001520259197212091)
  ·
    refine ⟨2499075002280388795818137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1666050001520259197212091 2499075002280388795818137)
    ·
      refine ⟨1874306251710291596863603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2499075002280388795818137 1874306251710291596863603)
      ·
        refine ⟨2811459377565437395295405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874306251710291596863603 2811459377565437395295405)
        ·
          refine ⟨1054297266587039023235777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2811459377565437395295405 1054297266587039023235777)
          ·
            refine ⟨790722949940279267426833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1054297266587039023235777 790722949940279267426833)
            ·
              refine ⟨593042212455209450570125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790722949940279267426833 593042212455209450570125)
              ·
                refine ⟨222390829670703543963797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 593042212455209450570125 222390829670703543963797)
                ·
                  refine ⟨10424570140814228623303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 222390829670703543963797 10424570140814228623303)
                  ·
                    rfl

theorem cell21_45679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_45679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45679 prefixEnd_45679 := by exact prefixLift 45679
  have htrace : WordTrace (prefixWord ++ tailWord_45679) baseStart_45679 baseEnd_45679 := by
    simpa [prefixWord, tailWord_45679, baseEnd_45679] using wordTrace_append hprefix tailTrace_45679
  have hstable : (prefixWord ++ tailWord_45679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45679).length < 2 ^ (prefixWord ++ tailWord_45679).sum := by decide
  have hdescent : baseEnd_45679 < baseStart_45679 := by decide
  rcases family_descends (prefixWord ++ tailWord_45679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45685 : List Nat := [1, 3, 4, 2, 3, 1, 1, 6]
def baseStart_45685 : Nat := 118140960795 + 45685 * 2 ^ 59
def prefixEnd_45685 : Nat := 4983230072969 + 3 ^ 40 * 45685 * 2
def baseEnd_45685 : Nat := 3475313140853183841097

theorem tailTrace_45685 : CollatzResearch.WordTrace tailWord_45685 prefixEnd_45685 3475313140853183841097 := by
  unfold tailWord_45685
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666268839498522221930509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1110845892999014814620339 1666268839498522221930509)
  ·
    refine ⟨624850814811945833223941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1666268839498522221930509 624850814811945833223941)
    ·
      refine ⟨117159527777239843729489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 624850814811945833223941 117159527777239843729489)
      ·
        refine ⟨87869645832929882797117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117159527777239843729489 87869645832929882797117)
        ·
          refine ⟨32951117187348706048919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87869645832929882797117 32951117187348706048919)
          ·
            refine ⟨49426675781023059073379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32951117187348706048919 49426675781023059073379)
            ·
              refine ⟨74140013671534588610069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49426675781023059073379 74140013671534588610069)
              ·
                refine ⟨3475313140853183841097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74140013671534588610069 3475313140853183841097)
                ·
                  rfl

theorem cell21_45685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 6].length) (baseStart_45685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45685 prefixEnd_45685 := by exact prefixLift 45685
  have htrace : WordTrace (prefixWord ++ tailWord_45685) baseStart_45685 baseEnd_45685 := by
    simpa [prefixWord, tailWord_45685, baseEnd_45685] using wordTrace_append hprefix tailTrace_45685
  have hstable : (prefixWord ++ tailWord_45685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45685).length < 2 ^ (prefixWord ++ tailWord_45685).sum := by decide
  have hdescent : baseEnd_45685 < baseStart_45685 := by decide
  rcases family_descends (prefixWord ++ tailWord_45685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45696 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 4]
def baseStart_45696 : Nat := 118140960795 + 45696 * 2 ^ 59
def prefixEnd_45696 : Nat := 4983230072969 + 3 ^ 40 * 45696 * 2
def baseEnd_45696 : Nat := 10428449772425976839935

theorem tailTrace_45696 : CollatzResearch.WordTrace tailWord_45696 prefixEnd_45696 10428449772425976839935 := by
  unfold tailWord_45696
  simp only [CollatzResearch.WordTrace]
  refine ⟨833335021229335550290471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1111113361639114067053961 833335021229335550290471)
  ·
    refine ⟨1250002531844003325435707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833335021229335550290471 1250002531844003325435707)
    ·
      refine ⟨1875003797766004988153561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250002531844003325435707 1875003797766004988153561)
      ·
        refine ⟨1406252848324503741115171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1875003797766004988153561 1406252848324503741115171)
        ·
          refine ⟨2109379272486755611672757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406252848324503741115171 2109379272486755611672757)
          ·
            refine ⟨197754306795633338594321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2109379272486755611672757 197754306795633338594321)
            ·
              refine ⟨148315730096725003945741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197754306795633338594321 148315730096725003945741)
              ·
                refine ⟨55618398786271876479653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148315730096725003945741 55618398786271876479653)
                ·
                  refine ⟨10428449772425976839935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55618398786271876479653 10428449772425976839935)
                  ·
                    rfl

theorem cell21_45696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_45696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45696 prefixEnd_45696 := by exact prefixLift 45696
  have htrace : WordTrace (prefixWord ++ tailWord_45696) baseStart_45696 baseEnd_45696 := by
    simpa [prefixWord, tailWord_45696, baseEnd_45696] using wordTrace_append hprefix tailTrace_45696
  have hstable : (prefixWord ++ tailWord_45696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45696).length < 2 ^ (prefixWord ++ tailWord_45696).sum := by decide
  have hdescent : baseEnd_45696 < baseStart_45696 := by decide
  rcases family_descends (prefixWord ++ tailWord_45696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45716 : List Nat := [2, 4, 2, 2, 1, 2, 2, 3, 3]
def baseStart_45716 : Nat := 118140960795 + 45716 * 2 ^ 59
def prefixEnd_45716 : Nat := 4983230072969 + 3 ^ 40 * 45716 * 2
def baseEnd_45716 : Nat := 10433014044910386506561

theorem tailTrace_45716 : CollatzResearch.WordTrace tailWord_45716 prefixEnd_45716 10433014044910386506561 := by
  unfold tailWord_45716
  simp only [CollatzResearch.WordTrace]
  refine ⟨833699751193107258154501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1111599668257476344206001 833699751193107258154501)
  ·
    refine ⟨156318703348707610903969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 833699751193107258154501 156318703348707610903969)
    ·
      refine ⟨117239027511530708177977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156318703348707610903969 117239027511530708177977)
      ·
        refine ⟨87929270633648031133483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117239027511530708177977 87929270633648031133483)
        ·
          refine ⟨131893905950472046700225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87929270633648031133483 131893905950472046700225)
          ·
            refine ⟨98920429462854035025169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131893905950472046700225 98920429462854035025169)
            ·
              refine ⟨74190322097140526268877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98920429462854035025169 74190322097140526268877)
              ·
                refine ⟨27821370786427697350829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74190322097140526268877 27821370786427697350829)
                ·
                  refine ⟨10433014044910386506561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27821370786427697350829 10433014044910386506561)
                  ·
                    rfl

theorem cell21_45716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_45716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45716 prefixEnd_45716 := by exact prefixLift 45716
  have htrace : WordTrace (prefixWord ++ tailWord_45716) baseStart_45716 baseEnd_45716 := by
    simpa [prefixWord, tailWord_45716, baseEnd_45716] using wordTrace_append hprefix tailTrace_45716
  have hstable : (prefixWord ++ tailWord_45716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45716).length < 2 ^ (prefixWord ++ tailWord_45716).sum := by decide
  have hdescent : baseEnd_45716 < baseStart_45716 := by decide
  rcases family_descends (prefixWord ++ tailWord_45716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45772 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 6]
def baseStart_45772 : Nat := 118140960795 + 45772 * 2 ^ 59
def prefixEnd_45772 : Nat := 4983230072969 + 3 ^ 40 * 45772 * 2
def baseEnd_45772 : Nat := 10445794007866733573113

theorem tailTrace_45772 : CollatzResearch.WordTrace tailWord_45772 prefixEnd_45772 10445794007866733573113 := by
  unfold tailWord_45772
  simp only [CollatzResearch.WordTrace]
  refine ⟨834720995091668040173785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1112961326788890720231713 834720995091668040173785)
  ·
    refine ⟨626040746318751030130339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 834720995091668040173785 626040746318751030130339)
    ·
      refine ⟨939061119478126545195509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626040746318751030130339 939061119478126545195509)
      ·
        refine ⟨88036979951074363612079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 939061119478126545195509 88036979951074363612079)
        ·
          refine ⟨132055469926611545418119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88036979951074363612079 132055469926611545418119)
          ·
            refine ⟨198083204889917318127179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132055469926611545418119 198083204889917318127179)
            ·
              refine ⟨297124807334875977190769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198083204889917318127179 297124807334875977190769)
              ·
                refine ⟨222843605501156982893077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297124807334875977190769 222843605501156982893077)
                ·
                  refine ⟨10445794007866733573113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 222843605501156982893077 10445794007866733573113)
                  ·
                    rfl

theorem cell21_45772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_45772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45772 prefixEnd_45772 := by exact prefixLift 45772
  have htrace : WordTrace (prefixWord ++ tailWord_45772) baseStart_45772 baseEnd_45772 := by
    simpa [prefixWord, tailWord_45772, baseEnd_45772] using wordTrace_append hprefix tailTrace_45772
  have hstable : (prefixWord ++ tailWord_45772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45772).length < 2 ^ (prefixWord ++ tailWord_45772).sum := by decide
  have hdescent : baseEnd_45772 < baseStart_45772 := by decide
  rcases family_descends (prefixWord ++ tailWord_45772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45806 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_45806 : Nat := 118140960795 + 45806 * 2 ^ 59
def prefixEnd_45806 : Nat := 4983230072969 + 3 ^ 40 * 45806 * 2
def baseEnd_45806 : Nat := 10453553271090230006377

theorem tailTrace_45806 : CollatzResearch.WordTrace tailWord_45806 prefixEnd_45806 10453553271090230006377 := by
  unfold tailWord_45806
  simp only [CollatzResearch.WordTrace]
  refine ⟨208835259007519985885659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1113788048040106591390181 208835259007519985885659)
  ·
    refine ⟨313252888511279978828489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208835259007519985885659 313252888511279978828489)
    ·
      refine ⟨234939666383459984121367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313252888511279978828489 234939666383459984121367)
      ·
        refine ⟨352409499575189976182051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234939666383459984121367 352409499575189976182051)
        ·
          refine ⟨528614249362784964273077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352409499575189976182051 528614249362784964273077)
          ·
            refine ⟨49557585877761090400601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 528614249362784964273077 49557585877761090400601)
            ·
              refine ⟨37168189408320817800451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49557585877761090400601 37168189408320817800451)
              ·
                refine ⟨55752284112481226700677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37168189408320817800451 55752284112481226700677)
                ·
                  refine ⟨10453553271090230006377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55752284112481226700677 10453553271090230006377)
                  ·
                    rfl

theorem cell21_45806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_45806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45806 prefixEnd_45806 := by exact prefixLift 45806
  have htrace : WordTrace (prefixWord ++ tailWord_45806) baseStart_45806 baseEnd_45806 := by
    simpa [prefixWord, tailWord_45806, baseEnd_45806] using wordTrace_append hprefix tailTrace_45806
  have hstable : (prefixWord ++ tailWord_45806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45806).length < 2 ^ (prefixWord ++ tailWord_45806).sum := by decide
  have hdescent : baseEnd_45806 < baseStart_45806 := by decide
  rcases family_descends (prefixWord ++ tailWord_45806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45834 : List Nat := [3, 1, 2, 2, 1, 2, 2, 5, 3]
def baseStart_45834 : Nat := 118140960795 + 45834 * 2 ^ 59
def prefixEnd_45834 : Nat := 4983230072969 + 3 ^ 40 * 45834 * 2
def baseEnd_45834 : Nat := 10459943252568403539653

theorem tailTrace_45834 : CollatzResearch.WordTrace tailWord_45834 prefixEnd_45834 10459943252568403539653 := by
  unfold tailWord_45834
  simp only [CollatzResearch.WordTrace]
  refine ⟨417925828989680167276139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1114468877305813779403037 417925828989680167276139)
  ·
    refine ⟨626888743484520250914209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 417925828989680167276139 626888743484520250914209)
    ·
      refine ⟨470166557613390188185657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 626888743484520250914209 470166557613390188185657)
      ·
        refine ⟨352624918210042641139243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470166557613390188185657 352624918210042641139243)
        ·
          refine ⟨528937377315063961708865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352624918210042641139243 528937377315063961708865)
          ·
            refine ⟨396703032986297971281649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528937377315063961708865 396703032986297971281649)
            ·
              refine ⟨297527274739723478461237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396703032986297971281649 297527274739723478461237)
              ·
                refine ⟨27893182006849076105741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 297527274739723478461237 27893182006849076105741)
                ·
                  refine ⟨10459943252568403539653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27893182006849076105741 10459943252568403539653)
                  ·
                    rfl

theorem cell21_45834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_45834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_45834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_45834 prefixEnd_45834 := by exact prefixLift 45834
  have htrace : WordTrace (prefixWord ++ tailWord_45834) baseStart_45834 baseEnd_45834 := by
    simpa [prefixWord, tailWord_45834, baseEnd_45834] using wordTrace_append hprefix tailTrace_45834
  have hstable : (prefixWord ++ tailWord_45834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45834).length < 2 ^ (prefixWord ++ tailWord_45834).sum := by decide
  have hdescent : baseEnd_45834 < baseStart_45834 := by decide
  rcases family_descends (prefixWord ++ tailWord_45834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46020 : List Nat := [2, 3, 3, 3, 1, 1, 1, 4, 3]
def baseStart_46020 : Nat := 118140960795 + 46020 * 2 ^ 59
def prefixEnd_46020 : Nat := 4983230072969 + 3 ^ 40 * 46020 * 2
def baseEnd_46020 : Nat := 10502390986673413439273

theorem tailTrace_46020 : CollatzResearch.WordTrace tailWord_46020 prefixEnd_46020 10502390986673413439273 := by
  unfold tailWord_46020
  simp only [CollatzResearch.WordTrace]
  refine ⟨839243646642437217687757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1118991528856582956917009 839243646642437217687757)
  ·
    refine ⟨314716367490913956632909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 839243646642437217687757 314716367490913956632909)
    ·
      refine ⟨118018637809092733737341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314716367490913956632909 118018637809092733737341)
      ·
        refine ⟨44256989178409775151503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118018637809092733737341 44256989178409775151503)
        ·
          refine ⟨66385483767614662727255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44256989178409775151503 66385483767614662727255)
          ·
            refine ⟨99578225651421994090883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66385483767614662727255 99578225651421994090883)
            ·
              refine ⟨149367338477132991136325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99578225651421994090883 149367338477132991136325)
              ·
                refine ⟨28006375964462435838061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149367338477132991136325 28006375964462435838061)
                ·
                  refine ⟨10502390986673413439273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28006375964462435838061 10502390986673413439273)
                  ·
                    rfl

theorem cell21_46020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_46020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46020 prefixEnd_46020 := by exact prefixLift 46020
  have htrace : WordTrace (prefixWord ++ tailWord_46020) baseStart_46020 baseEnd_46020 := by
    simpa [prefixWord, tailWord_46020, baseEnd_46020] using wordTrace_append hprefix tailTrace_46020
  have hstable : (prefixWord ++ tailWord_46020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46020).length < 2 ^ (prefixWord ++ tailWord_46020).sum := by decide
  have hdescent : baseEnd_46020 < baseStart_46020 := by decide
  rcases family_descends (prefixWord ++ tailWord_46020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46045 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 7]
def baseStart_46045 : Nat := 118140960795 + 46045 * 2 ^ 59
def prefixEnd_46045 : Nat := 4983230072969 + 3 ^ 40 * 46045 * 2
def baseEnd_46045 : Nat := 10508096327278925522555

theorem tailTrace_46045 : CollatzResearch.WordTrace tailWord_46045 prefixEnd_46045 10508096327278925522555 := by
  unfold tailWord_46045
  simp only [CollatzResearch.WordTrace]
  refine ⟨1679399118194303705035589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1119599412129535803357059 1679399118194303705035589)
  ·
    refine ⟨314887334661431944694173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1679399118194303705035589 314887334661431944694173)
    ·
      refine ⟨118082750498036979260315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314887334661431944694173 118082750498036979260315)
      ·
        refine ⟨177124125747055468890473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118082750498036979260315 177124125747055468890473)
        ·
          refine ⟨132843094310291601667855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177124125747055468890473 132843094310291601667855)
          ·
            refine ⟨199264641465437402501783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132843094310291601667855 199264641465437402501783)
            ·
              refine ⟨298896962198156103752675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199264641465437402501783 298896962198156103752675)
              ·
                refine ⟨448345443297234155629013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298896962198156103752675 448345443297234155629013)
                ·
                  refine ⟨10508096327278925522555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 448345443297234155629013 10508096327278925522555)
                  ·
                    rfl

theorem cell21_46045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_46045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46045 prefixEnd_46045 := by exact prefixLift 46045
  have htrace : WordTrace (prefixWord ++ tailWord_46045) baseStart_46045 baseEnd_46045 := by
    simpa [prefixWord, tailWord_46045, baseEnd_46045] using wordTrace_append hprefix tailTrace_46045
  have hstable : (prefixWord ++ tailWord_46045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46045).length < 2 ^ (prefixWord ++ tailWord_46045).sum := by decide
  have hdescent : baseEnd_46045 < baseStart_46045 := by decide
  rcases family_descends (prefixWord ++ tailWord_46045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46073 : List Nat := [1, 2, 1, 3, 1, 3, 10]
def baseStart_46073 : Nat := 118140960795 + 46073 * 2 ^ 59
def prefixEnd_46073 : Nat := 4983230072969 + 3 ^ 40 * 46073 * 2
def baseEnd_46073 : Nat := 1168276256528566561759

theorem tailTrace_46073 : CollatzResearch.WordTrace tailWord_46073 prefixEnd_46073 1168276256528566561759 := by
  unfold tailWord_46073
  simp only [CollatzResearch.WordTrace]
  refine ⟨1680420362092864487054873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1120280241395242991369915 1680420362092864487054873)
  ·
    refine ⟨1260315271569648365291155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1680420362092864487054873 1260315271569648365291155)
    ·
      refine ⟨1890472907354472547936733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1260315271569648365291155 1890472907354472547936733)
      ·
        refine ⟨708927340257927205476275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1890472907354472547936733 708927340257927205476275)
        ·
          refine ⟨1063391010386890808214413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708927340257927205476275 1063391010386890808214413)
          ·
            refine ⟨398771628895084053080405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1063391010386890808214413 398771628895084053080405)
            ·
              refine ⟨1168276256528566561759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 398771628895084053080405 1168276256528566561759)
              ·
                rfl

theorem cell21_46073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 10].length) (baseStart_46073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46073 prefixEnd_46073 := by exact prefixLift 46073
  have htrace : WordTrace (prefixWord ++ tailWord_46073) baseStart_46073 baseEnd_46073 := by
    simpa [prefixWord, tailWord_46073, baseEnd_46073] using wordTrace_append hprefix tailTrace_46073
  have hstable : (prefixWord ++ tailWord_46073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46073).length < 2 ^ (prefixWord ++ tailWord_46073).sum := by decide
  have hdescent : baseEnd_46073 < baseStart_46073 := by decide
  rcases family_descends (prefixWord ++ tailWord_46073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46076 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 4]
def baseStart_46076 : Nat := 118140960795 + 46076 * 2 ^ 59
def prefixEnd_46076 : Nat := 4983230072969 + 3 ^ 40 * 46076 * 2
def baseEnd_46076 : Nat := 10515170949629760505825

theorem tailTrace_46076 : CollatzResearch.WordTrace tailWord_46076 prefixEnd_46076 10515170949629760505825 := by
  unfold tailWord_46076
  simp only [CollatzResearch.WordTrace]
  refine ⟨840264890540997999707041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1120353187387997332942721 840264890540997999707041)
  ·
    refine ⟨630198667905748499780281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 840264890540997999707041 630198667905748499780281)
    ·
      refine ⟨472649000929311374835211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 630198667905748499780281 472649000929311374835211)
      ·
        refine ⟨708973501393967062252817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472649000929311374835211 708973501393967062252817)
        ·
          refine ⟨531730126045475296689613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708973501393967062252817 531730126045475296689613)
          ·
            refine ⟨199398797267053236258605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 531730126045475296689613 199398797267053236258605)
            ·
              refine ⟨74774548975144963596977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199398797267053236258605 74774548975144963596977)
              ·
                refine ⟨56080911731358722697733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74774548975144963596977 56080911731358722697733)
                ·
                  refine ⟨10515170949629760505825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56080911731358722697733 10515170949629760505825)
                  ·
                    rfl

theorem cell21_46076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_46076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46076 prefixEnd_46076 := by exact prefixLift 46076
  have htrace : WordTrace (prefixWord ++ tailWord_46076) baseStart_46076 baseEnd_46076 := by
    simpa [prefixWord, tailWord_46076, baseEnd_46076] using wordTrace_append hprefix tailTrace_46076
  have hstable : (prefixWord ++ tailWord_46076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46076).length < 2 ^ (prefixWord ++ tailWord_46076).sum := by decide
  have hdescent : baseEnd_46076 < baseStart_46076 := by decide
  rcases family_descends (prefixWord ++ tailWord_46076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46135 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 4]
def baseStart_46135 : Nat := 118140960795 + 46135 * 2 ^ 59
def prefixEnd_46135 : Nat := 4983230072969 + 3 ^ 40 * 46135 * 2
def baseEnd_46135 : Nat := 10528635553458769022371

theorem tailTrace_46135 : CollatzResearch.WordTrace tailWord_46135 prefixEnd_46135 10528635553458769022371 := by
  unfold tailWord_46135
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682681687868249075811859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1121787791912166050541239 1682681687868249075811859)
  ·
    refine ⟨2524022531802373613717789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1682681687868249075811859 2524022531802373613717789)
    ·
      refine ⟨946508449425890105144171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2524022531802373613717789 946508449425890105144171)
      ·
        refine ⟨1419762674138835157716257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946508449425890105144171 1419762674138835157716257)
        ·
          refine ⟨1064822005604126368287193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1419762674138835157716257 1064822005604126368287193)
          ·
            refine ⟨798616504203094776215395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1064822005604126368287193 798616504203094776215395)
            ·
              refine ⟨1197924756304642164323093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798616504203094776215395 1197924756304642164323093)
              ·
                refine ⟨56152722951780101452645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1197924756304642164323093 56152722951780101452645)
                ·
                  refine ⟨10528635553458769022371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56152722951780101452645 10528635553458769022371)
                  ·
                    rfl

theorem cell21_46135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 4].length) (baseStart_46135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46135 prefixEnd_46135 := by exact prefixLift 46135
  have htrace : WordTrace (prefixWord ++ tailWord_46135) baseStart_46135 baseEnd_46135 := by
    simpa [prefixWord, tailWord_46135, baseEnd_46135] using wordTrace_append hprefix tailTrace_46135
  have hstable : (prefixWord ++ tailWord_46135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46135).length < 2 ^ (prefixWord ++ tailWord_46135).sum := by decide
  have hdescent : baseEnd_46135 < baseStart_46135 := by decide
  rcases family_descends (prefixWord ++ tailWord_46135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46149 : List Nat := [1, 3, 1, 1, 1, 3, 3, 8]
def baseStart_46149 : Nat := 118140960795 + 46149 * 2 ^ 59
def prefixEnd_46149 : Nat := 4983230072969 + 3 ^ 40 * 46149 * 2
def baseEnd_46149 : Nat := 3510610181399285263003

theorem tailTrace_46149 : CollatzResearch.WordTrace tailWord_46149 prefixEnd_46149 3510610181399285263003 := by
  unfold tailWord_46149
  simp only [CollatzResearch.WordTrace]
  refine ⟨1683192309817529466821501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1122128206545019644547667 1683192309817529466821501)
  ·
    refine ⟨631197116181573550058063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1683192309817529466821501 631197116181573550058063)
    ·
      refine ⟨946795674272360325087095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 631197116181573550058063 946795674272360325087095)
      ·
        refine ⟨1420193511408540487630643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946795674272360325087095 1420193511408540487630643)
        ·
          refine ⟨2130290267112810731445965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420193511408540487630643 2130290267112810731445965)
          ·
            refine ⟨798858850167304024292237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2130290267112810731445965 798858850167304024292237)
            ·
              refine ⟨299572068812739009109589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 798858850167304024292237 299572068812739009109589)
              ·
                refine ⟨3510610181399285263003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 299572068812739009109589 3510610181399285263003)
                ·
                  rfl

theorem cell21_46149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 8].length) (baseStart_46149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46149 prefixEnd_46149 := by exact prefixLift 46149
  have htrace : WordTrace (prefixWord ++ tailWord_46149) baseStart_46149 baseEnd_46149 := by
    simpa [prefixWord, tailWord_46149, baseEnd_46149] using wordTrace_append hprefix tailTrace_46149
  have hstable : (prefixWord ++ tailWord_46149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46149).length < 2 ^ (prefixWord ++ tailWord_46149).sum := by decide
  have hdescent : baseEnd_46149 < baseStart_46149 := by decide
  rcases family_descends (prefixWord ++ tailWord_46149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46211 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 4]
def baseStart_46211 : Nat := 118140960795 + 46211 * 2 ^ 59
def prefixEnd_46211 : Nat := 4983230072969 + 3 ^ 40 * 46211 * 2
def baseEnd_46211 : Nat := 10545979788899525755549

theorem tailTrace_46211 : CollatzResearch.WordTrace tailWord_46211 prefixEnd_46211 10545979788899525755549 := by
  unfold tailWord_46211
  simp only [CollatzResearch.WordTrace]
  refine ⟨1685453635592914055578487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1123635757061942703718991 1685453635592914055578487)
  ·
    refine ⟨2528180453389371083367731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1685453635592914055578487 2528180453389371083367731)
    ·
      refine ⟨3792270680084056625051597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2528180453389371083367731 3792270680084056625051597)
      ·
        refine ⟨1422101505031521234394349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3792270680084056625051597 1422101505031521234394349)
        ·
          refine ⟨533288064386820462897881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1422101505031521234394349 533288064386820462897881)
          ·
            refine ⟨399966048290115347173411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533288064386820462897881 399966048290115347173411)
            ·
              refine ⟨599949072435173020760117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399966048290115347173411 599949072435173020760117)
              ·
                refine ⟨56245225540797470696261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 599949072435173020760117 56245225540797470696261)
                ·
                  refine ⟨10545979788899525755549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56245225540797470696261 10545979788899525755549)
                  ·
                    rfl

theorem cell21_46211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 4].length) (baseStart_46211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46211 prefixEnd_46211 := by exact prefixLift 46211
  have htrace : WordTrace (prefixWord ++ tailWord_46211) baseStart_46211 baseEnd_46211 := by
    simpa [prefixWord, tailWord_46211, baseEnd_46211] using wordTrace_append hprefix tailTrace_46211
  have hstable : (prefixWord ++ tailWord_46211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46211).length < 2 ^ (prefixWord ++ tailWord_46211).sum := by decide
  have hdescent : baseEnd_46211 < baseStart_46211 := by decide
  rcases family_descends (prefixWord ++ tailWord_46211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46276 : List Nat := [2, 3, 3, 1, 3, 2, 2, 5]
def baseStart_46276 : Nat := 118140960795 + 46276 * 2 ^ 59
def prefixEnd_46276 : Nat := 4983230072969 + 3 ^ 40 * 46276 * 2
def baseEnd_46276 : Nat := 3520271224824619057361

theorem tailTrace_46276 : CollatzResearch.WordTrace tailWord_46276 prefixEnd_46276 3520271224824619057361 := by
  unfold tailWord_46276
  simp only [CollatzResearch.WordTrace]
  refine ⟨843912190178715078347341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1125216253571620104463121 843912190178715078347341)
  ·
    refine ⟨316467071317018154380253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 843912190178715078347341 316467071317018154380253)
    ·
      refine ⟨118675151743881807892595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316467071317018154380253 118675151743881807892595)
      ·
        refine ⟨178012727615822711838893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118675151743881807892595 178012727615822711838893)
        ·
          refine ⟨66754772855933516939585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178012727615822711838893 66754772855933516939585)
          ·
            refine ⟨50066079641950137704689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66754772855933516939585 50066079641950137704689)
            ·
              refine ⟨37549559731462603278517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50066079641950137704689 37549559731462603278517)
              ·
                refine ⟨3520271224824619057361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37549559731462603278517 3520271224824619057361)
                ·
                  rfl

theorem cell21_46276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_46276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46276 prefixEnd_46276 := by exact prefixLift 46276
  have htrace : WordTrace (prefixWord ++ tailWord_46276) baseStart_46276 baseEnd_46276 := by
    simpa [prefixWord, tailWord_46276, baseEnd_46276] using wordTrace_append hprefix tailTrace_46276
  have hstable : (prefixWord ++ tailWord_46276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46276).length < 2 ^ (prefixWord ++ tailWord_46276).sum := by decide
  have hdescent : baseEnd_46276 < baseStart_46276 := by decide
  rcases family_descends (prefixWord ++ tailWord_46276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46394 : List Nat := [3, 1, 1, 1, 4, 1, 5, 5]
def baseStart_46394 : Nat := 118140960795 + 46394 * 2 ^ 59
def prefixEnd_46394 : Nat := 4983230072969 + 3 ^ 40 * 46394 * 2
def baseEnd_46394 : Nat := 3529247627377291401725

theorem tailTrace_46394 : CollatzResearch.WordTrace tailWord_46394 prefixEnd_46394 3529247627377291401725 := by
  unfold tailWord_46394
  simp only [CollatzResearch.WordTrace]
  refine ⟨423032048482484077372559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1128085462619957539660157 423032048482484077372559)
  ·
    refine ⟨634548072723726116058839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 423032048482484077372559 634548072723726116058839)
    ·
      refine ⟨951822109085589174088259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 634548072723726116058839 951822109085589174088259)
      ·
        refine ⟨1427733163628383761132389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951822109085589174088259 1427733163628383761132389)
        ·
          refine ⟨267699968180321955212323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1427733163628383761132389 267699968180321955212323)
          ·
            refine ⟨401549952270482932818485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267699968180321955212323 401549952270482932818485)
            ·
              refine ⟨37645308025357774951733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 401549952270482932818485 37645308025357774951733)
              ·
                refine ⟨3529247627377291401725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37645308025357774951733 3529247627377291401725)
                ·
                  rfl

theorem cell21_46394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_46394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46394 prefixEnd_46394 := by exact prefixLift 46394
  have htrace : WordTrace (prefixWord ++ tailWord_46394) baseStart_46394 baseEnd_46394 := by
    simpa [prefixWord, tailWord_46394, baseEnd_46394] using wordTrace_append hprefix tailTrace_46394
  have hstable : (prefixWord ++ tailWord_46394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46394).length < 2 ^ (prefixWord ++ tailWord_46394).sum := by decide
  have hdescent : baseEnd_46394 < baseStart_46394 := by decide
  rcases family_descends (prefixWord ++ tailWord_46394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46425 : List Nat := [1, 2, 1, 2, 2, 2, 4, 4, 3]
def baseStart_46425 : Nat := 118140960795 + 46425 * 2 ^ 59
def prefixEnd_46425 : Nat := 4983230072969 + 3 ^ 40 * 46425 * 2
def baseEnd_46425 : Nat := 10594817504482709188445

theorem tailTrace_46425 : CollatzResearch.WordTrace tailWord_46425 prefixEnd_46425 10594817504482709188445 := by
  unfold tailWord_46425
  simp only [CollatzResearch.WordTrace]
  refine ⟨1693258856817628603868729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1128839237878419069245819 1693258856817628603868729)
  ·
    refine ⟨1269944142613221452901547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1693258856817628603868729 1269944142613221452901547)
    ·
      refine ⟨1904916213919832179352321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1269944142613221452901547 1904916213919832179352321)
      ·
        refine ⟨1428687160439874134514241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1904916213919832179352321 1428687160439874134514241)
        ·
          refine ⟨1071515370329905600885681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1428687160439874134514241 1071515370329905600885681)
          ·
            refine ⟨803636527747429200664261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1071515370329905600885681 803636527747429200664261)
            ·
              refine ⟨150681848952642975124549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 803636527747429200664261 150681848952642975124549)
              ·
                refine ⟨28252846678620557835853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150681848952642975124549 28252846678620557835853)
                ·
                  refine ⟨10594817504482709188445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28252846678620557835853 10594817504482709188445)
                  ·
                    rfl

theorem cell21_46425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 3].length) (baseStart_46425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46425 prefixEnd_46425 := by exact prefixLift 46425
  have htrace : WordTrace (prefixWord ++ tailWord_46425) baseStart_46425 baseEnd_46425 := by
    simpa [prefixWord, tailWord_46425, baseEnd_46425] using wordTrace_append hprefix tailTrace_46425
  have hstable : (prefixWord ++ tailWord_46425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46425).length < 2 ^ (prefixWord ++ tailWord_46425).sum := by decide
  have hdescent : baseEnd_46425 < baseStart_46425 := by decide
  rcases family_descends (prefixWord ++ tailWord_46425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46532 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 4]
def baseStart_46532 : Nat := 118140960795 + 46532 * 2 ^ 59
def prefixEnd_46532 : Nat := 4983230072969 + 3 ^ 40 * 46532 * 2
def baseEnd_46532 : Nat := 10619236362274300904893

theorem tailTrace_46532 : CollatzResearch.WordTrace tailWord_46532 prefixEnd_46532 10619236362274300904893 := by
  unfold tailWord_46532
  simp only [CollatzResearch.WordTrace]
  refine ⟨848580733714992939006925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1131440978286657252009233 848580733714992939006925)
  ·
    refine ⟨318217775143122352127597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 848580733714992939006925 318217775143122352127597)
    ·
      refine ⟨119331665678670882047849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 318217775143122352127597 119331665678670882047849)
      ·
        refine ⟨89498749259003161535887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119331665678670882047849 89498749259003161535887)
        ·
          refine ⟨134248123888504742303831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89498749259003161535887 134248123888504742303831)
          ·
            refine ⟨201372185832757113455747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134248123888504742303831 201372185832757113455747)
            ·
              refine ⟨302058278749135670183621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201372185832757113455747 302058278749135670183621)
              ·
                refine ⟨56635927265462938159429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302058278749135670183621 56635927265462938159429)
                ·
                  refine ⟨10619236362274300904893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56635927265462938159429 10619236362274300904893)
                  ·
                    rfl

theorem cell21_46532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_46532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46532 prefixEnd_46532 := by exact prefixLift 46532
  have htrace : WordTrace (prefixWord ++ tailWord_46532) baseStart_46532 baseEnd_46532 := by
    simpa [prefixWord, tailWord_46532, baseEnd_46532] using wordTrace_append hprefix tailTrace_46532
  have hstable : (prefixWord ++ tailWord_46532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46532).length < 2 ^ (prefixWord ++ tailWord_46532).sum := by decide
  have hdescent : baseEnd_46532 < baseStart_46532 := by decide
  rcases family_descends (prefixWord ++ tailWord_46532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46577 : List Nat := [1, 2, 2, 2, 3, 2, 1, 5, 3]
def baseStart_46577 : Nat := 118140960795 + 46577 * 2 ^ 59
def prefixEnd_46577 : Nat := 4983230072969 + 3 ^ 40 * 46577 * 2
def baseEnd_46577 : Nat := 10629505975364222654801

theorem tailTrace_46577 : CollatzResearch.WordTrace tailWord_46577 prefixEnd_46577 10629505975364222654801 := by
  unfold tailWord_46577
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698802752266958563401985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1132535168177972375601323 1698802752266958563401985)
  ·
    refine ⟨1274102064200218922551489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1698802752266958563401985 1274102064200218922551489)
    ·
      refine ⟨955576548150164191913617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1274102064200218922551489 955576548150164191913617)
      ·
        refine ⟨716682411112623143935213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 955576548150164191913617 716682411112623143935213)
        ·
          refine ⟨268755904167233678975705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 716682411112623143935213 268755904167233678975705)
          ·
            refine ⟨201566928125425259231779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268755904167233678975705 201566928125425259231779)
            ·
              refine ⟨302350392188137888847669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201566928125425259231779 302350392188137888847669)
              ·
                refine ⟨28345349267637927079469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302350392188137888847669 28345349267637927079469)
                ·
                  refine ⟨10629505975364222654801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28345349267637927079469 10629505975364222654801)
                  ·
                    rfl

theorem cell21_46577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 3].length) (baseStart_46577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46577 prefixEnd_46577 := by exact prefixLift 46577
  have htrace : WordTrace (prefixWord ++ tailWord_46577) baseStart_46577 baseEnd_46577 := by
    simpa [prefixWord, tailWord_46577, baseEnd_46577] using wordTrace_append hprefix tailTrace_46577
  have hstable : (prefixWord ++ tailWord_46577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46577).length < 2 ^ (prefixWord ++ tailWord_46577).sum := by decide
  have hdescent : baseEnd_46577 < baseStart_46577 := by decide
  rcases family_descends (prefixWord ++ tailWord_46577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46594 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_46594 : Nat := 118140960795 + 46594 * 2 ^ 59
def prefixEnd_46594 : Nat := 4983230072969 + 3 ^ 40 * 46594 * 2
def baseEnd_46594 : Nat := 10633385606975970871433

theorem tailTrace_46594 : CollatzResearch.WordTrace tailWord_46594 prefixEnd_46594 10633385606975970871433 := by
  unfold tailWord_46594
  simp only [CollatzResearch.WordTrace]
  refine ⟨424855698301342616692709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1132948528803580311180557 424855698301342616692709)
  ·
    refine ⟨79660443431501740629883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 424855698301342616692709 79660443431501740629883)
    ·
      refine ⟨119490665147252610944825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79660443431501740629883 119490665147252610944825)
      ·
        refine ⟨89617998860439458208619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119490665147252610944825 89617998860439458208619)
        ·
          refine ⟨134426998290659187312929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89617998860439458208619 134426998290659187312929)
          ·
            refine ⟨100820248717994390484697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134426998290659187312929 100820248717994390484697)
            ·
              refine ⟨75615186538495792863523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100820248717994390484697 75615186538495792863523)
              ·
                refine ⟨113422779807743689295285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75615186538495792863523 113422779807743689295285)
                ·
                  refine ⟨10633385606975970871433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113422779807743689295285 10633385606975970871433)
                  ·
                    rfl

theorem cell21_46594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_46594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46594 prefixEnd_46594 := by exact prefixLift 46594
  have htrace : WordTrace (prefixWord ++ tailWord_46594) baseStart_46594 baseEnd_46594 := by
    simpa [prefixWord, tailWord_46594, baseEnd_46594] using wordTrace_append hprefix tailTrace_46594
  have hstable : (prefixWord ++ tailWord_46594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46594).length < 2 ^ (prefixWord ++ tailWord_46594).sum := by decide
  have hdescent : baseEnd_46594 < baseStart_46594 := by decide
  rcases family_descends (prefixWord ++ tailWord_46594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46650 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_46650 : Nat := 118140960795 + 46650 * 2 ^ 59
def prefixEnd_46650 : Nat := 4983230072969 + 3 ^ 40 * 46650 * 2
def baseEnd_46650 : Nat := 10646165569932317937985

theorem tailTrace_46650 : CollatzResearch.WordTrace tailWord_46650 prefixEnd_46650 10646165569932317937985 := by
  unfold tailWord_46650
  simp only [CollatzResearch.WordTrace]
  refine ⟨425366320250623007702351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1134310187334994687206269 425366320250623007702351)
  ·
    refine ⟨638049480375934511553527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 425366320250623007702351 638049480375934511553527)
    ·
      refine ⟨957074220563901767330291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638049480375934511553527 957074220563901767330291)
      ·
        refine ⟨1435611330845852650995437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957074220563901767330291 1435611330845852650995437)
        ·
          refine ⟨538354249067194744123289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1435611330845852650995437 538354249067194744123289)
          ·
            refine ⟨403765686800396058092467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538354249067194744123289 403765686800396058092467)
            ·
              refine ⟨605648530200594087138701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403765686800396058092467 605648530200594087138701)
              ·
                refine ⟨227118198825222782677013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 605648530200594087138701 227118198825222782677013)
                ·
                  refine ⟨10646165569932317937985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 227118198825222782677013 10646165569932317937985)
                  ·
                    rfl

theorem cell21_46650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_46650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46650 prefixEnd_46650 := by exact prefixLift 46650
  have htrace : WordTrace (prefixWord ++ tailWord_46650) baseStart_46650 baseEnd_46650 := by
    simpa [prefixWord, tailWord_46650, baseEnd_46650] using wordTrace_append hprefix tailTrace_46650
  have hstable : (prefixWord ++ tailWord_46650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46650).length < 2 ^ (prefixWord ++ tailWord_46650).sum := by decide
  have hdescent : baseEnd_46650 < baseStart_46650 := by decide
  rcases family_descends (prefixWord ++ tailWord_46650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46788 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_46788 : Nat := 118140960795 + 46788 * 2 ^ 59
def prefixEnd_46788 : Nat := 4983230072969 + 3 ^ 40 * 46788 * 2
def baseEnd_46788 : Nat := 10677659050074744637703

theorem tailTrace_46788 : CollatzResearch.WordTrace tailWord_46788 prefixEnd_46788 10677659050074744637703 := by
  unfold tailWord_46788
  simp only [CollatzResearch.WordTrace]
  refine ⟨853249277251270799666509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1137665703001694399555345 853249277251270799666509)
  ·
    refine ⟨319968478969226549874941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 853249277251270799666509 319968478969226549874941)
    ·
      refine ⟨119988179613459956203103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 319968478969226549874941 119988179613459956203103)
      ·
        refine ⟨179982269420189934304655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119988179613459956203103 179982269420189934304655)
        ·
          refine ⟨269973404130284901456983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179982269420189934304655 269973404130284901456983)
          ·
            refine ⟨404960106195427352185475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269973404130284901456983 404960106195427352185475)
            ·
              refine ⟨607440159293141028278213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404960106195427352185475 607440159293141028278213)
              ·
                refine ⟨113895029867463942802165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 607440159293141028278213 113895029867463942802165)
                ·
                  refine ⟨10677659050074744637703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113895029867463942802165 10677659050074744637703)
                  ·
                    rfl

theorem cell21_46788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_46788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46788 prefixEnd_46788 := by exact prefixLift 46788
  have htrace : WordTrace (prefixWord ++ tailWord_46788) baseStart_46788 baseEnd_46788 := by
    simpa [prefixWord, tailWord_46788, baseEnd_46788] using wordTrace_append hprefix tailTrace_46788
  have hstable : (prefixWord ++ tailWord_46788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46788).length < 2 ^ (prefixWord ++ tailWord_46788).sum := by decide
  have hdescent : baseEnd_46788 < baseStart_46788 := by decide
  rcases family_descends (prefixWord ++ tailWord_46788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46816 : List Nat := [2, 1, 1, 3, 1, 2, 11]
def baseStart_46816 : Nat := 118140960795 + 46816 * 2 ^ 59
def prefixEnd_46816 : Nat := 4983230072969 + 3 ^ 40 * 46816 * 2
def baseEnd_46816 : Nat := 1187116559061435352331

theorem tailTrace_46816 : CollatzResearch.WordTrace tailWord_46816 prefixEnd_46816 1187116559061435352331 := by
  unfold tailWord_46816
  simp only [CollatzResearch.WordTrace]
  refine ⟨853759899200551190676151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1138346532267401587568201 853759899200551190676151)
  ·
    refine ⟨1280639848800826786014227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853759899200551190676151 1280639848800826786014227)
    ·
      refine ⟨1920959773201240179021341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1280639848800826786014227 1920959773201240179021341)
      ·
        refine ⟨720359914950465067133003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1920959773201240179021341 720359914950465067133003)
        ·
          refine ⟨1080539872425697600699505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720359914950465067133003 1080539872425697600699505)
          ·
            refine ⟨810404904319273200524629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1080539872425697600699505 810404904319273200524629)
            ·
              refine ⟨1187116559061435352331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 810404904319273200524629 1187116559061435352331)
              ·
                rfl

theorem cell21_46816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 11].length) (baseStart_46816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46816 prefixEnd_46816 := by exact prefixLift 46816
  have htrace : WordTrace (prefixWord ++ tailWord_46816) baseStart_46816 baseEnd_46816 := by
    simpa [prefixWord, tailWord_46816, baseEnd_46816] using wordTrace_append hprefix tailTrace_46816
  have hstable : (prefixWord ++ tailWord_46816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46816).length < 2 ^ (prefixWord ++ tailWord_46816).sum := by decide
  have hdescent : baseEnd_46816 < baseStart_46816 := by decide
  rcases family_descends (prefixWord ++ tailWord_46816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46833 : List Nat := [1, 2, 2, 2, 2, 4, 2, 6]
def baseStart_46833 : Nat := 118140960795 + 46833 * 2 ^ 59
def prefixEnd_46833 : Nat := 4983230072969 + 3 ^ 40 * 46833 * 2
def baseEnd_46833 : Nat := 3562642887721555462537

theorem tailTrace_46833 : CollatzResearch.WordTrace tailWord_46833 prefixEnd_46833 3562642887721555462537 := by
  unfold tailWord_46833
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708139839339514284721153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1138759892893009523147435 1708139839339514284721153)
  ·
    refine ⟨1281104879504635713540865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1708139839339514284721153 1281104879504635713540865)
    ·
      refine ⟨960828659628476785155649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1281104879504635713540865 960828659628476785155649)
      ·
        refine ⟨720621494721357588866737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 960828659628476785155649 720621494721357588866737)
        ·
          refine ⟨540466121041018191650053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 720621494721357588866737 540466121041018191650053)
          ·
            refine ⟨101337397695190910934385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 540466121041018191650053 101337397695190910934385)
            ·
              refine ⟨76003048271393183200789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101337397695190910934385 76003048271393183200789)
              ·
                refine ⟨3562642887721555462537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76003048271393183200789 3562642887721555462537)
                ·
                  rfl

theorem cell21_46833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 6].length) (baseStart_46833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46833 prefixEnd_46833 := by exact prefixLift 46833
  have htrace : WordTrace (prefixWord ++ tailWord_46833) baseStart_46833 baseEnd_46833 := by
    simpa [prefixWord, tailWord_46833, baseEnd_46833] using wordTrace_append hprefix tailTrace_46833
  have hstable : (prefixWord ++ tailWord_46833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46833).length < 2 ^ (prefixWord ++ tailWord_46833).sum := by decide
  have hdescent : baseEnd_46833 < baseStart_46833 := by decide
  rcases family_descends (prefixWord ++ tailWord_46833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46847 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 5]
def baseStart_46847 : Nat := 118140960795 + 46847 * 2 ^ 59
def prefixEnd_46847 : Nat := 4983230072969 + 3 ^ 40 * 46847 * 2
def baseEnd_46847 : Nat := 10691123653903753154249

theorem tailTrace_46847 : CollatzResearch.WordTrace tailWord_46847 prefixEnd_46847 10691123653903753154249 := by
  unfold tailWord_46847
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708650461288794675730795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1139100307525863117153863 1708650461288794675730795)
  ·
    refine ⟨2562975691933192013596193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708650461288794675730795 2562975691933192013596193)
    ·
      refine ⟨1922231768949894010197145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2562975691933192013596193 1922231768949894010197145)
      ·
        refine ⟨1441673826712420507647859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1922231768949894010197145 1441673826712420507647859)
        ·
          refine ⟨2162510740068630761471789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1441673826712420507647859 2162510740068630761471789)
          ·
            refine ⟨810941527525736535551921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2162510740068630761471789 810941527525736535551921)
            ·
              refine ⟨608206145644302401663941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810941527525736535551921 608206145644302401663941)
              ·
                refine ⟨114038652308306700311989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 608206145644302401663941 114038652308306700311989)
                ·
                  refine ⟨10691123653903753154249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114038652308306700311989 10691123653903753154249)
                  ·
                    rfl

theorem cell21_46847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_46847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46847 prefixEnd_46847 := by exact prefixLift 46847
  have htrace : WordTrace (prefixWord ++ tailWord_46847) baseStart_46847 baseEnd_46847 := by
    simpa [prefixWord, tailWord_46847, baseEnd_46847] using wordTrace_append hprefix tailTrace_46847
  have hstable : (prefixWord ++ tailWord_46847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46847).length < 2 ^ (prefixWord ++ tailWord_46847).sum := by decide
  have hdescent : baseEnd_46847 < baseStart_46847 := by decide
  rcases family_descends (prefixWord ++ tailWord_46847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46881 : List Nat := [1, 2, 3, 2, 1, 4, 1, 4, 3]
def baseStart_46881 : Nat := 118140960795 + 46881 * 2 ^ 59
def prefixEnd_46881 : Nat := 4983230072969 + 3 ^ 40 * 46881 * 2
def baseEnd_46881 : Nat := 10698882917127249587513

theorem tailTrace_46881 : CollatzResearch.WordTrace tailWord_46881 prefixEnd_46881 10698882917127249587513 := by
  unfold tailWord_46881
  simp only [CollatzResearch.WordTrace]
  refine ⟨1709890543165618482468497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1139927028777078988312331 1709890543165618482468497)
  ·
    refine ⟨1282417907374213861851373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1709890543165618482468497 1282417907374213861851373)
    ·
      refine ⟨480906715265330198194265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1282417907374213861851373 480906715265330198194265)
      ·
        refine ⟨360680036448997648645699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480906715265330198194265 360680036448997648645699)
        ·
          refine ⟨541020054673496472968549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360680036448997648645699 541020054673496472968549)
          ·
            refine ⟨101441260251280588681603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 541020054673496472968549 101441260251280588681603)
            ·
              refine ⟨152161890376920883022405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101441260251280588681603 152161890376920883022405)
              ·
                refine ⟨28530354445672665566701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152161890376920883022405 28530354445672665566701)
                ·
                  refine ⟨10698882917127249587513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28530354445672665566701 10698882917127249587513)
                  ·
                    rfl

theorem cell21_46881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 3].length) (baseStart_46881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_46881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_46881 prefixEnd_46881 := by exact prefixLift 46881
  have htrace : WordTrace (prefixWord ++ tailWord_46881) baseStart_46881 baseEnd_46881 := by
    simpa [prefixWord, tailWord_46881, baseEnd_46881] using wordTrace_append hprefix tailTrace_46881
  have hstable : (prefixWord ++ tailWord_46881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46881).length < 2 ^ (prefixWord ++ tailWord_46881).sum := by decide
  have hdescent : baseEnd_46881 < baseStart_46881 := by decide
  rcases family_descends (prefixWord ++ tailWord_46881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47044 : List Nat := [2, 3, 3, 13]
def baseStart_47044 : Nat := 118140960795 + 47044 * 2 ^ 59
def prefixEnd_47044 : Nat := 4983230072969 + 3 ^ 40 * 47044 * 2
def baseEnd_47044 : Nat := 44181406328704478891

theorem tailTrace_47044 : CollatzResearch.WordTrace tailWord_47044 prefixEnd_47044 44181406328704478891 := by
  unfold tailWord_47044
  simp only [CollatzResearch.WordTrace]
  refine ⟨857917820787548660326093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1143890427716731547101457 857917820787548660326093)
  ·
    refine ⟨321719182795330747622285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 857917820787548660326093 321719182795330747622285)
    ·
      refine ⟨120644693548249030358357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 321719182795330747622285 120644693548249030358357)
      ·
        refine ⟨44181406328704478891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 120644693548249030358357 44181406328704478891)
        ·
          rfl

theorem cell21_47044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 13].length) (baseStart_47044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47044 prefixEnd_47044 := by exact prefixLift 47044
  have htrace : WordTrace (prefixWord ++ tailWord_47044) baseStart_47044 baseEnd_47044 := by
    simpa [prefixWord, tailWord_47044, baseEnd_47044] using wordTrace_append hprefix tailTrace_47044
  have hstable : (prefixWord ++ tailWord_47044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47044).length < 2 ^ (prefixWord ++ tailWord_47044).sum := by decide
  have hdescent : baseEnd_47044 < baseStart_47044 := by decide
  rcases family_descends (prefixWord ++ tailWord_47044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47061 : List Nat := [1, 3, 2, 3, 2, 1, 3, 6]
def baseStart_47061 : Nat := 118140960795 + 47061 * 2 ^ 59
def prefixEnd_47061 : Nat := 4983230072969 + 3 ^ 40 * 47061 * 2
def baseEnd_47061 : Nat := 3579987123162312195715

theorem tailTrace_47061 : CollatzResearch.WordTrace tailWord_47061 prefixEnd_47061 3579987123162312195715 := by
  unfold tailWord_47061
  simp only [CollatzResearch.WordTrace]
  refine ⟨1716455682513509224021037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1144303788342339482680691 1716455682513509224021037)
  ·
    refine ⟨643670880942565959007889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1716455682513509224021037 643670880942565959007889)
    ·
      refine ⟨482753160706924469255917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 643670880942565959007889 482753160706924469255917)
      ·
        refine ⟨181032435265096675970969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 482753160706924469255917 181032435265096675970969)
        ·
          refine ⟨135774326448822506978227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181032435265096675970969 135774326448822506978227)
          ·
            refine ⟨203661489673233760467341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135774326448822506978227 203661489673233760467341)
            ·
              refine ⟨76373058627462660175253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203661489673233760467341 76373058627462660175253)
              ·
                refine ⟨3579987123162312195715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76373058627462660175253 3579987123162312195715)
                ·
                  rfl

theorem cell21_47061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 6].length) (baseStart_47061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47061 prefixEnd_47061 := by exact prefixLift 47061
  have htrace : WordTrace (prefixWord ++ tailWord_47061) baseStart_47061 baseEnd_47061 := by
    simpa [prefixWord, tailWord_47061, baseEnd_47061] using wordTrace_append hprefix tailTrace_47061
  have hstable : (prefixWord ++ tailWord_47061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47061).length < 2 ^ (prefixWord ++ tailWord_47061).sum := by decide
  have hdescent : baseEnd_47061 < baseStart_47061 := by decide
  rcases family_descends (prefixWord ++ tailWord_47061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47075 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 7]
def baseStart_47075 : Nat := 118140960795 + 47075 * 2 ^ 59
def prefixEnd_47075 : Nat := 4983230072969 + 3 ^ 40 * 47075 * 2
def baseEnd_47075 : Nat := 10743156360226023353783

theorem tailTrace_47075 : CollatzResearch.WordTrace tailWord_47075 prefixEnd_47075 10743156360226023353783 := by
  unfold tailWord_47075
  simp only [CollatzResearch.WordTrace]
  refine ⟨1716966304462789615030679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1144644202975193076687119 1716966304462789615030679)
  ·
    refine ⟨2575449456694184422546019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1716966304462789615030679 2575449456694184422546019)
    ·
      refine ⟨3863174185041276633819029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2575449456694184422546019 3863174185041276633819029)
      ·
        refine ⟨181086289923809842210267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3863174185041276633819029 181086289923809842210267)
        ·
          refine ⟨271629434885714763315401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181086289923809842210267 271629434885714763315401)
          ·
            refine ⟨203722076164286072486551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271629434885714763315401 203722076164286072486551)
            ·
              refine ⟨305583114246429108729827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203722076164286072486551 305583114246429108729827)
              ·
                refine ⟨458374671369643663094741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305583114246429108729827 458374671369643663094741)
                ·
                  refine ⟨10743156360226023353783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 458374671369643663094741 10743156360226023353783)
                  ·
                    rfl

theorem cell21_47075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_47075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47075 prefixEnd_47075 := by exact prefixLift 47075
  have htrace : WordTrace (prefixWord ++ tailWord_47075) baseStart_47075 baseEnd_47075 := by
    simpa [prefixWord, tailWord_47075, baseEnd_47075] using wordTrace_append hprefix tailTrace_47075
  have hstable : (prefixWord ++ tailWord_47075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47075).length < 2 ^ (prefixWord ++ tailWord_47075).sum := by decide
  have hdescent : baseEnd_47075 < baseStart_47075 := by decide
  rcases family_descends (prefixWord ++ tailWord_47075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47137 : List Nat := [1, 2, 3, 2, 4, 1, 1, 7]
def baseStart_47137 : Nat := 118140960795 + 47137 * 2 ^ 59
def prefixEnd_47137 : Nat := 4983230072969 + 3 ^ 40 * 47137 * 2
def baseEnd_47137 : Nat := 3585768534975897773441

theorem tailTrace_47137 : CollatzResearch.WordTrace tailWord_47137 prefixEnd_47137 3585768534975897773441 := by
  unfold tailWord_47137
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719227630238174203787665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1146151753492116135858443 1719227630238174203787665)
  ·
    refine ⟨1289420722678630652840749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1719227630238174203787665 1289420722678630652840749)
    ·
      refine ⟨483532771004486494815281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1289420722678630652840749 483532771004486494815281)
      ·
        refine ⟨362649578253364871111461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483532771004486494815281 362649578253364871111461)
        ·
          refine ⟨67996795922505913333399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 362649578253364871111461 67996795922505913333399)
          ·
            refine ⟨101995193883758870000099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67996795922505913333399 101995193883758870000099)
            ·
              refine ⟨152992790825638305000149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101995193883758870000099 152992790825638305000149)
              ·
                refine ⟨3585768534975897773441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 152992790825638305000149 3585768534975897773441)
                ·
                  rfl

theorem cell21_47137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 7].length) (baseStart_47137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47137 prefixEnd_47137 := by exact prefixLift 47137
  have htrace : WordTrace (prefixWord ++ tailWord_47137) baseStart_47137 baseEnd_47137 := by
    simpa [prefixWord, tailWord_47137, baseEnd_47137] using wordTrace_append hprefix tailTrace_47137
  have hstable : (prefixWord ++ tailWord_47137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47137).length < 2 ^ (prefixWord ++ tailWord_47137).sum := by decide
  have hdescent : baseEnd_47137 < baseStart_47137 := by decide
  rcases family_descends (prefixWord ++ tailWord_47137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47143 : List Nat := [1, 1, 7, 1, 2, 2, 1, 3, 3]
def baseStart_47143 : Nat := 118140960795 + 47143 * 2 ^ 59
def prefixEnd_47143 : Nat := 4983230072969 + 3 ^ 40 * 47143 * 2
def baseEnd_47143 : Nat := 10758674886673016220311

theorem tailTrace_47143 : CollatzResearch.WordTrace tailWord_47143 prefixEnd_47143 10758674886673016220311 := by
  unfold tailWord_47143
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719446468216437228506083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1146297645477624819004055 1719446468216437228506083)
  ·
    refine ⟨2579169702324655842759125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1719446468216437228506083 2579169702324655842759125)
    ·
      refine ⟨60449289898234121314667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2579169702324655842759125 60449289898234121314667)
      ·
        refine ⟨90673934847351181972001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60449289898234121314667 90673934847351181972001)
        ·
          refine ⟨68005451135513386479001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90673934847351181972001 68005451135513386479001)
          ·
            refine ⟨51004088351635039859251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68005451135513386479001 51004088351635039859251)
            ·
              refine ⟨76506132527452559788877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51004088351635039859251 76506132527452559788877)
              ·
                refine ⟨28689799697794709920829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76506132527452559788877 28689799697794709920829)
                ·
                  refine ⟨10758674886673016220311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28689799697794709920829 10758674886673016220311)
                  ·
                    rfl

theorem cell21_47143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 3].length) (baseStart_47143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47143 prefixEnd_47143 := by exact prefixLift 47143
  have htrace : WordTrace (prefixWord ++ tailWord_47143) baseStart_47143 baseEnd_47143 := by
    simpa [prefixWord, tailWord_47143, baseEnd_47143] using wordTrace_append hprefix tailTrace_47143
  have hstable : (prefixWord ++ tailWord_47143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47143).length < 2 ^ (prefixWord ++ tailWord_47143).sum := by decide
  have hdescent : baseEnd_47143 < baseStart_47143 := by decide
  rcases family_descends (prefixWord ++ tailWord_47143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47168 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 5]
def baseStart_47168 : Nat := 118140960795 + 47168 * 2 ^ 59
def prefixEnd_47168 : Nat := 4983230072969 + 3 ^ 40 * 47168 * 2
def baseEnd_47168 : Nat := 10764380227278528303593

theorem tailTrace_47168 : CollatzResearch.WordTrace tailWord_47168 prefixEnd_47168 10764380227278528303593 := by
  unfold tailWord_47168
  simp only [CollatzResearch.WordTrace]
  refine ⟨860179146562933249083079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1146905528750577665444105 860179146562933249083079)
  ·
    refine ⟨1290268719844399873624619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 860179146562933249083079 1290268719844399873624619)
    ·
      refine ⟨1935403079766599810436929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1290268719844399873624619 1935403079766599810436929)
      ·
        refine ⟨1451552309824949857827697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1935403079766599810436929 1451552309824949857827697)
        ·
          refine ⟨1088664232368712393370773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1451552309824949857827697 1088664232368712393370773)
          ·
            refine ⟨51031135892283393439255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1088664232368712393370773 51031135892283393439255)
            ·
              refine ⟨76546703838425090158883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51031135892283393439255 76546703838425090158883)
              ·
                refine ⟨114820055757637635238325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76546703838425090158883 114820055757637635238325)
                ·
                  refine ⟨10764380227278528303593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114820055757637635238325 10764380227278528303593)
                  ·
                    rfl

theorem cell21_47168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_47168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47168 prefixEnd_47168 := by exact prefixLift 47168
  have htrace : WordTrace (prefixWord ++ tailWord_47168) baseStart_47168 baseEnd_47168 := by
    simpa [prefixWord, tailWord_47168, baseEnd_47168] using wordTrace_append hprefix tailTrace_47168
  have hstable : (prefixWord ++ tailWord_47168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47168).length < 2 ^ (prefixWord ++ tailWord_47168).sum := by decide
  have hdescent : baseEnd_47168 < baseStart_47168 := by decide
  rcases family_descends (prefixWord ++ tailWord_47168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47261 : List Nat := [1, 4, 2, 1, 1, 4, 2, 3, 3]
def baseStart_47261 : Nat := 118140960795 + 47261 * 2 ^ 59
def prefixEnd_47261 : Nat := 4983230072969 + 3 ^ 40 * 47261 * 2
def baseEnd_47261 : Nat := 10785604094331033253403

theorem tailTrace_47261 : CollatzResearch.WordTrace tailWord_47261 prefixEnd_47261 10785604094331033253403 := by
  unfold tailWord_47261
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723750281788943381301637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1149166854525962254201091 1723750281788943381301637)
  ·
    refine ⟨323203177835426883994057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1723750281788943381301637 323203177835426883994057)
    ·
      refine ⟨242402383376570162995543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323203177835426883994057 242402383376570162995543)
      ·
        refine ⟨363603575064855244493315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242402383376570162995543 363603575064855244493315)
        ·
          refine ⟨545405362597282866739973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363603575064855244493315 545405362597282866739973)
          ·
            refine ⟨102263505486990537513745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 545405362597282866739973 102263505486990537513745)
            ·
              refine ⟨76697629115242903135309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102263505486990537513745 76697629115242903135309)
              ·
                refine ⟨28761610918216088675741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76697629115242903135309 28761610918216088675741)
                ·
                  refine ⟨10785604094331033253403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28761610918216088675741 10785604094331033253403)
                  ·
                    rfl

theorem cell21_47261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_47261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47261 prefixEnd_47261 := by exact prefixLift 47261
  have htrace : WordTrace (prefixWord ++ tailWord_47261) baseStart_47261 baseEnd_47261 := by
    simpa [prefixWord, tailWord_47261, baseEnd_47261] using wordTrace_append hprefix tailTrace_47261
  have hstable : (prefixWord ++ tailWord_47261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47261).length < 2 ^ (prefixWord ++ tailWord_47261).sum := by decide
  have hdescent : baseEnd_47261 < baseStart_47261 := by decide
  rcases family_descends (prefixWord ++ tailWord_47261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47278 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_47278 : Nat := 118140960795 + 47278 * 2 ^ 59
def prefixEnd_47278 : Nat := 4983230072969 + 3 ^ 40 * 47278 * 2
def baseEnd_47278 : Nat := 10789483725942781470035

theorem tailTrace_47278 : CollatzResearch.WordTrace tailWord_47278 prefixEnd_47278 10789483725942781470035 := by
  unfold tailWord_47278
  simp only [CollatzResearch.WordTrace]
  refine ⟨215546290340919410583811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1149580215151570189780325 215546290340919410583811)
  ·
    refine ⟨323319435511379115875717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215546290340919410583811 323319435511379115875717)
    ·
      refine ⟨60622394158383584226697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323319435511379115875717 60622394158383584226697)
      ·
        refine ⟨45466795618787688170023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60622394158383584226697 45466795618787688170023)
        ·
          refine ⟨68200193428181532255035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45466795618787688170023 68200193428181532255035)
          ·
            refine ⟨102300290142272298382553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68200193428181532255035 102300290142272298382553)
            ·
              refine ⟨76725217606704223786915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102300290142272298382553 76725217606704223786915)
              ·
                refine ⟨115087826410056335680373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76725217606704223786915 115087826410056335680373)
                ·
                  refine ⟨10789483725942781470035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115087826410056335680373 10789483725942781470035)
                  ·
                    rfl

theorem cell21_47278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_47278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47278 prefixEnd_47278 := by exact prefixLift 47278
  have htrace : WordTrace (prefixWord ++ tailWord_47278) baseStart_47278 baseEnd_47278 := by
    simpa [prefixWord, tailWord_47278, baseEnd_47278] using wordTrace_append hprefix tailTrace_47278
  have hstable : (prefixWord ++ tailWord_47278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47278).length < 2 ^ (prefixWord ++ tailWord_47278).sum := by decide
  have hdescent : baseEnd_47278 < baseStart_47278 := by decide
  rcases family_descends (prefixWord ++ tailWord_47278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47292 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 4]
def baseStart_47292 : Nat := 118140960795 + 47292 * 2 ^ 59
def prefixEnd_47292 : Nat := 4983230072969 + 3 ^ 40 * 47292 * 2
def baseEnd_47292 : Nat := 10792678716681868236673

theorem tailTrace_47292 : CollatzResearch.WordTrace tailWord_47292 prefixEnd_47292 10792678716681868236673 := by
  unfold tailWord_47292
  simp only [CollatzResearch.WordTrace]
  refine ⟨862440472338317837840065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1149920629784423783786753 862440472338317837840065)
  ·
    refine ⟨646830354253738378380049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 862440472338317837840065 646830354253738378380049)
    ·
      refine ⟨485122765690303783785037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 646830354253738378380049 485122765690303783785037)
      ·
        refine ⟨181921037133863918919389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485122765690303783785037 181921037133863918919389)
        ·
          refine ⟨68220388925198969594771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181921037133863918919389 68220388925198969594771)
          ·
            refine ⟨102330583387798454392157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68220388925198969594771 102330583387798454392157)
            ·
              refine ⟨38373968770424420397059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102330583387798454392157 38373968770424420397059)
              ·
                refine ⟨57560953155636630595589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38373968770424420397059 57560953155636630595589)
                ·
                  refine ⟨10792678716681868236673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57560953155636630595589 10792678716681868236673)
                  ·
                    rfl

theorem cell21_47292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_47292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47292 prefixEnd_47292 := by exact prefixLift 47292
  have htrace : WordTrace (prefixWord ++ tailWord_47292) baseStart_47292 baseEnd_47292 := by
    simpa [prefixWord, tailWord_47292, baseEnd_47292] using wordTrace_append hprefix tailTrace_47292
  have hstable : (prefixWord ++ tailWord_47292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47292).length < 2 ^ (prefixWord ++ tailWord_47292).sum := by decide
  have hdescent : baseEnd_47292 < baseStart_47292 := by decide
  rcases family_descends (prefixWord ++ tailWord_47292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47393 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 6]
def baseStart_47393 : Nat := 118140960795 + 47393 * 2 ^ 59
def prefixEnd_47393 : Nat := 4983230072969 + 3 ^ 40 * 47393 * 2
def baseEnd_47393 : Nat := 10815728292728137053133

theorem tailTrace_47393 : CollatzResearch.WordTrace tailWord_47393 prefixEnd_47393 10815728292728137053133 := by
  unfold tailWord_47393
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728564717310729925106833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1152376478207153283404555 1728564717310729925106833)
  ·
    refine ⟨1296423537983047443830125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1728564717310729925106833 1296423537983047443830125)
    ·
      refine ⟨486158826743642791436297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1296423537983047443830125 486158826743642791436297)
      ·
        refine ⟨364619120057732093577223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486158826743642791436297 364619120057732093577223)
        ·
          refine ⟨546928680086598140365835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364619120057732093577223 546928680086598140365835)
          ·
            refine ⟨820393020129897210548753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546928680086598140365835 820393020129897210548753)
            ·
              refine ⟨615294765097422907911565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820393020129897210548753 615294765097422907911565)
              ·
                refine ⟨230735536911533590466837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 615294765097422907911565 230735536911533590466837)
                ·
                  refine ⟨10815728292728137053133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 230735536911533590466837 10815728292728137053133)
                  ·
                    rfl

theorem cell21_47393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_47393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47393 prefixEnd_47393 := by exact prefixLift 47393
  have htrace : WordTrace (prefixWord ++ tailWord_47393) baseStart_47393 baseEnd_47393 := by
    simpa [prefixWord, tailWord_47393, baseEnd_47393] using wordTrace_append hprefix tailTrace_47393
  have hstable : (prefixWord ++ tailWord_47393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47393).length < 2 ^ (prefixWord ++ tailWord_47393).sum := by decide
  have hdescent : baseEnd_47393 < baseStart_47393 := by decide
  rcases family_descends (prefixWord ++ tailWord_47393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47489 : List Nat := [1, 2, 4, 3, 1, 1, 3, 3, 3]
def baseStart_47489 : Nat := 118140960795 + 47489 * 2 ^ 59
def prefixEnd_47489 : Nat := 4983230072969 + 3 ^ 40 * 47489 * 2
def baseEnd_47489 : Nat := 10837636800653303452937

theorem tailTrace_47489 : CollatzResearch.WordTrace tailWord_47489 prefixEnd_47489 10837636800653303452937 := by
  unfold tailWord_47489
  simp only [CollatzResearch.WordTrace]
  refine ⟨1732066124962938320601521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1154710749975292213734347 1732066124962938320601521)
  ·
    refine ⟨1299049593722203740451141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1732066124962938320601521 1299049593722203740451141)
    ·
      refine ⟨243571798822913201334589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1299049593722203740451141 243571798822913201334589)
      ·
        refine ⟨91339424558592450500471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243571798822913201334589 91339424558592450500471)
        ·
          refine ⟨137009136837888675750707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91339424558592450500471 137009136837888675750707)
          ·
            refine ⟨205513705256833013626061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137009136837888675750707 205513705256833013626061)
            ·
              refine ⟨77067639471312380109773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205513705256833013626061 77067639471312380109773)
              ·
                refine ⟨28900364801742142541165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77067639471312380109773 28900364801742142541165)
                ·
                  refine ⟨10837636800653303452937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28900364801742142541165 10837636800653303452937)
                  ·
                    rfl

theorem cell21_47489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 3].length) (baseStart_47489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47489 prefixEnd_47489 := by exact prefixLift 47489
  have htrace : WordTrace (prefixWord ++ tailWord_47489) baseStart_47489 baseEnd_47489 := by
    simpa [prefixWord, tailWord_47489, baseEnd_47489] using wordTrace_append hprefix tailTrace_47489
  have hstable : (prefixWord ++ tailWord_47489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47489).length < 2 ^ (prefixWord ++ tailWord_47489).sum := by decide
  have hdescent : baseEnd_47489 < baseStart_47489 := by decide
  rcases family_descends (prefixWord ++ tailWord_47489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47500 : List Nat := [2, 2, 1, 2, 1, 6, 7]
def baseStart_47500 : Nat := 118140960795 + 47500 * 2 ^ 59
def prefixEnd_47500 : Nat := 4983230072969 + 3 ^ 40 * 47500 * 2
def baseEnd_47500 : Nat := 1204460794502192085509

theorem tailTrace_47500 : CollatzResearch.WordTrace tailWord_47500 prefixEnd_47500 1204460794502192085509 := by
  unfold tailWord_47500
  simp only [CollatzResearch.WordTrace]
  refine ⟨866233663961543599625977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1154978218615391466167969 866233663961543599625977)
  ·
    refine ⟨649675247971157699719483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 866233663961543599625977 649675247971157699719483)
    ·
      refine ⟨974512871956736549579225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 649675247971157699719483 974512871956736549579225)
      ·
        refine ⟨730884653967552412184419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 974512871956736549579225 730884653967552412184419)
        ·
          refine ⟨1096326980951328618276629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730884653967552412184419 1096326980951328618276629)
          ·
            refine ⟨51390327232093528981717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1096326980951328618276629 51390327232093528981717)
            ·
              refine ⟨1204460794502192085509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 51390327232093528981717 1204460794502192085509)
              ·
                rfl

theorem cell21_47500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 7].length) (baseStart_47500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47500 prefixEnd_47500 := by exact prefixLift 47500
  have htrace : WordTrace (prefixWord ++ tailWord_47500) baseStart_47500 baseEnd_47500 := by
    simpa [prefixWord, tailWord_47500, baseEnd_47500] using wordTrace_append hprefix tailTrace_47500
  have hstable : (prefixWord ++ tailWord_47500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47500).length < 2 ^ (prefixWord ++ tailWord_47500).sum := by decide
  have hdescent : baseEnd_47500 < baseStart_47500 := by decide
  rcases family_descends (prefixWord ++ tailWord_47500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47517 : List Nat := [1, 4, 2, 1, 4, 1, 2, 6]
def baseStart_47517 : Nat := 118140960795 + 47517 * 2 ^ 59
def prefixEnd_47517 : Nat := 4983230072969 + 3 ^ 40 * 47517 * 2
def baseEnd_47517 : Nat := 3614675594043825662071

theorem tailTrace_47517 : CollatzResearch.WordTrace tailWord_47517 prefixEnd_47517 3614675594043825662071 := by
  unfold tailWord_47517
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733087368861499102620805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1155391579240999401747203 1733087368861499102620805)
  ·
    refine ⟨324953881661531081741401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1733087368861499102620805 324953881661531081741401)
    ·
      refine ⟨243715411246148311306051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324953881661531081741401 243715411246148311306051)
      ·
        refine ⟨365573116869222466959077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243715411246148311306051 365573116869222466959077)
        ·
          refine ⟨68544959412979212554827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365573116869222466959077 68544959412979212554827)
          ·
            refine ⟨102817439119468818832241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68544959412979212554827 102817439119468818832241)
            ·
              refine ⟨77113079339601614124181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102817439119468818832241 77113079339601614124181)
              ·
                refine ⟨3614675594043825662071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77113079339601614124181 3614675594043825662071)
                ·
                  rfl

theorem cell21_47517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 6].length) (baseStart_47517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47517 prefixEnd_47517 := by exact prefixLift 47517
  have htrace : WordTrace (prefixWord ++ tailWord_47517) baseStart_47517 baseEnd_47517 := by
    simpa [prefixWord, tailWord_47517, baseEnd_47517] using wordTrace_append hprefix tailTrace_47517
  have hstable : (prefixWord ++ tailWord_47517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47517).length < 2 ^ (prefixWord ++ tailWord_47517).sum := by decide
  have hdescent : baseEnd_47517 < baseStart_47517 := by decide
  rcases family_descends (prefixWord ++ tailWord_47517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47559 : List Nat := [1, 1, 4, 1, 1, 13]
def baseStart_47559 : Nat := 118140960795 + 47559 * 2 ^ 59
def prefixEnd_47559 : Nat := 4983230072969 + 3 ^ 40 * 47559 * 2
def baseEnd_47559 : Nat := 401985620531434714301

theorem tailTrace_47559 : CollatzResearch.WordTrace tailWord_47559 prefixEnd_47559 401985620531434714301 := by
  unfold tailWord_47559
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734619234709340275649731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1156412823139560183766487 1734619234709340275649731)
  ·
    refine ⟨2601928852064010413474597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1734619234709340275649731 2601928852064010413474597)
    ·
      refine ⟨487861659762001952526487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2601928852064010413474597 487861659762001952526487)
      ·
        refine ⟨731792489643002928789731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487861659762001952526487 731792489643002928789731)
        ·
          refine ⟨1097688734464504393184597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731792489643002928789731 1097688734464504393184597)
          ·
            refine ⟨401985620531434714301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 1097688734464504393184597 401985620531434714301)
            ·
              rfl

theorem cell21_47559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 13].length) (baseStart_47559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47559 prefixEnd_47559 := by exact prefixLift 47559
  have htrace : WordTrace (prefixWord ++ tailWord_47559) baseStart_47559 baseEnd_47559 := by
    simpa [prefixWord, tailWord_47559, baseEnd_47559] using wordTrace_append hprefix tailTrace_47559
  have hstable : (prefixWord ++ tailWord_47559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47559).length < 2 ^ (prefixWord ++ tailWord_47559).sum := by decide
  have hdescent : baseEnd_47559 < baseStart_47559 := by decide
  rcases family_descends (prefixWord ++ tailWord_47559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47562 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_47562 : Nat := 118140960795 + 47562 * 2 ^ 59
def prefixEnd_47562 : Nat := 4983230072969 + 3 ^ 40 * 47562 * 2
def baseEnd_47562 : Nat := 10854296395221398736121

theorem tailTrace_47562 : CollatzResearch.WordTrace tailWord_47562 prefixEnd_47562 10854296395221398736121 := by
  unfold tailWord_47562
  simp only [CollatzResearch.WordTrace]
  refine ⟨433682163424617947002235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1156485769132314525339293 433682163424617947002235)
  ·
    refine ⟨650523245136926920503353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 433682163424617947002235 650523245136926920503353)
    ·
      refine ⟨487892433852695190377515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 650523245136926920503353 487892433852695190377515)
      ·
        refine ⟨731838650779042785566273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487892433852695190377515 731838650779042785566273)
        ·
          refine ⟨548878988084282089174705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731838650779042785566273 548878988084282089174705)
          ·
            refine ⟨411659241063211566881029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548878988084282089174705 411659241063211566881029)
            ·
              refine ⟨77186107699352168790193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 411659241063211566881029 77186107699352168790193)
              ·
                refine ⟨57889580774514126592645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77186107699352168790193 57889580774514126592645)
                ·
                  refine ⟨10854296395221398736121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57889580774514126592645 10854296395221398736121)
                  ·
                    rfl

theorem cell21_47562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_47562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47562 prefixEnd_47562 := by exact prefixLift 47562
  have htrace : WordTrace (prefixWord ++ tailWord_47562) baseStart_47562 baseEnd_47562 := by
    simpa [prefixWord, tailWord_47562, baseEnd_47562] using wordTrace_append hprefix tailTrace_47562
  have hstable : (prefixWord ++ tailWord_47562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47562).length < 2 ^ (prefixWord ++ tailWord_47562).sum := by decide
  have hdescent : baseEnd_47562 < baseStart_47562 := by decide
  rcases family_descends (prefixWord ++ tailWord_47562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47635 : List Nat := [1, 1, 1, 2, 1, 5, 2, 8]
def baseStart_47635 : Nat := 118140960795 + 47635 * 2 ^ 59
def prefixEnd_47635 : Nat := 4983230072969 + 3 ^ 40 * 47635 * 2
def baseEnd_47635 : Nat := 3623651996596498006435

theorem tailTrace_47635 : CollatzResearch.WordTrace tailWord_47635 prefixEnd_47635 3623651996596498006435 := by
  unfold tailWord_47635
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737391182434005255416359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1158260788289336836944239 1737391182434005255416359)
  ·
    refine ⟨2606086773651007883124539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1737391182434005255416359 2606086773651007883124539)
    ·
      refine ⟨3909130160476511824686809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606086773651007883124539 3909130160476511824686809)
      ·
        refine ⟨2931847620357383868515107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3909130160476511824686809 2931847620357383868515107)
        ·
          refine ⟨4397771430536075802772661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2931847620357383868515107 4397771430536075802772661)
          ·
            refine ⟨412291071612757106509937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4397771430536075802772661 412291071612757106509937)
            ·
              refine ⟨309218303709567829882453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412291071612757106509937 309218303709567829882453)
              ·
                refine ⟨3623651996596498006435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 309218303709567829882453 3623651996596498006435)
                ·
                  rfl

theorem cell21_47635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 8].length) (baseStart_47635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47635 prefixEnd_47635 := by exact prefixLift 47635
  have htrace : WordTrace (prefixWord ++ tailWord_47635) baseStart_47635 baseEnd_47635 := by
    simpa [prefixWord, tailWord_47635, baseEnd_47635] using wordTrace_append hprefix tailTrace_47635
  have hstable : (prefixWord ++ tailWord_47635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47635).length < 2 ^ (prefixWord ++ tailWord_47635).sum := by decide
  have hdescent : baseEnd_47635 < baseStart_47635 := by decide
  rcases family_descends (prefixWord ++ tailWord_47635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47666 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_47666 : Nat := 118140960795 + 47666 * 2 ^ 59
def prefixEnd_47666 : Nat := 4983230072969 + 3 ^ 40 * 47666 * 2
def baseEnd_47666 : Nat := 10878030612140329002575

theorem tailTrace_47666 : CollatzResearch.WordTrace tailWord_47666 prefixEnd_47666 10878030612140329002575 := by
  unfold tailWord_47666
  simp only [CollatzResearch.WordTrace]
  refine ⟨434630461330424387448713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1159014563547798366529901 434630461330424387448713)
  ·
    refine ⟨325972845997818290586535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 434630461330424387448713 325972845997818290586535)
    ·
      refine ⟨488959268996727435879803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325972845997818290586535 488959268996727435879803)
      ·
        refine ⟨733438903495091153819705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488959268996727435879803 733438903495091153819705)
        ·
          refine ⟨550079177621318365364779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733438903495091153819705 550079177621318365364779)
          ·
            refine ⟨825118766431977548047169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550079177621318365364779 825118766431977548047169)
            ·
              refine ⟨618839074823983161035377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 825118766431977548047169 618839074823983161035377)
              ·
                refine ⟨464129306117987370776533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 618839074823983161035377 464129306117987370776533)
                ·
                  refine ⟨10878030612140329002575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 464129306117987370776533 10878030612140329002575)
                  ·
                    rfl

theorem cell21_47666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_47666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47666 prefixEnd_47666 := by exact prefixLift 47666
  have htrace : WordTrace (prefixWord ++ tailWord_47666) baseStart_47666 baseEnd_47666 := by
    simpa [prefixWord, tailWord_47666, baseEnd_47666] using wordTrace_append hprefix tailTrace_47666
  have hstable : (prefixWord ++ tailWord_47666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47666).length < 2 ^ (prefixWord ++ tailWord_47666).sum := by decide
  have hdescent : baseEnd_47666 < baseStart_47666 := by decide
  rcases family_descends (prefixWord ++ tailWord_47666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47683 : List Nat := [1, 1, 1, 3, 1, 2, 1, 8, 3]
def baseStart_47683 : Nat := 118140960795 + 47683 * 2 ^ 59
def prefixEnd_47683 : Nat := 4983230072969 + 3 ^ 40 * 47683 * 2
def baseEnd_47683 : Nat := 10881910243752077219207

theorem tailTrace_47683 : CollatzResearch.WordTrace tailWord_47683 prefixEnd_47683 10881910243752077219207 := by
  unfold tailWord_47683
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739141886260109453163703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1159427924173406302109135 1739141886260109453163703)
  ·
    refine ⟨2608712829390164179745555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1739141886260109453163703 2608712829390164179745555)
    ·
      refine ⟨3913069244085246269618333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2608712829390164179745555 3913069244085246269618333)
      ·
        refine ⟨1467400966531967351106875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3913069244085246269618333 1467400966531967351106875)
        ·
          refine ⟨2201101449797951026660313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467400966531967351106875 2201101449797951026660313)
          ·
            refine ⟨1650826087348463269995235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2201101449797951026660313 1650826087348463269995235)
            ·
              refine ⟨2476239131022694904992853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1650826087348463269995235 2476239131022694904992853)
              ·
                refine ⟨29018427316672205917885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2476239131022694904992853 29018427316672205917885)
                ·
                  refine ⟨10881910243752077219207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29018427316672205917885 10881910243752077219207)
                  ·
                    rfl

theorem cell21_47683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 3].length) (baseStart_47683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47683 prefixEnd_47683 := by exact prefixLift 47683
  have htrace : WordTrace (prefixWord ++ tailWord_47683) baseStart_47683 baseEnd_47683 := by
    simpa [prefixWord, tailWord_47683, baseEnd_47683] using wordTrace_append hprefix tailTrace_47683
  have hstable : (prefixWord ++ tailWord_47683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47683).length < 2 ^ (prefixWord ++ tailWord_47683).sum := by decide
  have hdescent : baseEnd_47683 < baseStart_47683 := by decide
  rcases family_descends (prefixWord ++ tailWord_47683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47686 : List Nat := [6, 1, 1, 1, 2, 2, 2, 6]
def baseStart_47686 : Nat := 118140960795 + 47686 * 2 ^ 59
def prefixEnd_47686 : Nat := 4983230072969 + 3 ^ 40 * 47686 * 2
def baseEnd_47686 : Nat := 3627531628208246223067

theorem tailTrace_47686 : CollatzResearch.WordTrace tailWord_47686 prefixEnd_47686 3627531628208246223067 := by
  unfold tailWord_47686
  simp only [CollatzResearch.WordTrace]
  refine ⟨54351603289038780172591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1159500870166160643681941 54351603289038780172591)
  ·
    refine ⟨81527404933558170258887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54351603289038780172591 81527404933558170258887)
    ·
      refine ⟨122291107400337255388331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81527404933558170258887 122291107400337255388331)
      ·
        refine ⟨183436661100505883082497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122291107400337255388331 183436661100505883082497)
        ·
          refine ⟨137577495825379412311873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183436661100505883082497 137577495825379412311873)
          ·
            refine ⟨103183121869034559233905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137577495825379412311873 103183121869034559233905)
            ·
              refine ⟨77387341401775919425429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103183121869034559233905 77387341401775919425429)
              ·
                refine ⟨3627531628208246223067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77387341401775919425429 3627531628208246223067)
                ·
                  rfl

theorem cell21_47686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_47686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47686 prefixEnd_47686 := by exact prefixLift 47686
  have htrace : WordTrace (prefixWord ++ tailWord_47686) baseStart_47686 baseEnd_47686 := by
    simpa [prefixWord, tailWord_47686, baseEnd_47686] using wordTrace_append hprefix tailTrace_47686
  have hstable : (prefixWord ++ tailWord_47686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47686).length < 2 ^ (prefixWord ++ tailWord_47686).sum := by decide
  have hdescent : baseEnd_47686 < baseStart_47686 := by decide
  rcases family_descends (prefixWord ++ tailWord_47686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47728 : List Nat := [2, 1, 1, 1, 8, 8]
def baseStart_47728 : Nat := 118140960795 + 47728 * 2 ^ 59
def prefixEnd_47728 : Nat := 4983230072969 + 3 ^ 40 * 47728 * 2
def baseEnd_47728 : Nat := 403414068771925887745

theorem tailTrace_47728 : CollatzResearch.WordTrace tailWord_47728 prefixEnd_47728 403414068771925887745 := by
  unfold tailWord_47728
  simp only [CollatzResearch.WordTrace]
  refine ⟨870391585548541069275919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1160522114064721425701225 870391585548541069275919)
  ·
    refine ⟨1305587378322811603913879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 870391585548541069275919 1305587378322811603913879)
    ·
      refine ⟨1958381067484217405870819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1305587378322811603913879 1958381067484217405870819)
      ·
        refine ⟨2937571601226326108806229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958381067484217405870819 2937571601226326108806229)
        ·
          refine ⟨34424667201871009087573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 2937571601226326108806229 34424667201871009087573)
          ·
            refine ⟨403414068771925887745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 34424667201871009087573 403414068771925887745)
            ·
              rfl

theorem cell21_47728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 8].length) (baseStart_47728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47728 prefixEnd_47728 := by exact prefixLift 47728
  have htrace : WordTrace (prefixWord ++ tailWord_47728) baseStart_47728 baseEnd_47728 := by
    simpa [prefixWord, tailWord_47728, baseEnd_47728] using wordTrace_append hprefix tailTrace_47728
  have hstable : (prefixWord ++ tailWord_47728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47728).length < 2 ^ (prefixWord ++ tailWord_47728).sum := by decide
  have hdescent : baseEnd_47728 < baseStart_47728 := by decide
  rcases family_descends (prefixWord ++ tailWord_47728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47866 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_47866 : Nat := 118140960795 + 47866 * 2 ^ 59
def prefixEnd_47866 : Nat := 4983230072969 + 3 ^ 40 * 47866 * 2
def baseEnd_47866 : Nat := 10923673336984425668833

theorem tailTrace_47866 : CollatzResearch.WordTrace tailWord_47866 prefixEnd_47866 10923673336984425668833 := by
  unfold tailWord_47866
  simp only [CollatzResearch.WordTrace]
  refine ⟨436454111149282926768863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1163877629731421138050301 436454111149282926768863)
  ·
    refine ⟨654681166723924390153295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 436454111149282926768863 654681166723924390153295)
    ·
      refine ⟨982021750085886585229943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 654681166723924390153295 982021750085886585229943)
      ·
        refine ⟨1473032625128829877844915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982021750085886585229943 1473032625128829877844915)
        ·
          refine ⟨2209548937693244816767373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473032625128829877844915 2209548937693244816767373)
          ·
            refine ⟨828580851634966806287765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2209548937693244816767373 828580851634966806287765)
            ·
              refine ⟨38839727420389069044739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 828580851634966806287765 38839727420389069044739)
              ·
                refine ⟨58259591130583603567109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38839727420389069044739 58259591130583603567109)
                ·
                  refine ⟨10923673336984425668833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58259591130583603567109 10923673336984425668833)
                  ·
                    rfl

theorem cell21_47866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_47866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47866 prefixEnd_47866 := by exact prefixLift 47866
  have htrace : WordTrace (prefixWord ++ tailWord_47866) baseStart_47866 baseEnd_47866 := by
    simpa [prefixWord, tailWord_47866, baseEnd_47866] using wordTrace_append hprefix tailTrace_47866
  have hstable : (prefixWord ++ tailWord_47866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47866).length < 2 ^ (prefixWord ++ tailWord_47866).sum := by decide
  have hdescent : baseEnd_47866 < baseStart_47866 := by decide
  rcases family_descends (prefixWord ++ tailWord_47866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47914 : List Nat := [3, 1, 4, 3, 1, 2, 1, 6]
def baseStart_47914 : Nat := 118140960795 + 47914 * 2 ^ 59
def prefixEnd_47914 : Nat := 4983230072969 + 3 ^ 40 * 47914 * 2
def baseEnd_47914 : Nat := 3644875863649002956245

theorem tailTrace_47914 : CollatzResearch.WordTrace tailWord_47914 prefixEnd_47914 3644875863649002956245 := by
  unfold tailWord_47914
  simp only [CollatzResearch.WordTrace]
  refine ⟨436891787105808976205699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1165044765615490603215197 436891787105808976205699)
  ·
    refine ⟨655337680658713464308549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 436891787105808976205699 655337680658713464308549)
    ·
      refine ⟨122875815123508774557853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 655337680658713464308549 122875815123508774557853)
      ·
        refine ⟨46078430671315790459195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122875815123508774557853 46078430671315790459195)
        ·
          refine ⟨69117646006973685688793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46078430671315790459195 69117646006973685688793)
          ·
            refine ⟨51838234505230264266595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69117646006973685688793 51838234505230264266595)
            ·
              refine ⟨77757351757845396399893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51838234505230264266595 77757351757845396399893)
              ·
                refine ⟨3644875863649002956245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77757351757845396399893 3644875863649002956245)
                ·
                  rfl

theorem cell21_47914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_47914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47914 prefixEnd_47914 := by exact prefixLift 47914
  have htrace : WordTrace (prefixWord ++ tailWord_47914) baseStart_47914 baseEnd_47914 := by
    simpa [prefixWord, tailWord_47914, baseEnd_47914] using wordTrace_append hprefix tailTrace_47914
  have hstable : (prefixWord ++ tailWord_47914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47914).length < 2 ^ (prefixWord ++ tailWord_47914).sum := by decide
  have hdescent : baseEnd_47914 < baseStart_47914 := by decide
  rcases family_descends (prefixWord ++ tailWord_47914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47956 : List Nat := [2, 4, 1, 1, 4, 1, 8]
def baseStart_47956 : Nat := 118140960795 + 47956 * 2 ^ 59
def prefixEnd_47956 : Nat := 4983230072969 + 3 ^ 40 * 47956 * 2
def baseEnd_47956 : Nat := 1216023618129363240961

theorem tailTrace_47956 : CollatzResearch.WordTrace tailWord_47956 prefixEnd_47956 1216023618129363240961 := by
  unfold tailWord_47956
  simp only [CollatzResearch.WordTrace]
  refine ⟨874549507135538538925861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1166066009514051385234481 874549507135538538925861)
  ·
    refine ⟨163978032587913476048599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 874549507135538538925861 163978032587913476048599)
    ·
      refine ⟨245967048881870214072899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163978032587913476048599 245967048881870214072899)
      ·
        refine ⟨368950573322805321109349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245967048881870214072899 368950573322805321109349)
        ·
          refine ⟨69178232498025997708003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 368950573322805321109349 69178232498025997708003)
          ·
            refine ⟨103767348747038996562005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69178232498025997708003 103767348747038996562005)
            ·
              refine ⟨1216023618129363240961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 103767348747038996562005 1216023618129363240961)
              ·
                rfl

theorem cell21_47956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 8].length) (baseStart_47956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47956 prefixEnd_47956 := by exact prefixLift 47956
  have htrace : WordTrace (prefixWord ++ tailWord_47956) baseStart_47956 baseEnd_47956 := by
    simpa [prefixWord, tailWord_47956, baseEnd_47956] using wordTrace_append hprefix tailTrace_47956
  have hstable : (prefixWord ++ tailWord_47956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47956).length < 2 ^ (prefixWord ++ tailWord_47956).sum := by decide
  have hdescent : baseEnd_47956 < baseStart_47956 := by decide
  rcases family_descends (prefixWord ++ tailWord_47956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47990 : List Nat := [5, 1, 1, 3, 1, 3, 2, 5]
def baseStart_47990 : Nat := 118140960795 + 47990 * 2 ^ 59
def prefixEnd_47990 : Nat := 4983230072969 + 3 ^ 40 * 47990 * 2
def baseEnd_47990 : Nat := 3650657275462588533971

theorem tailTrace_47990 : CollatzResearch.WordTrace tailWord_47990 prefixEnd_47990 3650657275462588533971 := by
  unfold tailWord_47990
  simp only [CollatzResearch.WordTrace]
  refine ⟨109396193509243805286839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1166892730765267256392949 109396193509243805286839)
  ·
    refine ⟨164094290263865707930259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109396193509243805286839 164094290263865707930259)
    ·
      refine ⟨246141435395798561895389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164094290263865707930259 246141435395798561895389)
      ·
        refine ⟨92303038273424460710771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246141435395798561895389 92303038273424460710771)
        ·
          refine ⟨138454557410136691066157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92303038273424460710771 138454557410136691066157)
          ·
            refine ⟨51920459028801259149809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138454557410136691066157 51920459028801259149809)
            ·
              refine ⟨38940344271600944362357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51920459028801259149809 38940344271600944362357)
              ·
                refine ⟨3650657275462588533971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38940344271600944362357 3650657275462588533971)
                ·
                  rfl

theorem cell21_47990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_47990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_47990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_47990 prefixEnd_47990 := by exact prefixLift 47990
  have htrace : WordTrace (prefixWord ++ tailWord_47990) baseStart_47990 baseEnd_47990 := by
    simpa [prefixWord, tailWord_47990, baseEnd_47990] using wordTrace_append hprefix tailTrace_47990
  have hstable : (prefixWord ++ tailWord_47990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47990).length < 2 ^ (prefixWord ++ tailWord_47990).sum := by decide
  have hdescent : baseEnd_47990 < baseStart_47990 := by decide
  rcases family_descends (prefixWord ++ tailWord_47990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48139 : List Nat := [1, 1, 1, 1, 6, 2, 2, 4, 3]
def baseStart_48139 : Nat := 118140960795 + 48139 * 2 ^ 59
def prefixEnd_48139 : Nat := 4983230072969 + 3 ^ 40 * 48139 * 2
def baseEnd_48139 : Nat := 10985975656396617618275

theorem tailTrace_48139 : CollatzResearch.WordTrace tailWord_48139 prefixEnd_48139 10985975656396617618275 := by
  unfold tailWord_48139
  simp only [CollatzResearch.WordTrace]
  refine ⟨1755773572608099331763471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1170515715072066221175647 1755773572608099331763471)
  ·
    refine ⟨2633660358912148997645207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1755773572608099331763471 2633660358912148997645207)
    ·
      refine ⟨3950490538368223496467811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2633660358912148997645207 3950490538368223496467811)
      ·
        refine ⟨5925735807552335244701717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3950490538368223496467811 5925735807552335244701717)
        ·
          refine ⟨277768865979015714595393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5925735807552335244701717 277768865979015714595393)
          ·
            refine ⟨208326649484261785946545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277768865979015714595393 208326649484261785946545)
            ·
              refine ⟨156244987113196339459909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208326649484261785946545 156244987113196339459909)
              ·
                refine ⟨29295935083724313648733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156244987113196339459909 29295935083724313648733)
                ·
                  refine ⟨10985975656396617618275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29295935083724313648733 10985975656396617618275)
                  ·
                    rfl

theorem cell21_48139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 3].length) (baseStart_48139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48139 prefixEnd_48139 := by exact prefixLift 48139
  have htrace : WordTrace (prefixWord ++ tailWord_48139) baseStart_48139 baseEnd_48139 := by
    simpa [prefixWord, tailWord_48139, baseEnd_48139] using wordTrace_append hprefix tailTrace_48139
  have hstable : (prefixWord ++ tailWord_48139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48139).length < 2 ^ (prefixWord ++ tailWord_48139).sum := by decide
  have hdescent : baseEnd_48139 < baseStart_48139 := by decide
  rcases family_descends (prefixWord ++ tailWord_48139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48246 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_48246 : Nat := 118140960795 + 48246 * 2 ^ 59
def prefixEnd_48246 : Nat := 4983230072969 + 3 ^ 40 * 48246 * 2
def baseEnd_48246 : Nat := 11010394514188209334723

theorem tailTrace_48246 : CollatzResearch.WordTrace tailWord_48246 prefixEnd_48246 11010394514188209334723 := by
  unfold tailWord_48246
  simp only [CollatzResearch.WordTrace]
  refine ⟨109979761451278537869287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1173117455480304403939061 109979761451278537869287)
  ·
    refine ⟨164969642176917806803931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109979761451278537869287 164969642176917806803931)
    ·
      refine ⟨247454463265376710205897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164969642176917806803931 247454463265376710205897)
      ·
        refine ⟨185590847449032532654423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247454463265376710205897 185590847449032532654423)
        ·
          refine ⟨278386271173548798981635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185590847449032532654423 278386271173548798981635)
          ·
            refine ⟨417579406760323198472453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278386271173548798981635 417579406760323198472453)
            ·
              refine ⟨78296138767560599713585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 417579406760323198472453 78296138767560599713585)
              ·
                refine ⟨58722104075670449785189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78296138767560599713585 58722104075670449785189)
                ·
                  refine ⟨11010394514188209334723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58722104075670449785189 11010394514188209334723)
                  ·
                    rfl

theorem cell21_48246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_48246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48246 prefixEnd_48246 := by exact prefixLift 48246
  have htrace : WordTrace (prefixWord ++ tailWord_48246) baseStart_48246 baseEnd_48246 := by
    simpa [prefixWord, tailWord_48246, baseEnd_48246] using wordTrace_append hprefix tailTrace_48246
  have hstable : (prefixWord ++ tailWord_48246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48246).length < 2 ^ (prefixWord ++ tailWord_48246).sum := by decide
  have hdescent : baseEnd_48246 < baseStart_48246 := by decide
  rcases family_descends (prefixWord ++ tailWord_48246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48249 : List Nat := [1, 2, 1, 3, 5, 2, 2, 2, 3]
def baseStart_48249 : Nat := 118140960795 + 48249 * 2 ^ 59
def prefixEnd_48249 : Nat := 4983230072969 + 3 ^ 40 * 48249 * 2
def baseEnd_48249 : Nat := 11011079155060870784717

theorem tailTrace_48249 : CollatzResearch.WordTrace tailWord_48249 prefixEnd_48249 11011079155060870784717 := by
  unfold tailWord_48249
  simp only [CollatzResearch.WordTrace]
  refine ⟨1759785602209588118267801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1173190401473058745511867 1759785602209588118267801)
  ·
    refine ⟨1319839201657191088700851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1759785602209588118267801 1319839201657191088700851)
    ·
      refine ⟨1979758802485786633051277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1319839201657191088700851 1979758802485786633051277)
      ·
        refine ⟨742409550932169987394229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1979758802485786633051277 742409550932169987394229)
        ·
          refine ⟨69600895399890936318209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 742409550932169987394229 69600895399890936318209)
          ·
            refine ⟨52200671549918202238657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69600895399890936318209 52200671549918202238657)
            ·
              refine ⟨39150503662438651678993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52200671549918202238657 39150503662438651678993)
              ·
                refine ⟨29362877746828988759245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39150503662438651678993 29362877746828988759245)
                ·
                  refine ⟨11011079155060870784717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29362877746828988759245 11011079155060870784717)
                  ·
                    rfl

theorem cell21_48249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 3].length) (baseStart_48249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48249 prefixEnd_48249 := by exact prefixLift 48249
  have htrace : WordTrace (prefixWord ++ tailWord_48249) baseStart_48249 baseEnd_48249 := by
    simpa [prefixWord, tailWord_48249, baseEnd_48249] using wordTrace_append hprefix tailTrace_48249
  have hstable : (prefixWord ++ tailWord_48249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48249).length < 2 ^ (prefixWord ++ tailWord_48249).sum := by decide
  have hdescent : baseEnd_48249 < baseStart_48249 := by decide
  rcases family_descends (prefixWord ++ tailWord_48249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48260 : List Nat := [2, 3, 2, 1, 2, 4, 1, 6]
def baseStart_48260 : Nat := 118140960795 + 48260 * 2 ^ 59
def prefixEnd_48260 : Nat := 4983230072969 + 3 ^ 40 * 48260 * 2
def baseEnd_48260 : Nat := 3671196501642432033787

theorem tailTrace_48260 : CollatzResearch.WordTrace tailWord_48260 prefixEnd_48260 3671196501642432033787 := by
  unfold tailWord_48260
  simp only [CollatzResearch.WordTrace]
  refine ⟨880093402584868498459117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1173457870113157997945489 880093402584868498459117)
  ·
    refine ⟨330035025969325686922169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 880093402584868498459117 330035025969325686922169)
    ·
      refine ⟨247526269476994265191627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330035025969325686922169 247526269476994265191627)
      ·
        refine ⟨371289404215491397787441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247526269476994265191627 371289404215491397787441)
        ·
          refine ⟨278467053161618548340581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371289404215491397787441 278467053161618548340581)
          ·
            refine ⟨52212572467803477813859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278467053161618548340581 52212572467803477813859)
            ·
              refine ⟨78318858701705216720789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52212572467803477813859 78318858701705216720789)
              ·
                refine ⟨3671196501642432033787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78318858701705216720789 3671196501642432033787)
                ·
                  rfl

theorem cell21_48260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_48260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48260 prefixEnd_48260 := by exact prefixLift 48260
  have htrace : WordTrace (prefixWord ++ tailWord_48260) baseStart_48260 baseEnd_48260 := by
    simpa [prefixWord, tailWord_48260, baseEnd_48260] using wordTrace_append hprefix tailTrace_48260
  have hstable : (prefixWord ++ tailWord_48260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48260).length < 2 ^ (prefixWord ++ tailWord_48260).sum := by decide
  have hdescent : baseEnd_48260 < baseStart_48260 := by decide
  rcases family_descends (prefixWord ++ tailWord_48260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48274 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_48274 : Nat := 118140960795 + 48274 * 2 ^ 59
def prefixEnd_48274 : Nat := 4983230072969 + 3 ^ 40 * 48274 * 2
def baseEnd_48274 : Nat := 11016784495666382867999

theorem tailTrace_48274 : CollatzResearch.WordTrace tailWord_48274 prefixEnd_48274 11016784495666382867999 := by
  unfold tailWord_48274
  simp only [CollatzResearch.WordTrace]
  refine ⟨440174356779754346981969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1173798284746011591951917 440174356779754346981969)
  ·
    refine ⟨330130767584815760236477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 440174356779754346981969 330130767584815760236477)
    ·
      refine ⟨123799037844305910088679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330130767584815760236477 123799037844305910088679)
      ·
        refine ⟨185698556766458865133019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123799037844305910088679 185698556766458865133019)
        ·
          refine ⟨278547835149688297699529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185698556766458865133019 278547835149688297699529)
          ·
            refine ⟨208910876362266223274647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278547835149688297699529 208910876362266223274647)
            ·
              refine ⟨313366314543399334911971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208910876362266223274647 313366314543399334911971)
              ·
                refine ⟨470049471815099002367957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313366314543399334911971 470049471815099002367957)
                ·
                  refine ⟨11016784495666382867999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 470049471815099002367957 11016784495666382867999)
                  ·
                    rfl

theorem cell21_48274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_48274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48274 prefixEnd_48274 := by exact prefixLift 48274
  have htrace : WordTrace (prefixWord ++ tailWord_48274) baseStart_48274 baseEnd_48274 := by
    simpa [prefixWord, tailWord_48274, baseEnd_48274] using wordTrace_append hprefix tailTrace_48274
  have hstable : (prefixWord ++ tailWord_48274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48274).length < 2 ^ (prefixWord ++ tailWord_48274).sum := by decide
  have hdescent : baseEnd_48274 < baseStart_48274 := by decide
  rcases family_descends (prefixWord ++ tailWord_48274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48288 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_48288 : Nat := 118140960795 + 48288 * 2 ^ 59
def prefixEnd_48288 : Nat := 4983230072969 + 3 ^ 40 * 48288 * 2
def baseEnd_48288 : Nat := 11019979486405469634637

theorem tailTrace_48288 : CollatzResearch.WordTrace tailWord_48288 prefixEnd_48288 11019979486405469634637 := by
  unfold tailWord_48288
  simp only [CollatzResearch.WordTrace]
  refine ⟨880604024534148889468759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1174138699378865185958345 880604024534148889468759)
  ·
    refine ⟨1320906036801223334203139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 880604024534148889468759 1320906036801223334203139)
    ·
      refine ⟨1981359055201835001304709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1320906036801223334203139 1981359055201835001304709)
      ·
        refine ⟨371504822850344062744633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1981359055201835001304709 371504822850344062744633)
        ·
          refine ⟨278628617137758047058475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371504822850344062744633 278628617137758047058475)
          ·
            refine ⟨417942925706637070587713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278628617137758047058475 417942925706637070587713)
            ·
              refine ⟨313457194279977802940785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417942925706637070587713 313457194279977802940785)
              ·
                refine ⟨235092895709983352205589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313457194279977802940785 235092895709983352205589)
                ·
                  refine ⟨11019979486405469634637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 235092895709983352205589 11019979486405469634637)
                  ·
                    rfl

theorem cell21_48288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_48288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48288 prefixEnd_48288 := by exact prefixLift 48288
  have htrace : WordTrace (prefixWord ++ tailWord_48288) baseStart_48288 baseEnd_48288 := by
    simpa [prefixWord, tailWord_48288, baseEnd_48288] using wordTrace_append hprefix tailTrace_48288
  have hstable : (prefixWord ++ tailWord_48288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48288).length < 2 ^ (prefixWord ++ tailWord_48288).sum := by decide
  have hdescent : baseEnd_48288 < baseStart_48288 := by decide
  rcases family_descends (prefixWord ++ tailWord_48288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48305 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 6]
def baseStart_48305 : Nat := 118140960795 + 48305 * 2 ^ 59
def prefixEnd_48305 : Nat := 4983230072969 + 3 ^ 40 * 48305 * 2
def baseEnd_48305 : Nat := 11023859118017217851269

theorem tailTrace_48305 : CollatzResearch.WordTrace tailWord_48305 prefixEnd_48305 11023859118017217851269 := by
  unfold tailWord_48305
  simp only [CollatzResearch.WordTrace]
  refine ⟨1761828090006709682306369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1174552060004473121537579 1761828090006709682306369)
  ·
    refine ⟨1321371067505032261729777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1761828090006709682306369 1321371067505032261729777)
    ·
      refine ⟨991028300628774196297333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1321371067505032261729777 991028300628774196297333)
      ·
        refine ⟨92908903183947580902875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 991028300628774196297333 92908903183947580902875)
        ·
          refine ⟨139363354775921371354313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92908903183947580902875 139363354775921371354313)
          ·
            refine ⟨104522516081941028515735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139363354775921371354313 104522516081941028515735)
            ·
              refine ⟨156783774122911542773603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104522516081941028515735 156783774122911542773603)
              ·
                refine ⟨235175661184367314160405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156783774122911542773603 235175661184367314160405)
                ·
                  refine ⟨11023859118017217851269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 235175661184367314160405 11023859118017217851269)
                  ·
                    rfl

theorem cell21_48305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_48305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48305 prefixEnd_48305 := by exact prefixLift 48305
  have htrace : WordTrace (prefixWord ++ tailWord_48305) baseStart_48305 baseEnd_48305 := by
    simpa [prefixWord, tailWord_48305, baseEnd_48305] using wordTrace_append hprefix tailTrace_48305
  have hstable : (prefixWord ++ tailWord_48305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48305).length < 2 ^ (prefixWord ++ tailWord_48305).sum := by decide
  have hdescent : baseEnd_48305 < baseStart_48305 := by decide
  rcases family_descends (prefixWord ++ tailWord_48305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48342 : List Nat := [5, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_48342 : Nat := 118140960795 + 48342 * 2 ^ 59
def prefixEnd_48342 : Nat := 4983230072969 + 3 ^ 40 * 48342 * 2
def baseEnd_48342 : Nat := 11032303022113375734527

theorem tailTrace_48342 : CollatzResearch.WordTrace tailWord_48342 prefixEnd_48342 11032303022113375734527 := by
  unfold tailWord_48342
  simp only [CollatzResearch.WordTrace]
  refine ⟨110198599429541562587705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1175451727248443334268853 110198599429541562587705)
  ·
    refine ⟨82648949572156171940779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110198599429541562587705 82648949572156171940779)
    ·
      refine ⟨123973424358234257911169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82648949572156171940779 123973424358234257911169)
      ·
        refine ⟨92980068268675693433377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123973424358234257911169 92980068268675693433377)
        ·
          refine ⟨69735051201506770075033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92980068268675693433377 69735051201506770075033)
          ·
            refine ⟨52301288401130077556275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69735051201506770075033 52301288401130077556275)
            ·
              refine ⟨78451932601695116334413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52301288401130077556275 78451932601695116334413)
              ·
                refine ⟨29419474725635668625405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78451932601695116334413 29419474725635668625405)
                ·
                  refine ⟨11032303022113375734527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29419474725635668625405 11032303022113375734527)
                  ·
                    rfl

theorem cell21_48342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_48342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48342 prefixEnd_48342 := by exact prefixLift 48342
  have htrace : WordTrace (prefixWord ++ tailWord_48342) baseStart_48342 baseEnd_48342 := by
    simpa [prefixWord, tailWord_48342, baseEnd_48342] using wordTrace_append hprefix tailTrace_48342
  have hstable : (prefixWord ++ tailWord_48342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48342).length < 2 ^ (prefixWord ++ tailWord_48342).sum := by decide
  have hdescent : baseEnd_48342 < baseStart_48342 := by decide
  rcases family_descends (prefixWord ++ tailWord_48342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48364 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_48364 : Nat := 118140960795 + 48364 * 2 ^ 59
def prefixEnd_48364 : Nat := 4983230072969 + 3 ^ 40 * 48364 * 2
def baseEnd_48364 : Nat := 11037323721846226367815

theorem tailTrace_48364 : CollatzResearch.WordTrace tailWord_48364 prefixEnd_48364 11037323721846226367815 := by
  unfold tailWord_48364
  simp only [CollatzResearch.WordTrace]
  refine ⟨881989998396481379352073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1175986664528641839136097 881989998396481379352073)
  ·
    refine ⟨661492498797361034514055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 881989998396481379352073 661492498797361034514055)
    ·
      refine ⟨992238748196041551771083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661492498797361034514055 992238748196041551771083)
      ·
        refine ⟨1488358122294062327656625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992238748196041551771083 1488358122294062327656625)
        ·
          refine ⟨1116268591720546745742469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1488358122294062327656625 1116268591720546745742469)
          ·
            refine ⟨209300360947602514826713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1116268591720546745742469 209300360947602514826713)
            ·
              refine ⟨156975270710701886120035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209300360947602514826713 156975270710701886120035)
              ·
                refine ⟨235462906066052829180053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156975270710701886120035 235462906066052829180053)
                ·
                  refine ⟨11037323721846226367815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 235462906066052829180053 11037323721846226367815)
                  ·
                    rfl

theorem cell21_48364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_48364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_48364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_48364 prefixEnd_48364 := by exact prefixLift 48364
  have htrace : WordTrace (prefixWord ++ tailWord_48364) baseStart_48364 baseEnd_48364 := by
    simpa [prefixWord, tailWord_48364, baseEnd_48364] using wordTrace_append hprefix tailTrace_48364
  have hstable : (prefixWord ++ tailWord_48364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48364).length < 2 ^ (prefixWord ++ tailWord_48364).sum := by decide
  have hdescent : baseEnd_48364 < baseStart_48364 := by decide
  rcases family_descends (prefixWord ++ tailWord_48364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
