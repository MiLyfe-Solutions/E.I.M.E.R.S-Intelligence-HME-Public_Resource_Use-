import V185TrunkScan22Chunk035

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_322894 : List Nat := [4, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_322894 : Nat := 118140960795 + 322894 * 2 ^ 59
def prefixEnd_322894 : Nat := 4983230072969 + 3 ^ 40 * 322894 * 2
def baseEnd_322894 : Nat := 36844404989547757653343

theorem tailTrace_322894 : CollatzResearch.WordTrace tailWord_322894 prefixEnd_322894 36844404989547757653343 := by
  unfold tailWord_322894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472113961527207343739967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7851274461478439166613157 1472113961527207343739967)
  ·
    refine ⟨2208170942290811015609951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1472113961527207343739967 2208170942290811015609951)
    ·
      refine ⟨3312256413436216523414927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2208170942290811015609951 3312256413436216523414927)
      ·
        refine ⟨4968384620154324785122391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3312256413436216523414927 4968384620154324785122391)
        ·
          refine ⟨7452576930231487177683587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4968384620154324785122391 7452576930231487177683587)
          ·
            refine ⟨11178865395347230766525381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7452576930231487177683587 11178865395347230766525381)
            ·
              refine ⟨2096037261627605768723509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11178865395347230766525381 2096037261627605768723509)
              ·
                refine ⟨196503493277588040817829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2096037261627605768723509 196503493277588040817829)
                ·
                  refine ⟨36844404989547757653343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196503493277588040817829 36844404989547757653343)
                  ·
                    rfl

theorem cell22_322894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_322894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_322894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_322894 prefixEnd_322894 := by exact prefixLift 322894
  have htrace : WordTrace (prefixWord ++ tailWord_322894) baseStart_322894 baseEnd_322894 := by
    simpa [prefixWord, tailWord_322894, baseEnd_322894] using wordTrace_append hprefix tailTrace_322894
  have hstable : (prefixWord ++ tailWord_322894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322894).length < 2 ^ (prefixWord ++ tailWord_322894).sum := by decide
  have hdescent : baseEnd_322894 < baseStart_322894 := by decide
  rcases family_descends (prefixWord ++ tailWord_322894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323061 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_323061 : Nat := 118140960795 + 323061 * 2 ^ 59
def prefixEnd_323061 : Nat := 4983230072969 + 3 ^ 40 * 323061 * 2
def baseEnd_323061 : Nat := 110590382481510504034517

theorem tailTrace_323061 : CollatzResearch.WordTrace tailWord_323061 prefixEnd_323061 110590382481510504034517 := by
  unfold tailWord_323061
  simp only [CollatzResearch.WordTrace]
  refine ⟨11783002682612646271249037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7855335121741764180832691 11783002682612646271249037)
  ·
    refine ⟨4418626005979742351718389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11783002682612646271249037 4418626005979742351718389)
    ·
      refine ⟨414246188060600845473599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4418626005979742351718389 414246188060600845473599)
      ·
        refine ⟨621369282090901268210399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414246188060600845473599 621369282090901268210399)
        ·
          refine ⟨932053923136351902315599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621369282090901268210399 932053923136351902315599)
          ·
            refine ⟨1398080884704527853473399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932053923136351902315599 1398080884704527853473399)
            ·
              refine ⟨2097121327056791780210099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398080884704527853473399 2097121327056791780210099)
              ·
                refine ⟨3145681990585187670315149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097121327056791780210099 3145681990585187670315149)
                ·
                  refine ⟨1179630746469445376368181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3145681990585187670315149 1179630746469445376368181)
                  ·
                    refine ⟨110590382481510504034517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1179630746469445376368181 110590382481510504034517)
                    ·
                      rfl

theorem cell22_323061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_323061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323061 prefixEnd_323061 := by exact prefixLift 323061
  have htrace : WordTrace (prefixWord ++ tailWord_323061) baseStart_323061 baseEnd_323061 := by
    simpa [prefixWord, tailWord_323061, baseEnd_323061] using wordTrace_append hprefix tailTrace_323061
  have hstable : (prefixWord ++ tailWord_323061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323061).length < 2 ^ (prefixWord ++ tailWord_323061).sum := by decide
  have hdescent : baseEnd_323061 < baseStart_323061 := by decide
  rcases family_descends (prefixWord ++ tailWord_323061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323106 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_323106 : Nat := 118140960795 + 323106 * 2 ^ 59
def prefixEnd_323106 : Nat := 4983230072969 + 3 ^ 40 * 323106 * 2
def baseEnd_323106 : Nat := 110605786901145386659379

theorem tailTrace_323106 : CollatzResearch.WordTrace tailWord_323106 prefixEnd_323106 110605786901145386659379 := by
  unfold tailWord_323106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2946160991862404739159293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7856429311633079304424781 2946160991862404739159293)
  ·
    refine ⟨1104810371948401777184735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2946160991862404739159293 1104810371948401777184735)
    ·
      refine ⟨1657215557922602665777103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1104810371948401777184735 1657215557922602665777103)
      ·
        refine ⟨2485823336883903998665655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1657215557922602665777103 2485823336883903998665655)
        ·
          refine ⟨3728735005325855997998483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485823336883903998665655 3728735005325855997998483)
          ·
            refine ⟨5593102507988783996997725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728735005325855997998483 5593102507988783996997725)
            ·
              refine ⟨2097413440495793998874147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5593102507988783996997725 2097413440495793998874147)
              ·
                refine ⟨3146120160743690998311221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097413440495793998874147 3146120160743690998311221)
                ·
                  refine ⟨294948765069721031091677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3146120160743690998311221 294948765069721031091677)
                  ·
                    refine ⟨110605786901145386659379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 294948765069721031091677 110605786901145386659379)
                    ·
                      rfl

theorem cell22_323106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_323106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323106 prefixEnd_323106 := by exact prefixLift 323106
  have htrace : WordTrace (prefixWord ++ tailWord_323106) baseStart_323106 baseEnd_323106 := by
    simpa [prefixWord, tailWord_323106, baseEnd_323106] using wordTrace_append hprefix tailTrace_323106
  have hstable : (prefixWord ++ tailWord_323106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323106).length < 2 ^ (prefixWord ++ tailWord_323106).sum := by decide
  have hdescent : baseEnd_323106 < baseStart_323106 := by decide
  rcases family_descends (prefixWord ++ tailWord_323106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323123 : List Nat := [1, 1, 1, 2, 4, 3, 1, 5, 1, 3]
def baseStart_323123 : Nat := 118140960795 + 323123 * 2 ^ 59
def prefixEnd_323123 : Nat := 4983230072969 + 3 ^ 40 * 323123 * 2
def baseEnd_323123 : Nat := 110611606348563008984327

theorem tailTrace_323123 : CollatzResearch.WordTrace tailWord_323123 prefixEnd_323123 110611606348563008984327 := by
  unfold tailWord_323123
  simp only [CollatzResearch.WordTrace]
  refine ⟨11785264008388030860006023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7856842672258687240004015 11785264008388030860006023)
  ·
    refine ⟨17677896012582046290009035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11785264008388030860006023 17677896012582046290009035)
    ·
      refine ⟨26516844018873069435013553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17677896012582046290009035 26516844018873069435013553)
      ·
        refine ⟨19887633014154802076260165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26516844018873069435013553 19887633014154802076260165)
        ·
          refine ⟨3728931190154025389298781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19887633014154802076260165 3728931190154025389298781)
          ·
            refine ⟨1398349196307759520987043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3728931190154025389298781 1398349196307759520987043)
            ·
              refine ⟨2097523794461639281480565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398349196307759520987043 2097523794461639281480565)
              ·
                refine ⟨196642855730778682638803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2097523794461639281480565 196642855730778682638803)
                ·
                  refine ⟨294964283596168023958205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196642855730778682638803 294964283596168023958205)
                  ·
                    refine ⟨110611606348563008984327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 294964283596168023958205 110611606348563008984327)
                    ·
                      rfl

theorem cell22_323123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 1, 3].length) (baseStart_323123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323123 prefixEnd_323123 := by exact prefixLift 323123
  have htrace : WordTrace (prefixWord ++ tailWord_323123) baseStart_323123 baseEnd_323123 := by
    simpa [prefixWord, tailWord_323123, baseEnd_323123] using wordTrace_append hprefix tailTrace_323123
  have hstable : (prefixWord ++ tailWord_323123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323123).length < 2 ^ (prefixWord ++ tailWord_323123).sum := by decide
  have hdescent : baseEnd_323123 < baseStart_323123 := by decide
  rcases family_descends (prefixWord ++ tailWord_323123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323194 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_323194 : Nat := 118140960795 + 323194 * 2 ^ 59
def prefixEnd_323194 : Nat := 4983230072969 + 3 ^ 40 * 323194 * 2
def baseEnd_323194 : Nat := 110635911099542490459109

theorem tailTrace_323194 : CollatzResearch.WordTrace tailWord_323194 prefixEnd_323194 110635911099542490459109 := by
  unfold tailWord_323194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2946963397782702496460159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7858569060753873323893757 2946963397782702496460159)
  ·
    refine ⟨4420445096674053744690239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2946963397782702496460159 4420445096674053744690239)
    ·
      refine ⟨6630667645011080617035359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4420445096674053744690239 6630667645011080617035359)
      ·
        refine ⟨9946001467516620925553039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6630667645011080617035359 9946001467516620925553039)
        ·
          refine ⟨14919002201274931388329559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9946001467516620925553039 14919002201274931388329559)
          ·
            refine ⟨22378503301912397082494339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14919002201274931388329559 22378503301912397082494339)
            ·
              refine ⟨33567754952868595623741509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22378503301912397082494339 33567754952868595623741509)
              ·
                refine ⟨6293954053662861679451533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33567754952868595623741509 6293954053662861679451533)
                ·
                  refine ⟨2360232770123573129794325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6293954053662861679451533 2360232770123573129794325)
                  ·
                    refine ⟨110635911099542490459109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2360232770123573129794325 110635911099542490459109)
                    ·
                      rfl

theorem cell22_323194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_323194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323194 prefixEnd_323194 := by exact prefixLift 323194
  have htrace : WordTrace (prefixWord ++ tailWord_323194) baseStart_323194 baseEnd_323194 := by
    simpa [prefixWord, tailWord_323194, baseEnd_323194] using wordTrace_append hprefix tailTrace_323194
  have hstable : (prefixWord ++ tailWord_323194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323194).length < 2 ^ (prefixWord ++ tailWord_323194).sum := by decide
  have hdescent : baseEnd_323194 < baseStart_323194 := by decide
  rcases family_descends (prefixWord ++ tailWord_323194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323209 : List Nat := [1, 2, 1, 1, 4, 1, 3, 9]
def baseStart_323209 : Nat := 118140960795 + 323209 * 2 ^ 59
def prefixEnd_323209 : Nat := 4983230072969 + 3 ^ 40 * 323209 * 2
def baseEnd_323209 : Nat := 12293449545120827926007

theorem tailTrace_323209 : CollatzResearch.WordTrace tailWord_323209 prefixEnd_323209 12293449545120827926007 := by
  unfold tailWord_323209
  simp only [CollatzResearch.WordTrace]
  refine ⟨11788400686076467547636681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7858933790717645031757787 11788400686076467547636681)
  ·
    refine ⟨8841300514557350660727511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11788400686076467547636681 8841300514557350660727511)
    ·
      refine ⟨13261950771836025991091267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8841300514557350660727511 13261950771836025991091267)
      ·
        refine ⟨19892926157754038986636901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13261950771836025991091267 19892926157754038986636901)
        ·
          refine ⟨3729923654578882309994419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19892926157754038986636901 3729923654578882309994419)
          ·
            refine ⟨5594885481868323464991629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3729923654578882309994419 5594885481868323464991629)
            ·
              refine ⟨2098082055700621299371861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5594885481868323464991629 2098082055700621299371861)
              ·
                refine ⟨12293449545120827926007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2098082055700621299371861 12293449545120827926007)
                ·
                  rfl

theorem cell22_323209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 9].length) (baseStart_323209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323209 prefixEnd_323209 := by exact prefixLift 323209
  have htrace : WordTrace (prefixWord ++ tailWord_323209) baseStart_323209 baseEnd_323209 := by
    simpa [prefixWord, tailWord_323209, baseEnd_323209] using wordTrace_append hprefix tailTrace_323209
  have hstable : (prefixWord ++ tailWord_323209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323209).length < 2 ^ (prefixWord ++ tailWord_323209).sum := by decide
  have hdescent : baseEnd_323209 < baseStart_323209 := by decide
  rcases family_descends (prefixWord ++ tailWord_323209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323271 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 5]
def baseStart_323271 : Nat := 118140960795 + 323271 * 2 ^ 59
def prefixEnd_323271 : Nat := 4983230072969 + 3 ^ 40 * 323271 * 2
def baseEnd_323271 : Nat := 36887423257713318761291

theorem tailTrace_323271 : CollatzResearch.WordTrace tailWord_323271 prefixEnd_323271 36887423257713318761291 := by
  unfold tailWord_323271
  simp only [CollatzResearch.WordTrace]
  refine ⟨11790662011851852136393667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7860441341234568090929111 11790662011851852136393667)
  ·
    refine ⟨17685993017777778204590501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11790662011851852136393667 17685993017777778204590501)
    ·
      refine ⟨3316123690833333413360719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17685993017777778204590501 3316123690833333413360719)
      ·
        refine ⟨4974185536250000120041079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3316123690833333413360719 4974185536250000120041079)
        ·
          refine ⟨7461278304375000180061619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4974185536250000120041079 7461278304375000180061619)
          ·
            refine ⟨11191917456562500270092429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7461278304375000180061619 11191917456562500270092429)
            ·
              refine ⟨4196969046210937601284661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11191917456562500270092429 4196969046210937601284661)
              ·
                refine ⟨393465848082275400120437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4196969046210937601284661 393465848082275400120437)
                ·
                  refine ⟨36887423257713318761291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 393465848082275400120437 36887423257713318761291)
                  ·
                    rfl

theorem cell22_323271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 5].length) (baseStart_323271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323271 prefixEnd_323271 := by exact prefixLift 323271
  have htrace : WordTrace (prefixWord ++ tailWord_323271) baseStart_323271 baseEnd_323271 := by
    simpa [prefixWord, tailWord_323271, baseEnd_323271] using wordTrace_append hprefix tailTrace_323271
  have hstable : (prefixWord ++ tailWord_323271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323271).length < 2 ^ (prefixWord ++ tailWord_323271).sum := by decide
  have hdescent : baseEnd_323271 < baseStart_323271 := by decide
  rcases family_descends (prefixWord ++ tailWord_323271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323361 : List Nat := [1, 2, 3, 2, 1, 3, 10]
def baseStart_323361 : Nat := 118140960795 + 323361 * 2 ^ 59
def prefixEnd_323361 : Nat := 4983230072969 + 3 ^ 40 * 323361 * 2
def baseEnd_323361 : Nat := 4099743652311471167911

theorem tailTrace_323361 : CollatzResearch.WordTrace tailWord_323361 prefixEnd_323361 4099743652311471167911 := by
  unfold tailWord_323361
  simp only [CollatzResearch.WordTrace]
  refine ⟨11793944581525797507169937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7862629721017198338113291 11793944581525797507169937)
  ·
    refine ⟨8845458436144348130377453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11793944581525797507169937 8845458436144348130377453)
    ·
      refine ⟨3317046913554130548891545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8845458436144348130377453 3317046913554130548891545)
      ·
        refine ⟨2487785185165597911668659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3317046913554130548891545 2487785185165597911668659)
        ·
          refine ⟨3731677777748396867502989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487785185165597911668659 3731677777748396867502989)
          ·
            refine ⟨1399379166655648825313621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3731677777748396867502989 1399379166655648825313621)
            ·
              refine ⟨4099743652311471167911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1399379166655648825313621 4099743652311471167911)
              ·
                rfl

theorem cell22_323361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 10].length) (baseStart_323361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323361 prefixEnd_323361 := by exact prefixLift 323361
  have htrace : WordTrace (prefixWord ++ tailWord_323361) baseStart_323361 baseEnd_323361 := by
    simpa [prefixWord, tailWord_323361, baseEnd_323361] using wordTrace_append hprefix tailTrace_323361
  have hstable : (prefixWord ++ tailWord_323361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323361).length < 2 ^ (prefixWord ++ tailWord_323361).sum := by decide
  have hdescent : baseEnd_323361 < baseStart_323361 := by decide
  rcases family_descends (prefixWord ++ tailWord_323361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323378 : List Nat := [3, 2, 1, 1, 3, 3, 2, 7]
def baseStart_323378 : Nat := 118140960795 + 323378 * 2 ^ 59
def prefixEnd_323378 : Nat := 4983230072969 + 3 ^ 40 * 323378 * 2
def baseEnd_323378 : Nat := 12299877562203038206505

theorem tailTrace_323378 : CollatzResearch.WordTrace tailWord_323378 prefixEnd_323378 12299877562203038206505 := by
  unfold tailWord_323378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2948641155616052352634697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7863043081642806273692525 2948641155616052352634697)
  ·
    refine ⟨2211480866712039264476023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2948641155616052352634697 2211480866712039264476023)
    ·
      refine ⟨3317221300068058896714035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2211480866712039264476023 3317221300068058896714035)
      ·
        refine ⟨4975831950102088345071053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3317221300068058896714035 4975831950102088345071053)
        ·
          refine ⟨1865936981288283129401645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4975831950102088345071053 1865936981288283129401645)
          ·
            refine ⟨699726367983106173525617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1865936981288283129401645 699726367983106173525617)
            ·
              refine ⟨524794775987329630144213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699726367983106173525617 524794775987329630144213)
              ·
                refine ⟨12299877562203038206505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 524794775987329630144213 12299877562203038206505)
                ·
                  rfl

theorem cell22_323378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_323378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323378 prefixEnd_323378 := by exact prefixLift 323378
  have htrace : WordTrace (prefixWord ++ tailWord_323378) baseStart_323378 baseEnd_323378 := by
    simpa [prefixWord, tailWord_323378, baseEnd_323378] using wordTrace_append hprefix tailTrace_323378
  have hstable : (prefixWord ++ tailWord_323378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323378).length < 2 ^ (prefixWord ++ tailWord_323378).sum := by decide
  have hdescent : baseEnd_323378 < baseStart_323378 := by decide
  rcases family_descends (prefixWord ++ tailWord_323378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323423 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 5]
def baseStart_323423 : Nat := 118140960795 + 323423 * 2 ^ 59
def prefixEnd_323423 : Nat := 4983230072969 + 3 ^ 40 * 323423 * 2
def baseEnd_323423 : Nat := 36904767493154075494469

theorem tailTrace_323423 : CollatzResearch.WordTrace tailWord_323423 prefixEnd_323423 36904767493154075494469 := by
  unfold tailWord_323423
  simp only [CollatzResearch.WordTrace]
  refine ⟨11796205907301182095926923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7864137271534121397284615 11796205907301182095926923)
  ·
    refine ⟨17694308860951773143890385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11796205907301182095926923 17694308860951773143890385)
    ·
      refine ⟨13270731645713829857917789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17694308860951773143890385 13270731645713829857917789)
      ·
        refine ⟨4976524367142686196719171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13270731645713829857917789 4976524367142686196719171)
        ·
          refine ⟨7464786550714029295078757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4976524367142686196719171 7464786550714029295078757)
          ·
            refine ⟨1399647478258880492827267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7464786550714029295078757 1399647478258880492827267)
            ·
              refine ⟨2099471217388320739240901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399647478258880492827267 2099471217388320739240901)
              ·
                refine ⟨393650853260310138607669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2099471217388320739240901 393650853260310138607669)
                ·
                  refine ⟨36904767493154075494469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 393650853260310138607669 36904767493154075494469)
                  ·
                    rfl

theorem cell22_323423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 5].length) (baseStart_323423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323423 prefixEnd_323423 := by exact prefixLift 323423
  have htrace : WordTrace (prefixWord ++ tailWord_323423) baseStart_323423 baseEnd_323423 := by
    simpa [prefixWord, tailWord_323423, baseEnd_323423] using wordTrace_append hprefix tailTrace_323423
  have hstable : (prefixWord ++ tailWord_323423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323423).length < 2 ^ (prefixWord ++ tailWord_323423).sum := by decide
  have hdescent : baseEnd_323423 < baseStart_323423 := by decide
  rcases family_descends (prefixWord ++ tailWord_323423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323485 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 6]
def baseStart_323485 : Nat := 118140960795 + 323485 * 2 ^ 59
def prefixEnd_323485 : Nat := 4983230072969 + 3 ^ 40 * 323485 * 2
def baseEnd_323485 : Nat := 36911842115504910477739

theorem tailTrace_323485 : CollatzResearch.WordTrace tailWord_323485 prefixEnd_323485 36911842115504910477739 := by
  unfold tailWord_323485
  simp only [CollatzResearch.WordTrace]
  refine ⟨11798467233076566684683909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7865644822051044456455939 11798467233076566684683909)
  ·
    refine ⟨2212212606201856253378233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11798467233076566684683909 2212212606201856253378233)
    ·
      refine ⟨1659159454651392190033675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2212212606201856253378233 1659159454651392190033675)
      ·
        refine ⟨2488739181977088285050513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1659159454651392190033675 2488739181977088285050513)
        ·
          refine ⟨1866554386482816213787885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2488739181977088285050513 1866554386482816213787885)
          ·
            refine ⟨699957894931056080170457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1866554386482816213787885 699957894931056080170457)
            ·
              refine ⟨524968421198292060127843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699957894931056080170457 524968421198292060127843)
              ·
                refine ⟨787452631797438090191765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524968421198292060127843 787452631797438090191765)
                ·
                  refine ⟨36911842115504910477739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 787452631797438090191765 36911842115504910477739)
                  ·
                    rfl

theorem cell22_323485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_323485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323485 prefixEnd_323485 := by exact prefixLift 323485
  have htrace : WordTrace (prefixWord ++ tailWord_323485) baseStart_323485 baseEnd_323485 := by
    simpa [prefixWord, tailWord_323485, baseEnd_323485] using wordTrace_append hprefix tailTrace_323485
  have hstable : (prefixWord ++ tailWord_323485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323485).length < 2 ^ (prefixWord ++ tailWord_323485).sum := by decide
  have hdescent : baseEnd_323485 < baseStart_323485 := by decide
  rcases family_descends (prefixWord ++ tailWord_323485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323513 : List Nat := [1, 2, 1, 4, 2, 1, 3, 8]
def baseStart_323513 : Nat := 118140960795 + 323513 * 2 ^ 59
def prefixEnd_323513 : Nat := 4983230072969 + 3 ^ 40 * 323513 * 2
def baseEnd_323513 : Nat := 12305012368747999081459

theorem tailTrace_323513 : CollatzResearch.WordTrace tailWord_323513 prefixEnd_323513 12305012368747999081459 := by
  unfold tailWord_323513
  simp only [CollatzResearch.WordTrace]
  refine ⟨11799488476975127466703193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7866325651316751644468795 11799488476975127466703193)
  ·
    refine ⟨8849616357731345600027395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11799488476975127466703193 8849616357731345600027395)
    ·
      refine ⟨13274424536597018400041093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8849616357731345600027395 13274424536597018400041093)
      ·
        refine ⟨2488954600611940950007705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13274424536597018400041093 2488954600611940950007705)
        ·
          refine ⟨1866715950458955712505779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2488954600611940950007705 1866715950458955712505779)
          ·
            refine ⟨2800073925688433568758669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866715950458955712505779 2800073925688433568758669)
            ·
              refine ⟨1050027722133162588284501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2800073925688433568758669 1050027722133162588284501)
              ·
                refine ⟨12305012368747999081459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1050027722133162588284501 12305012368747999081459)
                ·
                  rfl

theorem cell22_323513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 8].length) (baseStart_323513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323513 prefixEnd_323513 := by exact prefixLift 323513
  have htrace : WordTrace (prefixWord ++ tailWord_323513) baseStart_323513 baseEnd_323513 := by
    simpa [prefixWord, tailWord_323513, baseEnd_323513] using wordTrace_append hprefix tailTrace_323513
  have hstable : (prefixWord ++ tailWord_323513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323513).length < 2 ^ (prefixWord ++ tailWord_323513).sum := by decide
  have hdescent : baseEnd_323513 < baseStart_323513 := by decide
  rcases family_descends (prefixWord ++ tailWord_323513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323543 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 2, 6]
def baseStart_323543 : Nat := 118140960795 + 323543 * 2 ^ 59
def prefixEnd_323543 : Nat := 4983230072969 + 3 ^ 40 * 323543 * 2
def baseEnd_323543 : Nat := 110755380931821913483039

theorem tailTrace_323543 : CollatzResearch.WordTrace tailWord_323543 prefixEnd_323543 110755380931821913483039 := by
  unfold tailWord_323543
  simp only [CollatzResearch.WordTrace]
  refine ⟨11800582666866442590295283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7867055111244295060196855 11800582666866442590295283)
  ·
    refine ⟨17700874000299663885442925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11800582666866442590295283 17700874000299663885442925)
    ·
      refine ⟨6637827750112373957041097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17700874000299663885442925 6637827750112373957041097)
      ·
        refine ⟨4978370812584280467780823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6637827750112373957041097 4978370812584280467780823)
        ·
          refine ⟨7467556218876420701671235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4978370812584280467780823 7467556218876420701671235)
          ·
            refine ⟨11201334328314631052506853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7467556218876420701671235 11201334328314631052506853)
            ·
              refine ⟨2100250186558993322345035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11201334328314631052506853 2100250186558993322345035)
              ·
                refine ⟨3150375279838489983517553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100250186558993322345035 3150375279838489983517553)
                ·
                  refine ⟨2362781459878867487638165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3150375279838489983517553 2362781459878867487638165)
                  ·
                    refine ⟨110755380931821913483039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2362781459878867487638165 110755380931821913483039)
                    ·
                      rfl

theorem cell22_323543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_323543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323543 prefixEnd_323543 := by exact prefixLift 323543
  have htrace : WordTrace (prefixWord ++ tailWord_323543) baseStart_323543 baseEnd_323543 := by
    simpa [prefixWord, tailWord_323543, baseEnd_323543] using wordTrace_append hprefix tailTrace_323543
  have hstable : (prefixWord ++ tailWord_323543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323543).length < 2 ^ (prefixWord ++ tailWord_323543).sum := by decide
  have hdescent : baseEnd_323543 < baseStart_323543 := by decide
  rcases family_descends (prefixWord ++ tailWord_323543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323607 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 2, 5]
def baseStart_323607 : Nat := 118140960795 + 323607 * 2 ^ 59
def prefixEnd_323607 : Nat := 4983230072969 + 3 ^ 40 * 323607 * 2
def baseEnd_323607 : Nat := 110777289439747079882843

theorem tailTrace_323607 : CollatzResearch.WordTrace tailWord_323607 prefixEnd_323607 110777289439747079882843 := by
  unfold tailWord_323607
  simp only [CollatzResearch.WordTrace]
  refine ⟨11802916938634581520625075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7868611292423054347083383 11802916938634581520625075)
  ·
    refine ⟨17704375407951872280937613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11802916938634581520625075 17704375407951872280937613)
    ·
      refine ⟨6639140777981952105351605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17704375407951872280937613 6639140777981952105351605)
      ·
        refine ⟨622419447935808009876713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6639140777981952105351605 622419447935808009876713)
        ·
          refine ⟨466814585951856007407535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 622419447935808009876713 466814585951856007407535)
          ·
            refine ⟨700221878927784011111303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466814585951856007407535 700221878927784011111303)
            ·
              refine ⟨1050332818391676016666955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700221878927784011111303 1050332818391676016666955)
              ·
                refine ⟨1575499227587514025000433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1050332818391676016666955 1575499227587514025000433)
                ·
                  refine ⟨1181624420690635518750325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1575499227587514025000433 1181624420690635518750325)
                  ·
                    refine ⟨110777289439747079882843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1181624420690635518750325 110777289439747079882843)
                    ·
                      rfl

theorem cell22_323607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_323607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323607 prefixEnd_323607 := by exact prefixLift 323607
  have htrace : WordTrace (prefixWord ++ tailWord_323607) baseStart_323607 baseEnd_323607 := by
    simpa [prefixWord, tailWord_323607, baseEnd_323607] using wordTrace_append hprefix tailTrace_323607
  have hstable : (prefixWord ++ tailWord_323607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323607).length < 2 ^ (prefixWord ++ tailWord_323607).sum := by decide
  have hdescent : baseEnd_323607 < baseStart_323607 := by decide
  rcases family_descends (prefixWord ++ tailWord_323607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323635 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 1, 5]
def baseStart_323635 : Nat := 118140960795 + 323635 * 2 ^ 59
def prefixEnd_323635 : Nat := 4983230072969 + 3 ^ 40 * 323635 * 2
def baseEnd_323635 : Nat := 110786874411964340182757

theorem tailTrace_323635 : CollatzResearch.WordTrace tailWord_323635 prefixEnd_323635 110786874411964340182757 := by
  unfold tailWord_323635
  simp only [CollatzResearch.WordTrace]
  refine ⟨11803938182533142302644359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7869292121688761535096239 11803938182533142302644359)
  ·
    refine ⟨17705907273799713453966539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11803938182533142302644359 17705907273799713453966539)
    ·
      refine ⟨26558860910699570180949809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17705907273799713453966539 26558860910699570180949809)
      ·
        refine ⟨19919145683024677635712357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26558860910699570180949809 19919145683024677635712357)
        ·
          refine ⟨3734839815567127056696067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19919145683024677635712357 3734839815567127056696067)
          ·
            refine ⟨5602259723350690585044101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3734839815567127056696067 5602259723350690585044101)
            ·
              refine ⟨1050423698128254484695769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5602259723350690585044101 1050423698128254484695769)
              ·
                refine ⟨787817773596190863521827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1050423698128254484695769 787817773596190863521827)
                ·
                  refine ⟨1181726660394286295282741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 787817773596190863521827 1181726660394286295282741)
                  ·
                    refine ⟨110786874411964340182757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1181726660394286295282741 110786874411964340182757)
                    ·
                      rfl

theorem cell22_323635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 5].length) (baseStart_323635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323635 prefixEnd_323635 := by exact prefixLift 323635
  have htrace : WordTrace (prefixWord ++ tailWord_323635) baseStart_323635 baseEnd_323635 := by
    simpa [prefixWord, tailWord_323635, baseEnd_323635] using wordTrace_append hprefix tailTrace_323635
  have hstable : (prefixWord ++ tailWord_323635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323635).length < 2 ^ (prefixWord ++ tailWord_323635).sum := by decide
  have hdescent : baseEnd_323635 < baseStart_323635 := by decide
  rcases family_descends (prefixWord ++ tailWord_323635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323637 : List Nat := [1, 3, 3, 1, 1, 1, 3, 5, 4]
def baseStart_323637 : Nat := 118140960795 + 323637 * 2 ^ 59
def prefixEnd_323637 : Nat := 4983230072969 + 3 ^ 40 * 323637 * 2
def baseEnd_323637 : Nat := 36929186350945667210917

theorem tailTrace_323637 : CollatzResearch.WordTrace tailWord_323637 prefixEnd_323637 36929186350945667210917 := by
  unfold tailWord_323637
  simp only [CollatzResearch.WordTrace]
  refine ⟨11804011128525896644217165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7869340752350597762811443 11804011128525896644217165)
  ·
    refine ⟨4426504173197211241581437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11804011128525896644217165 4426504173197211241581437)
    ·
      refine ⟨1659939064948954215593039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4426504173197211241581437 1659939064948954215593039)
      ·
        refine ⟨2489908597423431323389559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1659939064948954215593039 2489908597423431323389559)
        ·
          refine ⟨3734862896135146985084339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2489908597423431323389559 3734862896135146985084339)
          ·
            refine ⟨5602294344202720477626509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3734862896135146985084339 5602294344202720477626509)
            ·
              refine ⟨2100860379076020179109941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5602294344202720477626509 2100860379076020179109941)
              ·
                refine ⟨196955660538376891791557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2100860379076020179109941 196955660538376891791557)
                ·
                  refine ⟨36929186350945667210917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196955660538376891791557 36929186350945667210917)
                  ·
                    rfl

theorem cell22_323637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_323637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323637 prefixEnd_323637 := by exact prefixLift 323637
  have htrace : WordTrace (prefixWord ++ tailWord_323637) baseStart_323637 baseEnd_323637 := by
    simpa [prefixWord, tailWord_323637, baseEnd_323637] using wordTrace_append hprefix tailTrace_323637
  have hstable : (prefixWord ++ tailWord_323637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323637).length < 2 ^ (prefixWord ++ tailWord_323637).sum := by decide
  have hdescent : baseEnd_323637 < baseStart_323637 := by decide
  rcases family_descends (prefixWord ++ tailWord_323637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323654 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_323654 : Nat := 118140960795 + 323654 * 2 ^ 59
def prefixEnd_323654 : Nat := 4983230072969 + 3 ^ 40 * 323654 * 2
def baseEnd_323654 : Nat := 36931126166751541319233

theorem tailTrace_323654 : CollatzResearch.WordTrace tailWord_323654 prefixEnd_323654 36931126166751541319233 := by
  unfold tailWord_323654
  simp only [CollatzResearch.WordTrace]
  refine ⟨368894724045759642112063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7869754112976205698390677 368894724045759642112063)
  ·
    refine ⟨553342086068639463168095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 368894724045759642112063 553342086068639463168095)
    ·
      refine ⟨830013129102959194752143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 553342086068639463168095 830013129102959194752143)
      ·
        refine ⟨1245019693654438792128215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830013129102959194752143 1245019693654438792128215)
        ·
          refine ⟨1867529540481658188192323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245019693654438792128215 1867529540481658188192323)
          ·
            refine ⟨2801294310722487282288485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867529540481658188192323 2801294310722487282288485)
            ·
              refine ⟨525242683260466365429091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2801294310722487282288485 525242683260466365429091)
              ·
                refine ⟨787864024890699548143637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525242683260466365429091 787864024890699548143637)
                ·
                  refine ⟨36931126166751541319233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 787864024890699548143637 36931126166751541319233)
                  ·
                    rfl

theorem cell22_323654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_323654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323654 prefixEnd_323654 := by exact prefixLift 323654
  have htrace : WordTrace (prefixWord ++ tailWord_323654) baseStart_323654 baseEnd_323654 := by
    simpa [prefixWord, tailWord_323654, baseEnd_323654] using wordTrace_append hprefix tailTrace_323654
  have hstable : (prefixWord ++ tailWord_323654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323654).length < 2 ^ (prefixWord ++ tailWord_323654).sum := by decide
  have hdescent : baseEnd_323654 < baseStart_323654 := by decide
  rcases family_descends (prefixWord ++ tailWord_323654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323787 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 1, 5]
def baseStart_323787 : Nat := 118140960795 + 323787 * 2 ^ 59
def prefixEnd_323787 : Nat := 4983230072969 + 3 ^ 40 * 323787 * 2
def baseEnd_323787 : Nat := 110838907118286610382291

theorem tailTrace_323787 : CollatzResearch.WordTrace tailWord_323787 prefixEnd_323787 110838907118286610382291 := by
  unfold tailWord_323787
  simp only [CollatzResearch.WordTrace]
  refine ⟨11809482077982472262177615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7872988051988314841451743 11809482077982472262177615)
  ·
    refine ⟨17714223116973708393266423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11809482077982472262177615 17714223116973708393266423)
    ·
      refine ⟨26571334675460562589899635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17714223116973708393266423 26571334675460562589899635)
      ·
        refine ⟨39857002013190843884849453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26571334675460562589899635 39857002013190843884849453)
        ·
          refine ⟨14946375754946566456818545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39857002013190843884849453 14946375754946566456818545)
          ·
            refine ⟨11209781816209924842613909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14946375754946566456818545 11209781816209924842613909)
            ·
              refine ⟨525458522634840226997527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11209781816209924842613909 525458522634840226997527)
              ·
                refine ⟨788187783952260340496291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525458522634840226997527 788187783952260340496291)
                ·
                  refine ⟨1182281675928390510744437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 788187783952260340496291 1182281675928390510744437)
                  ·
                    refine ⟨110838907118286610382291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1182281675928390510744437 110838907118286610382291)
                    ·
                      rfl

theorem cell22_323787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 5].length) (baseStart_323787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323787 prefixEnd_323787 := by exact prefixLift 323787
  have htrace : WordTrace (prefixWord ++ tailWord_323787) baseStart_323787 baseEnd_323787 := by
    simpa [prefixWord, tailWord_323787, baseEnd_323787] using wordTrace_append hprefix tailTrace_323787
  have hstable : (prefixWord ++ tailWord_323787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323787).length < 2 ^ (prefixWord ++ tailWord_323787).sum := by decide
  have hdescent : baseEnd_323787 < baseStart_323787 := by decide
  rcases family_descends (prefixWord ++ tailWord_323787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323821 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_323821 : Nat := 118140960795 + 323821 * 2 ^ 59
def prefixEnd_323821 : Nat := 4983230072969 + 3 ^ 40 * 323821 * 2
def baseEnd_323821 : Nat := 110850546013121855032187

theorem tailTrace_323821 : CollatzResearch.WordTrace tailWord_323821 prefixEnd_323821 110850546013121855032187 := by
  unfold tailWord_323821
  simp only [CollatzResearch.WordTrace]
  refine ⟨11810722159859296068915317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7873814773239530712610211 11810722159859296068915317)
  ·
    refine ⟨1107255202486809006460811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11810722159859296068915317 1107255202486809006460811)
    ·
      refine ⟨1660882803730213509691217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1107255202486809006460811 1660882803730213509691217)
      ·
        refine ⟨1245662102797660132268413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1660882803730213509691217 1245662102797660132268413)
        ·
          refine ⟨467123288549122549600655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1245662102797660132268413 467123288549122549600655)
          ·
            refine ⟨700684932823683824400983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467123288549122549600655 700684932823683824400983)
            ·
              refine ⟨1051027399235525736601475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700684932823683824400983 1051027399235525736601475)
              ·
                refine ⟨1576541098853288604902213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051027399235525736601475 1576541098853288604902213)
                ·
                  refine ⟨295601456034991613419165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1576541098853288604902213 295601456034991613419165)
                  ·
                    refine ⟨110850546013121855032187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 295601456034991613419165 110850546013121855032187)
                    ·
                      rfl

theorem cell22_323821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_323821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323821 prefixEnd_323821 := by exact prefixLift 323821
  have htrace : WordTrace (prefixWord ++ tailWord_323821) baseStart_323821 baseEnd_323821 := by
    simpa [prefixWord, tailWord_323821, baseEnd_323821] using wordTrace_append hprefix tailTrace_323821
  have hstable : (prefixWord ++ tailWord_323821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323821).length < 2 ^ (prefixWord ++ tailWord_323821).sum := by decide
  have hdescent : baseEnd_323821 < baseStart_323821 := by decide
  rcases family_descends (prefixWord ++ tailWord_323821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323838 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_323838 : Nat := 118140960795 + 323838 * 2 ^ 59
def prefixEnd_323838 : Nat := 4983230072969 + 3 ^ 40 * 323838 * 2
def baseEnd_323838 : Nat := 110856365460539477357135

theorem tailTrace_323838 : CollatzResearch.WordTrace tailWord_323838 prefixEnd_323838 110856365460539477357135 := by
  unfold tailWord_323838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476417775099713496535521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7874228133865138648189445 1476417775099713496535521)
  ·
    refine ⟨1107313331324785122401641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1476417775099713496535521 1107313331324785122401641)
    ·
      refine ⟨830484998493588841801231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1107313331324785122401641 830484998493588841801231)
      ·
        refine ⟨1245727497740383262701847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830484998493588841801231 1245727497740383262701847)
        ·
          refine ⟨1868591246610574894052771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245727497740383262701847 1868591246610574894052771)
          ·
            refine ⟨2802886869915862341079157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1868591246610574894052771 2802886869915862341079157)
            ·
              refine ⟨262770644054612094476171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2802886869915862341079157 262770644054612094476171)
              ·
                refine ⟨394155966081918141714257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262770644054612094476171 394155966081918141714257)
                ·
                  refine ⟨295616974561438606285693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394155966081918141714257 295616974561438606285693)
                  ·
                    refine ⟨110856365460539477357135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 295616974561438606285693 110856365460539477357135)
                    ·
                      rfl

theorem cell22_323838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_323838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323838 prefixEnd_323838 := by exact prefixLift 323838
  have htrace : WordTrace (prefixWord ++ tailWord_323838) baseStart_323838 baseEnd_323838 := by
    simpa [prefixWord, tailWord_323838, baseEnd_323838] using wordTrace_append hprefix tailTrace_323838
  have hstable : (prefixWord ++ tailWord_323838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323838).length < 2 ^ (prefixWord ++ tailWord_323838).sum := by decide
  have hdescent : baseEnd_323838 < baseStart_323838 := by decide
  rcases family_descends (prefixWord ++ tailWord_323838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323849 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 3, 3]
def baseStart_323849 : Nat := 118140960795 + 323849 * 2 ^ 59
def prefixEnd_323849 : Nat := 4983230072969 + 3 ^ 40 * 323849 * 2
def baseEnd_323849 : Nat := 110860130985339115332101

theorem tailTrace_323849 : CollatzResearch.WordTrace tailWord_323849 prefixEnd_323849 110860130985339115332101 := by
  unfold tailWord_323849
  simp only [CollatzResearch.WordTrace]
  refine ⟨11811743403757856850934601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7874495602505237900623067 11811743403757856850934601)
  ·
    refine ⟨8858807552818392638200951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11811743403757856850934601 8858807552818392638200951)
    ·
      refine ⟨13288211329227588957301427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8858807552818392638200951 13288211329227588957301427)
      ·
        refine ⟨19932316993841383435952141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13288211329227588957301427 19932316993841383435952141)
        ·
          refine ⟨7474618872690518788482053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19932316993841383435952141 7474618872690518788482053)
          ·
            refine ⟨1401491038629472272840385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7474618872690518788482053 1401491038629472272840385)
            ·
              refine ⟨1051118278972104204630289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1401491038629472272840385 1051118278972104204630289)
              ·
                refine ⟨788338709229078153472717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051118278972104204630289 788338709229078153472717)
                ·
                  refine ⟨295627015960904307552269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788338709229078153472717 295627015960904307552269)
                  ·
                    refine ⟨110860130985339115332101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 295627015960904307552269 110860130985339115332101)
                    ·
                      rfl

theorem cell22_323849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 3].length) (baseStart_323849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323849 prefixEnd_323849 := by exact prefixLift 323849
  have htrace : WordTrace (prefixWord ++ tailWord_323849) baseStart_323849 baseEnd_323849 := by
    simpa [prefixWord, tailWord_323849, baseEnd_323849] using wordTrace_append hprefix tailTrace_323849
  have hstable : (prefixWord ++ tailWord_323849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323849).length < 2 ^ (prefixWord ++ tailWord_323849).sum := by decide
  have hdescent : baseEnd_323849 < baseStart_323849 := by decide
  rcases family_descends (prefixWord ++ tailWord_323849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323907 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 6]
def baseStart_323907 : Nat := 118140960795 + 323907 * 2 ^ 59
def prefixEnd_323907 : Nat := 4983230072969 + 3 ^ 40 * 323907 * 2
def baseEnd_323907 : Nat := 36959995190215432460641

theorem tailTrace_323907 : CollatzResearch.WordTrace tailWord_323907 prefixEnd_323907 36959995190215432460641 := by
  unfold tailWord_323907
  simp only [CollatzResearch.WordTrace]
  refine ⟨11813858837547732756545975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7875905891698488504363983 11813858837547732756545975)
  ·
    refine ⟨17720788256321599134818963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11813858837547732756545975 17720788256321599134818963)
    ·
      refine ⟨26581182384482398702228445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17720788256321599134818963 26581182384482398702228445)
      ·
        refine ⟨9967943394180899513335667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26581182384482398702228445 9967943394180899513335667)
        ·
          refine ⟨14951915091271349270003501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9967943394180899513335667 14951915091271349270003501)
          ·
            refine ⟨5606968159226755976251313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14951915091271349270003501 5606968159226755976251313)
            ·
              refine ⟨4205226119420066982188485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5606968159226755976251313 4205226119420066982188485)
              ·
                refine ⟨788479897391262559160341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4205226119420066982188485 788479897391262559160341)
                ·
                  refine ⟨36959995190215432460641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 788479897391262559160341 36959995190215432460641)
                  ·
                    rfl

theorem cell22_323907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 6].length) (baseStart_323907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323907 prefixEnd_323907 := by exact prefixLift 323907
  have htrace : WordTrace (prefixWord ++ tailWord_323907) baseStart_323907 baseEnd_323907 := by
    simpa [prefixWord, tailWord_323907, baseEnd_323907] using wordTrace_append hprefix tailTrace_323907
  have hstable : (prefixWord ++ tailWord_323907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323907).length < 2 ^ (prefixWord ++ tailWord_323907).sum := by decide
  have hdescent : baseEnd_323907 < baseStart_323907 := by decide
  rcases family_descends (prefixWord ++ tailWord_323907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323937 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_323937 : Nat := 118140960795 + 323937 * 2 ^ 59
def prefixEnd_323937 : Nat := 4983230072969 + 3 ^ 40 * 323937 * 2
def baseEnd_323937 : Nat := 110890255183736219131831

theorem tailTrace_323937 : CollatzResearch.WordTrace tailWord_323937 prefixEnd_323937 110890255183736219131831 := by
  unfold tailWord_323937
  simp only [CollatzResearch.WordTrace]
  refine ⟨11814953027439047880138065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7876635351626031920092043 11814953027439047880138065)
  ·
    refine ⟨8861214770579285910103549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11814953027439047880138065 8861214770579285910103549)
    ·
      refine ⟨3322955538967232216288831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8861214770579285910103549 3322955538967232216288831)
      ·
        refine ⟨4984433308450848324433247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3322955538967232216288831 4984433308450848324433247)
        ·
          refine ⟨7476649962676272486649871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4984433308450848324433247 7476649962676272486649871)
          ·
            refine ⟨11214974944014408729974807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7476649962676272486649871 11214974944014408729974807)
            ·
              refine ⟨16822462416021613094962211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11214974944014408729974807 16822462416021613094962211)
              ·
                refine ⟨25233693624032419642443317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16822462416021613094962211 25233693624032419642443317)
                ·
                  refine ⟨2365658777253039341479061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25233693624032419642443317 2365658777253039341479061)
                  ·
                    refine ⟨110890255183736219131831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2365658777253039341479061 110890255183736219131831)
                    ·
                      rfl

theorem cell22_323937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_323937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323937 prefixEnd_323937 := by exact prefixLift 323937
  have htrace : WordTrace (prefixWord ++ tailWord_323937) baseStart_323937 baseEnd_323937 := by
    simpa [prefixWord, tailWord_323937, baseEnd_323937] using wordTrace_append hprefix tailTrace_323937
  have hstable : (prefixWord ++ tailWord_323937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323937).length < 2 ^ (prefixWord ++ tailWord_323937).sum := by decide
  have hdescent : baseEnd_323937 < baseStart_323937 := by decide
  rcases family_descends (prefixWord ++ tailWord_323937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323941 : List Nat := [1, 3, 1, 3, 1, 4, 1, 4, 4]
def baseStart_323941 : Nat := 118140960795 + 323941 * 2 ^ 59
def prefixEnd_323941 : Nat := 4983230072969 + 3 ^ 40 * 323941 * 2
def baseEnd_323941 : Nat := 36963874821827180677273

theorem tailTrace_323941 : CollatzResearch.WordTrace tailWord_323941 prefixEnd_323941 36963874821827180677273 := by
  unfold tailWord_323941
  simp only [CollatzResearch.WordTrace]
  refine ⟨11815098919424556563283677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7876732612949704375522451 11815098919424556563283677)
  ·
    refine ⟨4430662094784208711231379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11815098919424556563283677 4430662094784208711231379)
    ·
      refine ⟨6645993142176313066847069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4430662094784208711231379 6645993142176313066847069)
      ·
        refine ⟨2492247428316117400067651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6645993142176313066847069 2492247428316117400067651)
        ·
          refine ⟨3738371142474176100101477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492247428316117400067651 3738371142474176100101477)
          ·
            refine ⟨700944589213908018769027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3738371142474176100101477 700944589213908018769027)
            ·
              refine ⟨1051416883820862028153541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700944589213908018769027 1051416883820862028153541)
              ·
                refine ⟨197140665716411630278789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1051416883820862028153541 197140665716411630278789)
                ·
                  refine ⟨36963874821827180677273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197140665716411630278789 36963874821827180677273)
                  ·
                    rfl

theorem cell22_323941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_323941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323941 prefixEnd_323941 := by exact prefixLift 323941
  have htrace : WordTrace (prefixWord ++ tailWord_323941) baseStart_323941 baseEnd_323941 := by
    simpa [prefixWord, tailWord_323941, baseEnd_323941] using wordTrace_append hprefix tailTrace_323941
  have hstable : (prefixWord ++ tailWord_323941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323941).length < 2 ^ (prefixWord ++ tailWord_323941).sum := by decide
  have hdescent : baseEnd_323941 < baseStart_323941 := by decide
  rcases family_descends (prefixWord ++ tailWord_323941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323958 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_323958 : Nat := 118140960795 + 323958 * 2 ^ 59
def prefixEnd_323958 : Nat := 4983230072969 + 3 ^ 40 * 323958 * 2
def baseEnd_323958 : Nat := 36965814637633054785589

theorem tailTrace_323958 : CollatzResearch.WordTrace tailWord_323958 prefixEnd_323958 36965814637633054785589 := by
  unfold tailWord_323958
  simp only [CollatzResearch.WordTrace]
  refine ⟨738482435022685529165783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7877145973575312311101685 738482435022685529165783)
  ·
    refine ⟨1107723652534028293748675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 738482435022685529165783 1107723652534028293748675)
    ·
      refine ⟨1661585478801042440623013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1107723652534028293748675 1661585478801042440623013)
      ·
        refine ⟨311547277275195457616815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1661585478801042440623013 311547277275195457616815)
        ·
          refine ⟨467320915912793186425223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311547277275195457616815 467320915912793186425223)
          ·
            refine ⟨700981373869189779637835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467320915912793186425223 700981373869189779637835)
            ·
              refine ⟨1051472060803784669456753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700981373869189779637835 1051472060803784669456753)
              ·
                refine ⟨788604045602838502092565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051472060803784669456753 788604045602838502092565)
                ·
                  refine ⟨36965814637633054785589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 788604045602838502092565 36965814637633054785589)
                  ·
                    rfl

theorem cell22_323958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_323958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323958 prefixEnd_323958 := by exact prefixLift 323958
  have htrace : WordTrace (prefixWord ++ tailWord_323958) baseStart_323958 baseEnd_323958 := by
    simpa [prefixWord, tailWord_323958, baseEnd_323958] using wordTrace_append hprefix tailTrace_323958
  have hstable : (prefixWord ++ tailWord_323958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323958).length < 2 ^ (prefixWord ++ tailWord_323958).sum := by decide
  have hdescent : baseEnd_323958 < baseStart_323958 := by decide
  rcases family_descends (prefixWord ++ tailWord_323958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323967 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 2, 7]
def baseStart_323967 : Nat := 118140960795 + 323967 * 2 ^ 59
def prefixEnd_323967 : Nat := 4983230072969 + 3 ^ 40 * 323967 * 2
def baseEnd_323967 : Nat := 110900524796826140881739

theorem tailTrace_323967 : CollatzResearch.WordTrace tailWord_323967 prefixEnd_323967 110900524796826140881739 := by
  unfold tailWord_323967
  simp only [CollatzResearch.WordTrace]
  refine ⟨11816047217330363003730155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7877364811553575335820103 11816047217330363003730155)
  ·
    refine ⟨17724070825995544505595233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11816047217330363003730155 17724070825995544505595233)
    ·
      refine ⟨13293053119496658379196425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17724070825995544505595233 13293053119496658379196425)
      ·
        refine ⟨9969789839622493784397319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13293053119496658379196425 9969789839622493784397319)
        ·
          refine ⟨14954684759433740676595979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9969789839622493784397319 14954684759433740676595979)
          ·
            refine ⟨22432027139150611014893969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14954684759433740676595979 22432027139150611014893969)
            ·
              refine ⟨16824020354362958261170477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22432027139150611014893969 16824020354362958261170477)
              ·
                refine ⟨6309007632886109347938929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16824020354362958261170477 6309007632886109347938929)
                ·
                  refine ⟨4731755724664582010954197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6309007632886109347938929 4731755724664582010954197)
                  ·
                    refine ⟨110900524796826140881739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4731755724664582010954197 110900524796826140881739)
                    ·
                      rfl

theorem cell22_323967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_323967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_323967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_323967 prefixEnd_323967 := by exact prefixLift 323967
  have htrace : WordTrace (prefixWord ++ tailWord_323967) baseStart_323967 baseEnd_323967 := by
    simpa [prefixWord, tailWord_323967, baseEnd_323967] using wordTrace_append hprefix tailTrace_323967
  have hstable : (prefixWord ++ tailWord_323967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323967).length < 2 ^ (prefixWord ++ tailWord_323967).sum := by decide
  have hdescent : baseEnd_323967 < baseStart_323967 := by decide
  rcases family_descends (prefixWord ++ tailWord_323967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324052 : List Nat := [2, 4, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_324052 : Nat := 118140960795 + 324052 * 2 ^ 59
def prefixEnd_324052 : Nat := 4983230072969 + 3 ^ 40 * 324052 * 2
def baseEnd_324052 : Nat := 110929622033914252506479

theorem tailTrace_324052 : CollatzResearch.WordTrace tailWord_324052 prefixEnd_324052 110929622033914252506479 := by
  unfold tailWord_324052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5909573711011211260287205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7879431614681615013716273 5909573711011211260287205)
  ·
    refine ⟨1108045070814602111303851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5909573711011211260287205 1108045070814602111303851)
    ·
      refine ⟨1662067606221903166955777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108045070814602111303851 1662067606221903166955777)
      ·
        refine ⟨1246550704666427375216833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1662067606221903166955777 1246550704666427375216833)
        ·
          refine ⟨934913028499820531412625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1246550704666427375216833 934913028499820531412625)
          ·
            refine ⟨701184771374865398559469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 934913028499820531412625 701184771374865398559469)
            ·
              refine ⟨262944289265574524459801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 701184771374865398559469 262944289265574524459801)
              ·
                refine ⟨197208216949180893344851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262944289265574524459801 197208216949180893344851)
                ·
                  refine ⟨295812325423771340017277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197208216949180893344851 295812325423771340017277)
                  ·
                    refine ⟨110929622033914252506479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 295812325423771340017277 110929622033914252506479)
                    ·
                      rfl

theorem cell22_324052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_324052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324052 prefixEnd_324052 := by exact prefixLift 324052
  have htrace : WordTrace (prefixWord ++ tailWord_324052) baseStart_324052 baseEnd_324052 := by
    simpa [prefixWord, tailWord_324052, baseEnd_324052] using wordTrace_append hprefix tailTrace_324052
  have hstable : (prefixWord ++ tailWord_324052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324052).length < 2 ^ (prefixWord ++ tailWord_324052).sum := by decide
  have hdescent : baseEnd_324052 < baseStart_324052 := by decide
  rcases family_descends (prefixWord ++ tailWord_324052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324061 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_324061 : Nat := 118140960795 + 324061 * 2 ^ 59
def prefixEnd_324061 : Nat := 4983230072969 + 3 ^ 40 * 324061 * 2
def baseEnd_324061 : Nat := 110932702917841229031451

theorem tailTrace_324061 : CollatzResearch.WordTrace tailWord_324061 prefixEnd_324061 110932702917841229031451 := by
  unfold tailWord_324061
  simp only [CollatzResearch.WordTrace]
  refine ⟨11819475678989817057652037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7879650452659878038434691 11819475678989817057652037)
  ·
    refine ⟨2216151689810590698309757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11819475678989817057652037 2216151689810590698309757)
    ·
      refine ⟨831056883678971511866159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2216151689810590698309757 831056883678971511866159)
      ·
        refine ⟨1246585325518457267799239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831056883678971511866159 1246585325518457267799239)
        ·
          refine ⟨1869877988277685901698859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246585325518457267799239 1869877988277685901698859)
          ·
            refine ⟨2804816982416528852548289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869877988277685901698859 2804816982416528852548289)
            ·
              refine ⟨2103612736812396639411217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804816982416528852548289 2103612736812396639411217)
              ·
                refine ⟨1577709552609297479558413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103612736812396639411217 1577709552609297479558413)
                ·
                  refine ⟨591641082228486554834405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1577709552609297479558413 591641082228486554834405)
                  ·
                    refine ⟨110932702917841229031451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 591641082228486554834405 110932702917841229031451)
                    ·
                      rfl

theorem cell22_324061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_324061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324061 prefixEnd_324061 := by exact prefixLift 324061
  have htrace : WordTrace (prefixWord ++ tailWord_324061) baseStart_324061 baseEnd_324061 := by
    simpa [prefixWord, tailWord_324061, baseEnd_324061] using wordTrace_append hprefix tailTrace_324061
  have hstable : (prefixWord ++ tailWord_324061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324061).length < 2 ^ (prefixWord ++ tailWord_324061).sum := by decide
  have hdescent : baseEnd_324061 < baseStart_324061 := by decide
  rcases family_descends (prefixWord ++ tailWord_324061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324078 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_324078 : Nat := 118140960795 + 324078 * 2 ^ 59
def prefixEnd_324078 : Nat := 4983230072969 + 3 ^ 40 * 324078 * 2
def baseEnd_324078 : Nat := 110938522365258851356399

theorem tailTrace_324078 : CollatzResearch.WordTrace tailWord_324078 prefixEnd_324078 110938522365258851356399 := by
  unfold tailWord_324078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477511964991028620127611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7880063813285485974013925 1477511964991028620127611)
  ·
    refine ⟨2216267947486542930191417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1477511964991028620127611 2216267947486542930191417)
    ·
      refine ⟨1662200960614907197643563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2216267947486542930191417 1662200960614907197643563)
      ·
        refine ⟨2493301440922360796465345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1662200960614907197643563 2493301440922360796465345)
        ·
          refine ⟨1869976080691770597349009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2493301440922360796465345 1869976080691770597349009)
          ·
            refine ⟨1402482060518827948011757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1869976080691770597349009 1402482060518827948011757)
            ·
              refine ⟨525930772694560480504409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1402482060518827948011757 525930772694560480504409)
              ·
                refine ⟨394448079520920360378307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525930772694560480504409 394448079520920360378307)
                ·
                  refine ⟨591672119281380540567461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394448079520920360378307 591672119281380540567461)
                  ·
                    refine ⟨110938522365258851356399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 591672119281380540567461 110938522365258851356399)
                    ·
                      rfl

theorem cell22_324078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_324078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324078 prefixEnd_324078 := by exact prefixLift 324078
  have htrace : WordTrace (prefixWord ++ tailWord_324078) baseStart_324078 baseEnd_324078 := by
    simpa [prefixWord, tailWord_324078, baseEnd_324078] using wordTrace_append hprefix tailTrace_324078
  have hstable : (prefixWord ++ tailWord_324078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324078).length < 2 ^ (prefixWord ++ tailWord_324078).sum := by decide
  have hdescent : baseEnd_324078 < baseStart_324078 := by decide
  rcases family_descends (prefixWord ++ tailWord_324078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324089 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_324089 : Nat := 118140960795 + 324089 * 2 ^ 59
def prefixEnd_324089 : Nat := 4983230072969 + 3 ^ 40 * 324089 * 2
def baseEnd_324089 : Nat := 110942287890058489331365

theorem tailTrace_324089 : CollatzResearch.WordTrace tailWord_324089 prefixEnd_324089 110942287890058489331365 := by
  unfold tailWord_324089
  simp only [CollatzResearch.WordTrace]
  refine ⟨11820496922888377839671321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7880331281925585226447547 11820496922888377839671321)
  ·
    refine ⟨8865372692166283379753491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11820496922888377839671321 8865372692166283379753491)
    ·
      refine ⟨13298059038249425069630237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8865372692166283379753491 13298059038249425069630237)
      ·
        refine ⟨4986772139343534401111339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13298059038249425069630237 4986772139343534401111339)
        ·
          refine ⟨7480158209015301601667009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4986772139343534401111339 7480158209015301601667009)
          ·
            refine ⟨5610118656761476201250257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7480158209015301601667009 5610118656761476201250257)
            ·
              refine ⟨4207588992571107150937693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5610118656761476201250257 4207588992571107150937693)
              ·
                refine ⟨1577845872214165181601635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4207588992571107150937693 1577845872214165181601635)
                ·
                  refine ⟨2366768808321247772402453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577845872214165181601635 2366768808321247772402453)
                  ·
                    refine ⟨110942287890058489331365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2366768808321247772402453 110942287890058489331365)
                    ·
                      rfl

theorem cell22_324089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_324089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324089 prefixEnd_324089 := by exact prefixLift 324089
  have htrace : WordTrace (prefixWord ++ tailWord_324089) baseStart_324089 baseEnd_324089 := by
    simpa [prefixWord, tailWord_324089, baseEnd_324089] using wordTrace_append hprefix tailTrace_324089
  have hstable : (prefixWord ++ tailWord_324089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324089).length < 2 ^ (prefixWord ++ tailWord_324089).sum := by decide
  have hdescent : baseEnd_324089 < baseStart_324089 := by decide
  rcases family_descends (prefixWord ++ tailWord_324089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324106 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_324106 : Nat := 118140960795 + 324106 * 2 ^ 59
def prefixEnd_324106 : Nat := 4983230072969 + 3 ^ 40 * 324106 * 2
def baseEnd_324106 : Nat := 110948107337476111656313

theorem tailTrace_324106 : CollatzResearch.WordTrace tailWord_324106 prefixEnd_324106 110948107337476111656313 := by
  unfold tailWord_324106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955279240956697435760043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7880744642551193162026781 2955279240956697435760043)
  ·
    refine ⟨4432918861435046153640065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2955279240956697435760043 4432918861435046153640065)
    ·
      refine ⟨3324689146076284615230049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4432918861435046153640065 3324689146076284615230049)
      ·
        refine ⟨2493516859557213461422537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3324689146076284615230049 2493516859557213461422537)
        ·
          refine ⟨1870137644667910096066903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2493516859557213461422537 1870137644667910096066903)
          ·
            refine ⟨2805206467001865144100355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870137644667910096066903 2805206467001865144100355)
            ·
              refine ⟨4207809700502797716150533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2805206467001865144100355 4207809700502797716150533)
              ·
                refine ⟨788964318844274571778225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4207809700502797716150533 788964318844274571778225)
                ·
                  refine ⟨591723239133205928833669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788964318844274571778225 591723239133205928833669)
                  ·
                    refine ⟨110948107337476111656313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 591723239133205928833669 110948107337476111656313)
                    ·
                      rfl

theorem cell22_324106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_324106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324106 prefixEnd_324106 := by exact prefixLift 324106
  have htrace : WordTrace (prefixWord ++ tailWord_324106) baseStart_324106 baseEnd_324106 := by
    simpa [prefixWord, tailWord_324106, baseEnd_324106] using wordTrace_append hprefix tailTrace_324106
  have hstable : (prefixWord ++ tailWord_324106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324106).length < 2 ^ (prefixWord ++ tailWord_324106).sum := by decide
  have hdescent : baseEnd_324106 < baseStart_324106 := by decide
  rcases family_descends (prefixWord ++ tailWord_324106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324108 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 2, 3]
def baseStart_324108 : Nat := 118140960795 + 324108 * 2 ^ 59
def prefixEnd_324108 : Nat := 4983230072969 + 3 ^ 40 * 324108 * 2
def baseEnd_324108 : Nat := 110948791978348773106307

theorem tailTrace_324108 : CollatzResearch.WordTrace tailWord_324108 prefixEnd_324108 110948791978348773106307 := by
  unfold tailWord_324108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5910594954909772042306489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7880793273213029389741985 5910594954909772042306489)
  ·
    refine ⟨4432946216182329031729867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5910594954909772042306489 4432946216182329031729867)
    ·
      refine ⟨6649419324273493547594801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4432946216182329031729867 6649419324273493547594801)
      ·
        refine ⟨4987064493205120160696101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6649419324273493547594801 4987064493205120160696101)
        ·
          refine ⟨935074592475960030130519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4987064493205120160696101 935074592475960030130519)
          ·
            refine ⟨1402611888713940045195779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935074592475960030130519 1402611888713940045195779)
            ·
              refine ⟨2103917833070910067793669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402611888713940045195779 2103917833070910067793669)
              ·
                refine ⟨394484593700795637711313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2103917833070910067793669 394484593700795637711313)
                ·
                  refine ⟨295863445275596728283485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394484593700795637711313 295863445275596728283485)
                  ·
                    refine ⟨110948791978348773106307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 295863445275596728283485 110948791978348773106307)
                    ·
                      rfl

theorem cell22_324108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_324108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324108 prefixEnd_324108 := by exact prefixLift 324108
  have htrace : WordTrace (prefixWord ++ tailWord_324108) baseStart_324108 baseEnd_324108 := by
    simpa [prefixWord, tailWord_324108, baseEnd_324108] using wordTrace_append hprefix tailTrace_324108
  have hstable : (prefixWord ++ tailWord_324108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324108).length < 2 ^ (prefixWord ++ tailWord_324108).sum := by decide
  have hdescent : baseEnd_324108 < baseStart_324108 := by decide
  rcases family_descends (prefixWord ++ tailWord_324108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324110 : List Nat := [4, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_324110 : Nat := 118140960795 + 324110 * 2 ^ 59
def prefixEnd_324110 : Nat := 4983230072969 + 3 ^ 40 * 324110 * 2
def baseEnd_324110 : Nat := 36983158873073811518767

theorem tailTrace_324110 : CollatzResearch.WordTrace tailWord_324110 prefixEnd_324110 36983158873073811518767 := by
  unfold tailWord_324110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477657856976537303273223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7880841903874865617457189 1477657856976537303273223)
  ·
    refine ⟨2216486785464805954909835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1477657856976537303273223 2216486785464805954909835)
    ·
      refine ⟨3324730178197208932364753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2216486785464805954909835 3324730178197208932364753)
      ·
        refine ⟨2493547633647906699273565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3324730178197208932364753 2493547633647906699273565)
        ·
          refine ⟨935080362617965012227587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2493547633647906699273565 935080362617965012227587)
          ·
            refine ⟨1402620543926947518341381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935080362617965012227587 1402620543926947518341381)
            ·
              refine ⟨262991351986302659689009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1402620543926947518341381 262991351986302659689009)
              ·
                refine ⟨197243513989726994766757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262991351986302659689009 197243513989726994766757)
                ·
                  refine ⟨36983158873073811518767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197243513989726994766757 36983158873073811518767)
                  ·
                    rfl

theorem cell22_324110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_324110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324110 prefixEnd_324110 := by exact prefixLift 324110
  have htrace : WordTrace (prefixWord ++ tailWord_324110) baseStart_324110 baseEnd_324110 := by
    simpa [prefixWord, tailWord_324110, baseEnd_324110] using wordTrace_append hprefix tailTrace_324110
  have hstable : (prefixWord ++ tailWord_324110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324110).length < 2 ^ (prefixWord ++ tailWord_324110).sum := by decide
  have hdescent : baseEnd_324110 < baseStart_324110 := by decide
  rcases family_descends (prefixWord ++ tailWord_324110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324138 : List Nat := [3, 1, 4, 1, 1, 3, 3, 6]
def baseStart_324138 : Nat := 118140960795 + 324138 * 2 ^ 59
def prefixEnd_324138 : Nat := 4983230072969 + 3 ^ 40 * 324138 * 2
def baseEnd_324138 : Nat := 12328784621270966095135

theorem tailTrace_324138 : CollatzResearch.WordTrace tailWord_324138 prefixEnd_324138 12328784621270966095135 := by
  unfold tailWord_324138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955571024927714802051267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7881522733140572805470045 2955571024927714802051267)
  ·
    refine ⟨4433356537391572203076901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2955571024927714802051267 4433356537391572203076901)
    ·
      refine ⟨831254350760919788076919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4433356537391572203076901 831254350760919788076919)
      ·
        refine ⟨1246881526141379682115379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831254350760919788076919 1246881526141379682115379)
        ·
          refine ⟨1870322289212069523173069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246881526141379682115379 1870322289212069523173069)
          ·
            refine ⟨701370858454526071189901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1870322289212069523173069 701370858454526071189901)
            ·
              refine ⟨263014071920447276696213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 701370858454526071189901 263014071920447276696213)
              ·
                refine ⟨12328784621270966095135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 263014071920447276696213 12328784621270966095135)
                ·
                  rfl

theorem cell22_324138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_324138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324138 prefixEnd_324138 := by exact prefixLift 324138
  have htrace : WordTrace (prefixWord ++ tailWord_324138) baseStart_324138 baseEnd_324138 := by
    simpa [prefixWord, tailWord_324138, baseEnd_324138] using wordTrace_append hprefix tailTrace_324138
  have hstable : (prefixWord ++ tailWord_324138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324138).length < 2 ^ (prefixWord ++ tailWord_324138).sum := by decide
  have hdescent : baseEnd_324138 < baseStart_324138 := by decide
  rcases family_descends (prefixWord ++ tailWord_324138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324170 : List Nat := [3, 1, 2, 1, 1, 4, 2, 4, 1, 3]
def baseStart_324170 : Nat := 118140960795 + 324170 * 2 ^ 59
def prefixEnd_324170 : Nat := 4983230072969 + 3 ^ 40 * 324170 * 2
def baseEnd_324170 : Nat := 110970015845401278056117

theorem tailTrace_324170 : CollatzResearch.WordTrace tailWord_324170 prefixEnd_324170 110970015845401278056117 := by
  unfold tailWord_324170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955862808898732168342491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7882300823729952448913309 2955862808898732168342491)
  ·
    refine ⟨4433794213348098252513737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2955862808898732168342491 4433794213348098252513737)
    ·
      refine ⟨3325345660011073689385303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4433794213348098252513737 3325345660011073689385303)
      ·
        refine ⟨4988018490016610534077955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325345660011073689385303 4988018490016610534077955)
        ·
          refine ⟨7482027735024915801116933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4988018490016610534077955 7482027735024915801116933)
          ·
            refine ⟨1402880200317171712709425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7482027735024915801116933 1402880200317171712709425)
            ·
              refine ⟨1052160150237878784532069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402880200317171712709425 1052160150237878784532069)
              ·
                refine ⟨197280028169602272099763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1052160150237878784532069 197280028169602272099763)
                ·
                  refine ⟨295920042254403408149645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197280028169602272099763 295920042254403408149645)
                  ·
                    refine ⟨110970015845401278056117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 295920042254403408149645 110970015845401278056117)
                    ·
                      rfl

theorem cell22_324170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_324170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324170 prefixEnd_324170 := by exact prefixLift 324170
  have htrace : WordTrace (prefixWord ++ tailWord_324170) baseStart_324170 baseEnd_324170 := by
    simpa [prefixWord, tailWord_324170, baseEnd_324170] using wordTrace_append hprefix tailTrace_324170
  have hstable : (prefixWord ++ tailWord_324170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324170).length < 2 ^ (prefixWord ++ tailWord_324170).sum := by decide
  have hdescent : baseEnd_324170 < baseStart_324170 := by decide
  rcases family_descends (prefixWord ++ tailWord_324170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324181 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_324181 : Nat := 118140960795 + 324181 * 2 ^ 59
def prefixEnd_324181 : Nat := 4983230072969 + 3 ^ 40 * 324181 * 2
def baseEnd_324181 : Nat := 110973781370200916031083

theorem tailTrace_324181 : CollatzResearch.WordTrace tailWord_324181 prefixEnd_324181 110973781370200916031083 := by
  unfold tailWord_324181
  simp only [CollatzResearch.WordTrace]
  refine ⟨11823852438555077552020397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7882568292370051701346931 11823852438555077552020397)
  ·
    refine ⟨4433944664458154082007649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11823852438555077552020397 4433944664458154082007649)
    ·
      refine ⟨3325458498343615561505737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4433944664458154082007649 3325458498343615561505737)
      ·
        refine ⟨2494093873757711671129303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3325458498343615561505737 2494093873757711671129303)
        ·
          refine ⟨3741140810636567506693955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2494093873757711671129303 3741140810636567506693955)
          ·
            refine ⟨5611711215954851260040933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3741140810636567506693955 5611711215954851260040933)
            ·
              refine ⟨1052195852991534611257675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5611711215954851260040933 1052195852991534611257675)
              ·
                refine ⟨1578293779487301916886513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052195852991534611257675 1578293779487301916886513)
                ·
                  refine ⟨1183720334615476437664885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1578293779487301916886513 1183720334615476437664885)
                  ·
                    refine ⟨110973781370200916031083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1183720334615476437664885 110973781370200916031083)
                    ·
                      rfl

theorem cell22_324181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_324181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324181 prefixEnd_324181 := by exact prefixLift 324181
  have htrace : WordTrace (prefixWord ++ tailWord_324181) baseStart_324181 baseEnd_324181 := by
    simpa [prefixWord, tailWord_324181, baseEnd_324181] using wordTrace_append hprefix tailTrace_324181
  have hstable : (prefixWord ++ tailWord_324181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324181).length < 2 ^ (prefixWord ++ tailWord_324181).sum := by decide
  have hdescent : baseEnd_324181 < baseStart_324181 := by decide
  rcases family_descends (prefixWord ++ tailWord_324181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324183 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 5]
def baseStart_324183 : Nat := 118140960795 + 324183 * 2 ^ 59
def prefixEnd_324183 : Nat := 4983230072969 + 3 ^ 40 * 324183 * 2
def baseEnd_324183 : Nat := 36991488670357859160359

theorem tailTrace_324183 : CollatzResearch.WordTrace tailWord_324183 prefixEnd_324183 36991488670357859160359 := by
  unfold tailWord_324183
  simp only [CollatzResearch.WordTrace]
  refine ⟨11823925384547831893593203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7882616923031887929062135 11823925384547831893593203)
  ·
    refine ⟨17735888076821747840389805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11823925384547831893593203 17735888076821747840389805)
    ·
      refine ⟨6650958028808155440146177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17735888076821747840389805 6650958028808155440146177)
      ·
        refine ⟨4988218521606116580109633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6650958028808155440146177 4988218521606116580109633)
        ·
          refine ⟨3741163891204587435082225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4988218521606116580109633 3741163891204587435082225)
          ·
            refine ⟨2805872918403440576311669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3741163891204587435082225 2805872918403440576311669)
            ·
              refine ⟨263050586100322554029219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2805872918403440576311669 263050586100322554029219)
              ·
                refine ⟨394575879150483831043829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263050586100322554029219 394575879150483831043829)
                ·
                  refine ⟨36991488670357859160359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 394575879150483831043829 36991488670357859160359)
                  ·
                    rfl

theorem cell22_324183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 5].length) (baseStart_324183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324183 prefixEnd_324183 := by exact prefixLift 324183
  have htrace : WordTrace (prefixWord ++ tailWord_324183) baseStart_324183 baseEnd_324183 := by
    simpa [prefixWord, tailWord_324183, baseEnd_324183] using wordTrace_append hprefix tailTrace_324183
  have hstable : (prefixWord ++ tailWord_324183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324183).length < 2 ^ (prefixWord ++ tailWord_324183).sum := by decide
  have hdescent : baseEnd_324183 < baseStart_324183 := by decide
  rcases family_descends (prefixWord ++ tailWord_324183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324228 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 6]
def baseStart_324228 : Nat := 118140960795 + 324228 * 2 ^ 59
def prefixEnd_324228 : Nat := 4983230072969 + 3 ^ 40 * 324228 * 2
def baseEnd_324228 : Nat := 36996623476902820035313

theorem tailTrace_324228 : CollatzResearch.WordTrace tailWord_324228 prefixEnd_324228 36996623476902820035313 := by
  unfold tailWord_324228
  simp only [CollatzResearch.WordTrace]
  refine ⟨5912783334692402289490669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7883711112923203052654225 5912783334692402289490669)
  ·
    refine ⟨2217293750509650858559001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5912783334692402289490669 2217293750509650858559001)
    ·
      refine ⟨1662970312882238143919251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2217293750509650858559001 1662970312882238143919251)
      ·
        refine ⟨2494455469323357215878877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1662970312882238143919251 2494455469323357215878877)
        ·
          refine ⟨935420800996258955954579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2494455469323357215878877 935420800996258955954579)
          ·
            refine ⟨1403131201494388433931869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935420800996258955954579 1403131201494388433931869)
            ·
              refine ⟨526174200560395662724451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1403131201494388433931869 526174200560395662724451)
              ·
                refine ⟨789261300840593494086677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526174200560395662724451 789261300840593494086677)
                ·
                  refine ⟨36996623476902820035313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 789261300840593494086677 36996623476902820035313)
                  ·
                    rfl

theorem cell22_324228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_324228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324228 prefixEnd_324228 := by exact prefixLift 324228
  have htrace : WordTrace (prefixWord ++ tailWord_324228) baseStart_324228 baseEnd_324228 := by
    simpa [prefixWord, tailWord_324228, baseEnd_324228] using wordTrace_append hprefix tailTrace_324228
  have hstable : (prefixWord ++ tailWord_324228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324228).length < 2 ^ (prefixWord ++ tailWord_324228).sum := by decide
  have hdescent : baseEnd_324228 < baseStart_324228 := by decide
  rcases family_descends (prefixWord ++ tailWord_324228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324243 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 2, 3]
def baseStart_324243 : Nat := 118140960795 + 324243 * 2 ^ 59
def prefixEnd_324243 : Nat := 4983230072969 + 3 ^ 40 * 324243 * 2
def baseEnd_324243 : Nat := 110995005237253420980893

theorem tailTrace_324243 : CollatzResearch.WordTrace tailWord_324243 prefixEnd_324243 110995005237253420980893 := by
  unfold tailWord_324243
  simp only [CollatzResearch.WordTrace]
  refine ⟨11826113764330462140777383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7884075842886974760518255 11826113764330462140777383)
  ·
    refine ⟨17739170646495693211166075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11826113764330462140777383 17739170646495693211166075)
    ·
      refine ⟨26608755969743539816749113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17739170646495693211166075 26608755969743539816749113)
      ·
        refine ⟨19956566977307654862561835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26608755969743539816749113 19956566977307654862561835)
        ·
          refine ⟨29934850465961482293842753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19956566977307654862561835 29934850465961482293842753)
          ·
            refine ⟨22451137849471111720382065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29934850465961482293842753 22451137849471111720382065)
            ·
              refine ⟨16838353387103333790286549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22451137849471111720382065 16838353387103333790286549)
              ·
                refine ⟨394648907510234385709841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16838353387103333790286549 394648907510234385709841)
                ·
                  refine ⟨295986680632675789282381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394648907510234385709841 295986680632675789282381)
                  ·
                    refine ⟨110995005237253420980893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 295986680632675789282381 110995005237253420980893)
                    ·
                      rfl

theorem cell22_324243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 3].length) (baseStart_324243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324243 prefixEnd_324243 := by exact prefixLift 324243
  have htrace : WordTrace (prefixWord ++ tailWord_324243) baseStart_324243 baseEnd_324243 := by
    simpa [prefixWord, tailWord_324243, baseEnd_324243] using wordTrace_append hprefix tailTrace_324243
  have hstable : (prefixWord ++ tailWord_324243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324243).length < 2 ^ (prefixWord ++ tailWord_324243).sum := by decide
  have hdescent : baseEnd_324243 < baseStart_324243 := by decide
  rcases family_descends (prefixWord ++ tailWord_324243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324273 : List Nat := [1, 2, 2, 6, 1, 10]
def baseStart_324273 : Nat := 118140960795 + 324273 * 2 ^ 59
def prefixEnd_324273 : Nat := 4983230072969 + 3 ^ 40 * 324273 * 2
def baseEnd_324273 : Nat := 1370435491979547441121

theorem tailTrace_324273 : CollatzResearch.WordTrace tailWord_324273 prefixEnd_324273 1370435491979547441121 := by
  unfold tailWord_324273
  simp only [CollatzResearch.WordTrace]
  refine ⟨11827207954221777264369473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7884805302814518176246315 11827207954221777264369473)
  ·
    refine ⟨8870405965666332948277105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11827207954221777264369473 8870405965666332948277105)
    ·
      refine ⟨6652804474249749711207829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8870405965666332948277105 6652804474249749711207829)
      ·
        refine ⟨311850209730457017712867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6652804474249749711207829 311850209730457017712867)
        ·
          refine ⟨467775314595685526569301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311850209730457017712867 467775314595685526569301)
          ·
            refine ⟨1370435491979547441121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 467775314595685526569301 1370435491979547441121)
            ·
              rfl

theorem cell22_324273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 10].length) (baseStart_324273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324273 prefixEnd_324273 := by exact prefixLift 324273
  have htrace : WordTrace (prefixWord ++ tailWord_324273) baseStart_324273 baseEnd_324273 := by
    simpa [prefixWord, tailWord_324273, baseEnd_324273] using wordTrace_append hprefix tailTrace_324273
  have hstable : (prefixWord ++ tailWord_324273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324273).length < 2 ^ (prefixWord ++ tailWord_324273).sum := by decide
  have hdescent : baseEnd_324273 < baseStart_324273 := by decide
  rcases family_descends (prefixWord ++ tailWord_324273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324277 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 2, 3]
def baseStart_324277 : Nat := 118140960795 + 324277 * 2 ^ 59
def prefixEnd_324277 : Nat := 4983230072969 + 3 ^ 40 * 324277 * 2
def baseEnd_324277 : Nat := 111006644132088665630789

theorem tailTrace_324277 : CollatzResearch.WordTrace tailWord_324277 prefixEnd_324277 111006644132088665630789 := by
  unfold tailWord_324277
  simp only [CollatzResearch.WordTrace]
  refine ⟨11827353846207285947515085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7884902564138190631676723 11827353846207285947515085)
  ·
    refine ⟨4435257692327732230318157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11827353846207285947515085 4435257692327732230318157)
    ·
      refine ⟨1663221634622899586369309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4435257692327732230318157 1663221634622899586369309)
      ·
        refine ⟨623708112983587344888491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1663221634622899586369309 623708112983587344888491)
        ·
          refine ⟨935562169475381017332737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623708112983587344888491 935562169475381017332737)
          ·
            refine ⟨701671627106535762999553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 935562169475381017332737 701671627106535762999553)
            ·
              refine ⟨526253720329901822249665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701671627106535762999553 526253720329901822249665)
              ·
                refine ⟨394690290247426366687249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526253720329901822249665 394690290247426366687249)
                ·
                  refine ⟨296017717685569775015437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 394690290247426366687249 296017717685569775015437)
                  ·
                    refine ⟨111006644132088665630789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296017717685569775015437 111006644132088665630789)
                    ·
                      rfl

theorem cell22_324277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_324277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324277 prefixEnd_324277 := by exact prefixLift 324277
  have htrace : WordTrace (prefixWord ++ tailWord_324277) baseStart_324277 baseEnd_324277 := by
    simpa [prefixWord, tailWord_324277, baseEnd_324277] using wordTrace_append hprefix tailTrace_324277
  have hstable : (prefixWord ++ tailWord_324277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324277).length < 2 ^ (prefixWord ++ tailWord_324277).sum := by decide
  have hdescent : baseEnd_324277 < baseStart_324277 := by decide
  rcases family_descends (prefixWord ++ tailWord_324277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324279 : List Nat := [1, 1, 3, 1, 7, 1, 2, 2, 4]
def baseStart_324279 : Nat := 118140960795 + 324279 * 2 ^ 59
def prefixEnd_324279 : Nat := 4983230072969 + 3 ^ 40 * 324279 * 2
def baseEnd_324279 : Nat := 37002442924320442360261

theorem tailTrace_324279 : CollatzResearch.WordTrace tailWord_324279 prefixEnd_324279 37002442924320442360261 := by
  unfold tailWord_324279
  simp only [CollatzResearch.WordTrace]
  refine ⟨11827426792200040289087891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7884951194800026859391927 11827426792200040289087891)
  ·
    refine ⟨17741140188300060433631837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11827426792200040289087891 17741140188300060433631837)
    ·
      refine ⟨6652927570612522662611939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17741140188300060433631837 6652927570612522662611939)
      ·
        refine ⟨9979391355918783993917909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6652927570612522662611939 9979391355918783993917909)
        ·
          refine ⟨233891984904346499857451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9979391355918783993917909 233891984904346499857451)
          ·
            refine ⟨350837977356519749786177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233891984904346499857451 350837977356519749786177)
            ·
              refine ⟨263128483017389812339633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350837977356519749786177 263128483017389812339633)
              ·
                refine ⟨197346362263042359254725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263128483017389812339633 197346362263042359254725)
                ·
                  refine ⟨37002442924320442360261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197346362263042359254725 37002442924320442360261)
                  ·
                    rfl

theorem cell22_324279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 4].length) (baseStart_324279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324279 prefixEnd_324279 := by exact prefixLift 324279
  have htrace : WordTrace (prefixWord ++ tailWord_324279) baseStart_324279 baseEnd_324279 := by
    simpa [prefixWord, tailWord_324279, baseEnd_324279] using wordTrace_append hprefix tailTrace_324279
  have hstable : (prefixWord ++ tailWord_324279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324279).length < 2 ^ (prefixWord ++ tailWord_324279).sum := by decide
  have hdescent : baseEnd_324279 < baseStart_324279 := by decide
  rcases family_descends (prefixWord ++ tailWord_324279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324294 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_324294 : Nat := 118140960795 + 324294 * 2 ^ 59
def prefixEnd_324294 : Nat := 4983230072969 + 3 ^ 40 * 324294 * 2
def baseEnd_324294 : Nat := 111012463579506287955737

theorem tailTrace_324294 : CollatzResearch.WordTrace tailWord_324294 prefixEnd_324294 111012463579506287955737 := by
  unfold tailWord_324294
  simp only [CollatzResearch.WordTrace]
  refine ⟨369624183973303057840123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7885315924763798567255957 369624183973303057840123)
  ·
    refine ⟨554436275959954586760185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 369624183973303057840123 554436275959954586760185)
    ·
      refine ⟨415827206969965940070139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 554436275959954586760185 415827206969965940070139)
      ·
        refine ⟨623740810454948910105209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415827206969965940070139 623740810454948910105209)
        ·
          refine ⟨467805607841211682578907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623740810454948910105209 467805607841211682578907)
          ·
            refine ⟨701708411761817523868361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467805607841211682578907 701708411761817523868361)
            ·
              refine ⟨526281308821363142901271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701708411761817523868361 526281308821363142901271)
              ·
                refine ⟨789421963232044714351907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526281308821363142901271 789421963232044714351907)
                ·
                  refine ⟨1184132944848067071527861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789421963232044714351907 1184132944848067071527861)
                  ·
                    refine ⟨111012463579506287955737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1184132944848067071527861 111012463579506287955737)
                    ·
                      rfl

theorem cell22_324294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_324294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324294 prefixEnd_324294 := by exact prefixLift 324294
  have htrace : WordTrace (prefixWord ++ tailWord_324294) baseStart_324294 baseEnd_324294 := by
    simpa [prefixWord, tailWord_324294, baseEnd_324294] using wordTrace_append hprefix tailTrace_324294
  have hstable : (prefixWord ++ tailWord_324294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324294).length < 2 ^ (prefixWord ++ tailWord_324294).sum := by decide
  have hdescent : baseEnd_324294 < baseStart_324294 := by decide
  rcases family_descends (prefixWord ++ tailWord_324294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324309 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 2, 4]
def baseStart_324309 : Nat := 118140960795 + 324309 * 2 ^ 59
def prefixEnd_324309 : Nat := 4983230072969 + 3 ^ 40 * 324309 * 2
def baseEnd_324309 : Nat := 111017598386051248830691

theorem tailTrace_324309 : CollatzResearch.WordTrace tailWord_324309 prefixEnd_324309 111017598386051248830691 := by
  unfold tailWord_324309
  simp only [CollatzResearch.WordTrace]
  refine ⟨11828520982091355412679981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7885680654727570275119987 11828520982091355412679981)
  ·
    refine ⟨4435695368284258279754993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11828520982091355412679981 4435695368284258279754993)
    ·
      refine ⟨3326771526213193709816245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4435695368284258279754993 3326771526213193709816245)
      ·
        refine ⟨311884830582486910295273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3326771526213193709816245 311884830582486910295273)
        ·
          refine ⟨233913622936865182721455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311884830582486910295273 233913622936865182721455)
          ·
            refine ⟨350870434405297774082183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233913622936865182721455 350870434405297774082183)
            ·
              refine ⟨526305651607946661123275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350870434405297774082183 526305651607946661123275)
              ·
                refine ⟨789458477411919991684913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526305651607946661123275 789458477411919991684913)
                ·
                  refine ⟨592093858058939993763685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 789458477411919991684913 592093858058939993763685)
                  ·
                    refine ⟨111017598386051248830691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 592093858058939993763685 111017598386051248830691)
                    ·
                      rfl

theorem cell22_324309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_324309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324309 prefixEnd_324309 := by exact prefixLift 324309
  have htrace : WordTrace (prefixWord ++ tailWord_324309) baseStart_324309 baseEnd_324309 := by
    simpa [prefixWord, tailWord_324309, baseEnd_324309] using wordTrace_append hprefix tailTrace_324309
  have hstable : (prefixWord ++ tailWord_324309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324309).length < 2 ^ (prefixWord ++ tailWord_324309).sum := by decide
  have hdescent : baseEnd_324309 < baseStart_324309 := by decide
  rcases family_descends (prefixWord ++ tailWord_324309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324333 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_324333 : Nat := 118140960795 + 324333 * 2 ^ 59
def prefixEnd_324333 : Nat := 4983230072969 + 3 ^ 40 * 324333 * 2
def baseEnd_324333 : Nat := 111025814076523186230617

theorem tailTrace_324333 : CollatzResearch.WordTrace tailWord_324333 prefixEnd_324333 111025814076523186230617 := by
  unfold tailWord_324333
  simp only [CollatzResearch.WordTrace]
  refine ⟨11829396334004407511553653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7886264222669605007702435 11829396334004407511553653)
  ·
    refine ⟨1109005906312913204208155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11829396334004407511553653 1109005906312913204208155)
    ·
      refine ⟨1663508859469369806312233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109005906312913204208155 1663508859469369806312233)
      ·
        refine ⟨1247631644602027354734175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1663508859469369806312233 1247631644602027354734175)
        ·
          refine ⟨1871447466903041032101263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1247631644602027354734175 1871447466903041032101263)
          ·
            refine ⟨2807171200354561548151895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871447466903041032101263 2807171200354561548151895)
            ·
              refine ⟨4210756800531842322227843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2807171200354561548151895 4210756800531842322227843)
              ·
                refine ⟨6316135200797763483341765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4210756800531842322227843 6316135200797763483341765)
                ·
                  refine ⟨1184275350149580653126581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6316135200797763483341765 1184275350149580653126581)
                  ·
                    refine ⟨111025814076523186230617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1184275350149580653126581 111025814076523186230617)
                    ·
                      rfl

theorem cell22_324333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_324333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324333 prefixEnd_324333 := by exact prefixLift 324333
  have htrace : WordTrace (prefixWord ++ tailWord_324333) baseStart_324333 baseEnd_324333 := by
    simpa [prefixWord, tailWord_324333, baseEnd_324333] using wordTrace_append hprefix tailTrace_324333
  have hstable : (prefixWord ++ tailWord_324333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324333).length < 2 ^ (prefixWord ++ tailWord_324333).sum := by decide
  have hdescent : baseEnd_324333 < baseStart_324333 := by decide
  rcases family_descends (prefixWord ++ tailWord_324333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324335 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 5]
def baseStart_324335 : Nat := 118140960795 + 324335 * 2 ^ 59
def prefixEnd_324335 : Nat := 4983230072969 + 3 ^ 40 * 324335 * 2
def baseEnd_324335 : Nat := 37008832905798615893537

theorem tailTrace_324335 : CollatzResearch.WordTrace tailWord_324335 prefixEnd_324335 37008832905798615893537 := by
  unfold tailWord_324335
  simp only [CollatzResearch.WordTrace]
  refine ⟨11829469279997161853126459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7886312853331441235417639 11829469279997161853126459)
  ·
    refine ⟨17744203919995742779689689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11829469279997161853126459 17744203919995742779689689)
    ·
      refine ⟨13308152939996807084767267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17744203919995742779689689 13308152939996807084767267)
      ·
        refine ⟨19962229409995210627150901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13308152939996807084767267 19962229409995210627150901)
        ·
          refine ⟨1871459007187050996295397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19962229409995210627150901 1871459007187050996295397)
          ·
            refine ⟨350898563847572061805387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1871459007187050996295397 350898563847572061805387)
            ·
              refine ⟨526347845771358092708081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350898563847572061805387 526347845771358092708081)
              ·
                refine ⟨394760884328518569531061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526347845771358092708081 394760884328518569531061)
                ·
                  refine ⟨37008832905798615893537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 394760884328518569531061 37008832905798615893537)
                  ·
                    rfl

theorem cell22_324335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 5].length) (baseStart_324335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324335 prefixEnd_324335 := by exact prefixLift 324335
  have htrace : WordTrace (prefixWord ++ tailWord_324335) baseStart_324335 baseEnd_324335 := by
    simpa [prefixWord, tailWord_324335, baseEnd_324335] using wordTrace_append hprefix tailTrace_324335
  have hstable : (prefixWord ++ tailWord_324335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324335).length < 2 ^ (prefixWord ++ tailWord_324335).sum := by decide
  have hdescent : baseEnd_324335 < baseStart_324335 := by decide
  rcases family_descends (prefixWord ++ tailWord_324335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324350 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_324350 : Nat := 118140960795 + 324350 * 2 ^ 59
def prefixEnd_324350 : Nat := 4983230072969 + 3 ^ 40 * 324350 * 2
def baseEnd_324350 : Nat := 111031633523940808555565

theorem tailTrace_324350 : CollatzResearch.WordTrace tailWord_324350 prefixEnd_324350 111031633523940808555565 := by
  unfold tailWord_324350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478752046867852426865313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7886677583295212943281669 1478752046867852426865313)
  ·
    refine ⟨1109064035150889320148985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1478752046867852426865313 1109064035150889320148985)
    ·
      refine ⟨831798026363166990111739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1109064035150889320148985 831798026363166990111739)
      ·
        refine ⟨1247697039544750485167609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831798026363166990111739 1247697039544750485167609)
        ·
          refine ⟨935772779658562863875707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1247697039544750485167609 935772779658562863875707)
          ·
            refine ⟨1403659169487844295813561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935772779658562863875707 1403659169487844295813561)
            ·
              refine ⟨1052744377115883221860171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403659169487844295813561 1052744377115883221860171)
              ·
                refine ⟨1579116565673824832790257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052744377115883221860171 1579116565673824832790257)
                ·
                  refine ⟨1184337424255368624592693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1579116565673824832790257 1184337424255368624592693)
                  ·
                    refine ⟨111031633523940808555565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1184337424255368624592693 111031633523940808555565)
                    ·
                      rfl

theorem cell22_324350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_324350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324350 prefixEnd_324350 := by exact prefixLift 324350
  have htrace : WordTrace (prefixWord ++ tailWord_324350) baseStart_324350 baseEnd_324350 := by
    simpa [prefixWord, tailWord_324350, baseEnd_324350] using wordTrace_append hprefix tailTrace_324350
  have hstable : (prefixWord ++ tailWord_324350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324350).length < 2 ^ (prefixWord ++ tailWord_324350).sum := by decide
  have hdescent : baseEnd_324350 < baseStart_324350 := by decide
  rcases family_descends (prefixWord ++ tailWord_324350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324378 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_324378 : Nat := 118140960795 + 324378 * 2 ^ 59
def prefixEnd_324378 : Nat := 4983230072969 + 3 ^ 40 * 324378 * 2
def baseEnd_324378 : Nat := 111041218496158068855479

theorem tailTrace_324378 : CollatzResearch.WordTrace tailWord_324378 prefixEnd_324378 111041218496158068855479 := by
  unfold tailWord_324378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2957759404710345049235447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7887358412560920131294525 2957759404710345049235447)
  ·
    refine ⟨4436639107065517573853171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2957759404710345049235447 4436639107065517573853171)
    ·
      refine ⟨6654958660598276360779757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4436639107065517573853171 6654958660598276360779757)
      ·
        refine ⟨2495609497724353635292409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6654958660598276360779757 2495609497724353635292409)
        ·
          refine ⟨1871707123293265226469307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2495609497724353635292409 1871707123293265226469307)
          ·
            refine ⟨2807560684939897839703961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871707123293265226469307 2807560684939897839703961)
            ·
              refine ⟨2105670513704923379777971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2807560684939897839703961 2105670513704923379777971)
              ·
                refine ⟨3158505770557385069666957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2105670513704923379777971 3158505770557385069666957)
                ·
                  refine ⟨1184439663959019401125109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3158505770557385069666957 1184439663959019401125109)
                  ·
                    refine ⟨111041218496158068855479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1184439663959019401125109 111041218496158068855479)
                    ·
                      rfl

theorem cell22_324378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_324378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324378 prefixEnd_324378 := by exact prefixLift 324378
  have htrace : WordTrace (prefixWord ++ tailWord_324378) baseStart_324378 baseEnd_324378 := by
    simpa [prefixWord, tailWord_324378, baseEnd_324378] using wordTrace_append hprefix tailTrace_324378
  have hstable : (prefixWord ++ tailWord_324378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324378).length < 2 ^ (prefixWord ++ tailWord_324378).sum := by decide
  have hdescent : baseEnd_324378 < baseStart_324378 := by decide
  rcases family_descends (prefixWord ++ tailWord_324378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324393 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 2, 4]
def baseStart_324393 : Nat := 118140960795 + 324393 * 2 ^ 59
def prefixEnd_324393 : Nat := 4983230072969 + 3 ^ 40 * 324393 * 2
def baseEnd_324393 : Nat := 111046353302703029730433

theorem tailTrace_324393 : CollatzResearch.WordTrace tailWord_324393 prefixEnd_324393 111046353302703029730433 := by
  unfold tailWord_324393
  simp only [CollatzResearch.WordTrace]
  refine ⟨11831584713787037758737833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7887723142524691839158555 11831584713787037758737833)
  ·
    refine ⟨8873688535340278319053375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11831584713787037758737833 8873688535340278319053375)
    ·
      refine ⟨13310532803010417478580063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8873688535340278319053375 13310532803010417478580063)
      ·
        refine ⟨19965799204515626217870095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13310532803010417478580063 19965799204515626217870095)
        ·
          refine ⟨29948698806773439326805143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19965799204515626217870095 29948698806773439326805143)
          ·
            refine ⟨44923048210160158990207715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29948698806773439326805143 44923048210160158990207715)
            ·
              refine ⟨67384572315240238485311573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44923048210160158990207715 67384572315240238485311573)
              ·
                refine ⟨789662956819221544749745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 67384572315240238485311573 789662956819221544749745)
                ·
                  refine ⟨592247217614416158562309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 789662956819221544749745 592247217614416158562309)
                  ·
                    refine ⟨111046353302703029730433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 592247217614416158562309 111046353302703029730433)
                    ·
                      rfl

theorem cell22_324393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_324393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324393 prefixEnd_324393 := by exact prefixLift 324393
  have htrace : WordTrace (prefixWord ++ tailWord_324393) baseStart_324393 baseEnd_324393 := by
    simpa [prefixWord, tailWord_324393, baseEnd_324393] using wordTrace_append hprefix tailTrace_324393
  have hstable : (prefixWord ++ tailWord_324393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324393).length < 2 ^ (prefixWord ++ tailWord_324393).sum := by decide
  have hdescent : baseEnd_324393 < baseStart_324393 := by decide
  rcases family_descends (prefixWord ++ tailWord_324393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324408 : List Nat := [2, 1, 2, 1, 3, 2, 4, 7]
def baseStart_324408 : Nat := 118140960795 + 324408 * 2 ^ 59
def prefixEnd_324408 : Nat := 4983230072969 + 3 ^ 40 * 324408 * 2
def baseEnd_324408 : Nat := 12339054234360887845043

theorem tailTrace_324408 : CollatzResearch.WordTrace tailWord_324408 prefixEnd_324408 12339054234360887845043 := by
  unfold tailWord_324408
  simp only [CollatzResearch.WordTrace]
  refine ⟨5916065904366347660266939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7888087872488463547022585 5916065904366347660266939)
  ·
    refine ⟨8874098856549521490400409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5916065904366347660266939 8874098856549521490400409)
    ·
      refine ⟨6655574142412141117800307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8874098856549521490400409 6655574142412141117800307)
      ·
        refine ⟨9983361213618211676700461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6655574142412141117800307 9983361213618211676700461)
        ·
          refine ⟨3743760455106829378762673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9983361213618211676700461 3743760455106829378762673)
          ·
            refine ⟨2807820341330122034072005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3743760455106829378762673 2807820341330122034072005)
            ·
              refine ⟨526466313999397881388501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2807820341330122034072005 526466313999397881388501)
              ·
                refine ⟨12339054234360887845043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 526466313999397881388501 12339054234360887845043)
                ·
                  rfl

theorem cell22_324408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 7].length) (baseStart_324408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324408 prefixEnd_324408 := by exact prefixLift 324408
  have htrace : WordTrace (prefixWord ++ tailWord_324408) baseStart_324408 baseEnd_324408 := by
    simpa [prefixWord, tailWord_324408, baseEnd_324408] using wordTrace_append hprefix tailTrace_324408
  have hstable : (prefixWord ++ tailWord_324408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324408).length < 2 ^ (prefixWord ++ tailWord_324408).sum := by decide
  have hdescent : baseEnd_324408 < baseStart_324408 := by decide
  rcases family_descends (prefixWord ++ tailWord_324408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324453 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 7]
def baseStart_324453 : Nat := 118140960795 + 324453 * 2 ^ 59
def prefixEnd_324453 : Nat := 4983230072969 + 3 ^ 40 * 324453 * 2
def baseEnd_324453 : Nat := 37022297509627624410083

theorem tailTrace_324453 : CollatzResearch.WordTrace tailWord_324453 prefixEnd_324453 37022297509627624410083 := by
  unfold tailWord_324453
  simp only [CollatzResearch.WordTrace]
  refine ⟨11833773093569668005922013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7889182062379778670614675 11833773093569668005922013)
  ·
    refine ⟨4437664910088625502220755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11833773093569668005922013 4437664910088625502220755)
    ·
      refine ⟨6656497365132938253331133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4437664910088625502220755 6656497365132938253331133)
      ·
        refine ⟨2496186511924851844999175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6656497365132938253331133 2496186511924851844999175)
        ·
          refine ⟨3744279767887277767498763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496186511924851844999175 3744279767887277767498763)
          ·
            refine ⟨5616419651830916651248145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3744279767887277767498763 5616419651830916651248145)
            ·
              refine ⟨4212314738873187488436109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5616419651830916651248145 4212314738873187488436109)
              ·
                refine ⟨1579618027077445308163541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4212314738873187488436109 1579618027077445308163541)
                ·
                  refine ⟨37022297509627624410083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1579618027077445308163541 37022297509627624410083)
                  ·
                    rfl

theorem cell22_324453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_324453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324453 prefixEnd_324453 := by exact prefixLift 324453
  have htrace : WordTrace (prefixWord ++ tailWord_324453) baseStart_324453 baseEnd_324453 := by
    simpa [prefixWord, tailWord_324453, baseEnd_324453] using wordTrace_append hprefix tailTrace_324453
  have hstable : (prefixWord ++ tailWord_324453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324453).length < 2 ^ (prefixWord ++ tailWord_324453).sum := by decide
  have hdescent : baseEnd_324453 < baseStart_324453 := by decide
  rcases family_descends (prefixWord ++ tailWord_324453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324562 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_324562 : Nat := 118140960795 + 324562 * 2 ^ 59
def prefixEnd_324562 : Nat := 4983230072969 + 3 ^ 40 * 324562 * 2
def baseEnd_324562 : Nat := 111104205456442922254915

theorem tailTrace_324562 : CollatzResearch.WordTrace tailWord_324562 prefixEnd_324562 111104205456442922254915 := by
  unfold tailWord_324562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959437162543694905409985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7891832433449853081093293 2959437162543694905409985)
  ·
    refine ⟨2219577871907771179057489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2959437162543694905409985 2219577871907771179057489)
    ·
      refine ⟨1664683403930828384293117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2219577871907771179057489 1664683403930828384293117)
      ·
        refine ⟨624256276474060644109919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1664683403930828384293117 624256276474060644109919)
        ·
          refine ⟨936384414711090966164879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624256276474060644109919 936384414711090966164879)
          ·
            refine ⟨1404576622066636449247319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936384414711090966164879 1404576622066636449247319)
            ·
              refine ⟨2106864933099954673870979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404576622066636449247319 2106864933099954673870979)
              ·
                refine ⟨3160297399649932010806469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106864933099954673870979 3160297399649932010806469)
                ·
                  refine ⟨592555762434362252026213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3160297399649932010806469 592555762434362252026213)
                  ·
                    refine ⟨111104205456442922254915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 592555762434362252026213 111104205456442922254915)
                    ·
                      rfl

theorem cell22_324562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_324562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324562 prefixEnd_324562 := by exact prefixLift 324562
  have htrace : WordTrace (prefixWord ++ tailWord_324562) baseStart_324562 baseEnd_324562 := by
    simpa [prefixWord, tailWord_324562, baseEnd_324562] using wordTrace_append hprefix tailTrace_324562
  have hstable : (prefixWord ++ tailWord_324562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324562).length < 2 ^ (prefixWord ++ tailWord_324562).sum := by decide
  have hdescent : baseEnd_324562 < baseStart_324562 := by decide
  rcases family_descends (prefixWord ++ tailWord_324562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324581 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 2, 3]
def baseStart_324581 : Nat := 118140960795 + 324581 * 2 ^ 59
def prefixEnd_324581 : Nat := 4983230072969 + 3 ^ 40 * 324581 * 2
def baseEnd_324581 : Nat := 111110709544733206029857

theorem tailTrace_324581 : CollatzResearch.WordTrace tailWord_324581 prefixEnd_324581 111110709544733206029857 := by
  unfold tailWord_324581
  simp only [CollatzResearch.WordTrace]
  refine ⟨11838441637105945866581597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7892294424737297244387731 11838441637105945866581597)
  ·
    refine ⟨4439415613914729699968099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11838441637105945866581597 4439415613914729699968099)
    ·
      refine ⟨6659123420872094549952149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4439415613914729699968099 6659123420872094549952149)
      ·
        refine ⟨312146410353379432029007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6659123420872094549952149 312146410353379432029007)
        ·
          refine ⟨468219615530069148043511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312146410353379432029007 468219615530069148043511)
          ·
            refine ⟨702329423295103722065267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468219615530069148043511 702329423295103722065267)
            ·
              refine ⟨1053494134942655583097901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702329423295103722065267 1053494134942655583097901)
              ·
                refine ⟨395060300603495843661713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1053494134942655583097901 395060300603495843661713)
                ·
                  refine ⟨296295225452621882746285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395060300603495843661713 296295225452621882746285)
                  ·
                    refine ⟨111110709544733206029857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296295225452621882746285 111110709544733206029857)
                    ·
                      rfl

theorem cell22_324581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_324581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324581 prefixEnd_324581 := by exact prefixLift 324581
  have htrace : WordTrace (prefixWord ++ tailWord_324581) baseStart_324581 baseEnd_324581 := by
    simpa [prefixWord, tailWord_324581, baseEnd_324581] using wordTrace_append hprefix tailTrace_324581
  have hstable : (prefixWord ++ tailWord_324581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324581).length < 2 ^ (prefixWord ++ tailWord_324581).sum := by decide
  have hdescent : baseEnd_324581 < baseStart_324581 := by decide
  rcases family_descends (prefixWord ++ tailWord_324581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324622 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_324622 : Nat := 118140960795 + 324622 * 2 ^ 59
def prefixEnd_324622 : Nat := 4983230072969 + 3 ^ 40 * 324622 * 2
def baseEnd_324622 : Nat := 37041581560874255251577

theorem tailTrace_324622 : CollatzResearch.WordTrace tailWord_324622 prefixEnd_324622 37041581560874255251577 := by
  unfold tailWord_324622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479992128744676233603015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7893291353304939912549413 1479992128744676233603015)
  ·
    refine ⟨2219988193117014350404523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1479992128744676233603015 2219988193117014350404523)
    ·
      refine ⟨3329982289675521525606785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2219988193117014350404523 3329982289675521525606785)
      ·
        refine ⟨2497486717256641144205089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3329982289675521525606785 2497486717256641144205089)
        ·
          refine ⟨1873115037942480858153817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2497486717256641144205089 1873115037942480858153817)
          ·
            refine ⟨1404836278456860643615363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1873115037942480858153817 1404836278456860643615363)
            ·
              refine ⟨2107254417685290965423045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404836278456860643615363 2107254417685290965423045)
              ·
                refine ⟨395110203315992056016821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2107254417685290965423045 395110203315992056016821)
                ·
                  refine ⟨37041581560874255251577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 395110203315992056016821 37041581560874255251577)
                  ·
                    rfl

theorem cell22_324622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_324622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324622 prefixEnd_324622 := by exact prefixLift 324622
  have htrace : WordTrace (prefixWord ++ tailWord_324622) baseStart_324622 baseEnd_324622 := by
    simpa [prefixWord, tailWord_324622, baseEnd_324622] using wordTrace_append hprefix tailTrace_324622
  have hstable : (prefixWord ++ tailWord_324622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324622).length < 2 ^ (prefixWord ++ tailWord_324622).sum := by decide
  have hdescent : baseEnd_324622 < baseStart_324622 := by decide
  rcases family_descends (prefixWord ++ tailWord_324622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324652 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_324652 : Nat := 118140960795 + 324652 * 2 ^ 59
def prefixEnd_324652 : Nat := 4983230072969 + 3 ^ 40 * 324652 * 2
def baseEnd_324652 : Nat := 111135014295712687504639

theorem tailTrace_324652 : CollatzResearch.WordTrace tailWord_324652 prefixEnd_324652 111135014295712687504639 := by
  unfold tailWord_324652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5920515609924362496208105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7894020813232483328277473 5920515609924362496208105)
  ·
    refine ⟨4440386707443271872156079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5920515609924362496208105 4440386707443271872156079)
    ·
      refine ⟨6660580061164907808234119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4440386707443271872156079 6660580061164907808234119)
      ·
        refine ⟨9990870091747361712351179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6660580061164907808234119 9990870091747361712351179)
        ·
          refine ⟨14986305137621042568526769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9990870091747361712351179 14986305137621042568526769)
          ·
            refine ⟨11239728853215781926395077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14986305137621042568526769 11239728853215781926395077)
            ·
              refine ⟨2107449159977959111199077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11239728853215781926395077 2107449159977959111199077)
              ·
                refine ⟨395146717495867333349827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2107449159977959111199077 395146717495867333349827)
                ·
                  refine ⟨592720076243801000024741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395146717495867333349827 592720076243801000024741)
                  ·
                    refine ⟨111135014295712687504639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 592720076243801000024741 111135014295712687504639)
                    ·
                      rfl

theorem cell22_324652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_324652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324652 prefixEnd_324652 := by exact prefixLift 324652
  have htrace : WordTrace (prefixWord ++ tailWord_324652) baseStart_324652 baseEnd_324652 := by
    simpa [prefixWord, tailWord_324652, baseEnd_324652] using wordTrace_append hprefix tailTrace_324652
  have hstable : (prefixWord ++ tailWord_324652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324652).length < 2 ^ (prefixWord ++ tailWord_324652).sum := by decide
  have hdescent : baseEnd_324652 < baseStart_324652 := by decide
  rcases family_descends (prefixWord ++ tailWord_324652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324669 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_324669 : Nat := 118140960795 + 324669 * 2 ^ 59
def prefixEnd_324669 : Nat := 4983230072969 + 3 ^ 40 * 324669 * 2
def baseEnd_324669 : Nat := 111140833743130309829587

theorem tailTrace_324669 : CollatzResearch.WordTrace tailWord_324669 prefixEnd_324669 111140833743130309829587 := by
  unfold tailWord_324669
  simp only [CollatzResearch.WordTrace]
  refine ⟨11841651260787136895785061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7894434173858091263856707 11841651260787136895785061)
  ·
    refine ⟨2220309611397588167959699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11841651260787136895785061 2220309611397588167959699)
    ·
      refine ⟨3330464417096382251939549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2220309611397588167959699 3330464417096382251939549)
      ·
        refine ⟨1248924156411143344477331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3330464417096382251939549 1248924156411143344477331)
        ·
          refine ⟨1873386234616715016715997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248924156411143344477331 1873386234616715016715997)
          ·
            refine ⟨702519837981268131268499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1873386234616715016715997 702519837981268131268499)
            ·
              refine ⟨1053779756971902196902749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702519837981268131268499 1053779756971902196902749)
              ·
                refine ⟨395167408864463323838531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1053779756971902196902749 395167408864463323838531)
                ·
                  refine ⟨592751113296694985757797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395167408864463323838531 592751113296694985757797)
                  ·
                    refine ⟨111140833743130309829587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 592751113296694985757797 111140833743130309829587)
                    ·
                      rfl

theorem cell22_324669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_324669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324669 prefixEnd_324669 := by exact prefixLift 324669
  have htrace : WordTrace (prefixWord ++ tailWord_324669) baseStart_324669 baseEnd_324669 := by
    simpa [prefixWord, tailWord_324669, baseEnd_324669] using wordTrace_append hprefix tailTrace_324669
  have hstable : (prefixWord ++ tailWord_324669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324669).length < 2 ^ (prefixWord ++ tailWord_324669).sum := by decide
  have hdescent : baseEnd_324669 < baseStart_324669 := by decide
  rcases family_descends (prefixWord ++ tailWord_324669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324695 : List Nat := [1, 1, 3, 2, 2, 1, 1, 11]
def baseStart_324695 : Nat := 118140960795 + 324695 * 2 ^ 59
def prefixEnd_324695 : Nat := 4983230072969 + 3 ^ 40 * 324695 * 2
def baseEnd_324695 : Nat := 12349970452719434297723

theorem tailTrace_324695 : CollatzResearch.WordTrace tailWord_324695 prefixEnd_324695 12349970452719434297723 := by
  unfold tailWord_324695
  simp only [CollatzResearch.WordTrace]
  refine ⟨11842599558692943336231539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7895066372461962224154359 11842599558692943336231539)
  ·
    refine ⟨17763899338039415004347309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11842599558692943336231539 17763899338039415004347309)
    ·
      refine ⟨6661462251764780626630241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17763899338039415004347309 6661462251764780626630241)
      ·
        refine ⟨4996096688823585469972681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6661462251764780626630241 4996096688823585469972681)
        ·
          refine ⟨3747072516617689102479511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4996096688823585469972681 3747072516617689102479511)
          ·
            refine ⟨5620608774926533653719267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747072516617689102479511 5620608774926533653719267)
            ·
              refine ⟨8430913162389800480578901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5620608774926533653719267 8430913162389800480578901)
              ·
                refine ⟨12349970452719434297723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 8430913162389800480578901 12349970452719434297723)
                ·
                  rfl

theorem cell22_324695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 11].length) (baseStart_324695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324695 prefixEnd_324695 := by exact prefixLift 324695
  have htrace : WordTrace (prefixWord ++ tailWord_324695) baseStart_324695 baseEnd_324695 := by
    simpa [prefixWord, tailWord_324695, baseEnd_324695] using wordTrace_append hprefix tailTrace_324695
  have hstable : (prefixWord ++ tailWord_324695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324695).length < 2 ^ (prefixWord ++ tailWord_324695).sum := by decide
  have hdescent : baseEnd_324695 < baseStart_324695 := by decide
  rcases family_descends (prefixWord ++ tailWord_324695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324729 : List Nat := [1, 2, 1, 3, 6, 1, 8]
def baseStart_324729 : Nat := 118140960795 + 324729 * 2 ^ 59
def prefixEnd_324729 : Nat := 4983230072969 + 3 ^ 40 * 324729 * 2
def baseEnd_324729 : Nat := 4117087887752227901089

theorem tailTrace_324729 : CollatzResearch.WordTrace tailWord_324729 prefixEnd_324729 4117087887752227901089 := by
  unfold tailWord_324729
  simp only [CollatzResearch.WordTrace]
  refine ⟨11843839640569767142969241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7895893093713178095312827 11843839640569767142969241)
  ·
    refine ⟨8882879730427325357226931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11843839640569767142969241 8882879730427325357226931)
    ·
      refine ⟨13324319595640988035840397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8882879730427325357226931 13324319595640988035840397)
      ·
        refine ⟨4996619848365370513440149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13324319595640988035840397 4996619848365370513440149)
        ·
          refine ⟨234216555392126742817507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4996619848365370513440149 234216555392126742817507)
          ·
            refine ⟨351324833088190114226261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234216555392126742817507 351324833088190114226261)
            ·
              refine ⟨4117087887752227901089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 351324833088190114226261 4117087887752227901089)
              ·
                rfl

theorem cell22_324729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 8].length) (baseStart_324729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324729 prefixEnd_324729 := by exact prefixLift 324729
  have htrace : WordTrace (prefixWord ++ tailWord_324729) baseStart_324729 baseEnd_324729 := by
    simpa [prefixWord, tailWord_324729, baseEnd_324729] using wordTrace_append hprefix tailTrace_324729
  have hstable : (prefixWord ++ tailWord_324729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324729).length < 2 ^ (prefixWord ++ tailWord_324729).sum := by decide
  have hdescent : baseEnd_324729 < baseStart_324729 := by decide
  rcases family_descends (prefixWord ++ tailWord_324729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324851 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 2, 3]
def baseStart_324851 : Nat := 118140960795 + 324851 * 2 ^ 59
def prefixEnd_324851 : Nat := 4983230072969 + 3 ^ 40 * 324851 * 2
def baseEnd_324851 : Nat := 111203136062542501779029

theorem tailTrace_324851 : CollatzResearch.WordTrace tailWord_324851 prefixEnd_324851 111203136062542501779029 := by
  unfold tailWord_324851
  simp only [CollatzResearch.WordTrace]
  refine ⟨11848289346127781978910407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7898859564085187985940271 11848289346127781978910407)
  ·
    refine ⟨17772434019191672968365611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11848289346127781978910407 17772434019191672968365611)
    ·
      refine ⟨26658651028787509452548417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17772434019191672968365611 26658651028787509452548417)
      ·
        refine ⟨19993988271590632089411313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26658651028787509452548417 19993988271590632089411313)
        ·
          refine ⟨14995491203692974067058485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19993988271590632089411313 14995491203692974067058485)
          ·
            refine ⟨1405827300346216318786733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14995491203692974067058485 1405827300346216318786733)
            ·
              refine ⟨527185237629831119545025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1405827300346216318786733 527185237629831119545025)
              ·
                refine ⟨395388928222373339658769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527185237629831119545025 395388928222373339658769)
                ·
                  refine ⟨296541696166780004744077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395388928222373339658769 296541696166780004744077)
                  ·
                    refine ⟨111203136062542501779029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296541696166780004744077 111203136062542501779029)
                    ·
                      rfl

theorem cell22_324851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 3].length) (baseStart_324851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324851 prefixEnd_324851 := by exact prefixLift 324851
  have htrace : WordTrace (prefixWord ++ tailWord_324851) baseStart_324851 baseEnd_324851 := by
    simpa [prefixWord, tailWord_324851, baseEnd_324851] using wordTrace_append hprefix tailTrace_324851
  have hstable : (prefixWord ++ tailWord_324851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324851).length < 2 ^ (prefixWord ++ tailWord_324851).sum := by decide
  have hdescent : baseEnd_324851 < baseStart_324851 := by decide
  rcases family_descends (prefixWord ++ tailWord_324851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324907 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 5, 7]
def baseStart_324907 : Nat := 118140960795 + 324907 * 2 ^ 59
def prefixEnd_324907 : Nat := 4983230072969 + 3 ^ 40 * 324907 * 2
def baseEnd_324907 : Nat := 111222306006977022378857

theorem tailTrace_324907 : CollatzResearch.WordTrace tailWord_324907 prefixEnd_324907 111222306006977022378857 := by
  unfold tailWord_324907
  simp only [CollatzResearch.WordTrace]
  refine ⟨11850331833924903542948975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7900221222616602361965983 11850331833924903542948975)
  ·
    refine ⟨17775497750887355314423463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11850331833924903542948975 17775497750887355314423463)
    ·
      refine ⟨26663246626331032971635195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17775497750887355314423463 26663246626331032971635195)
      ·
        refine ⟨39994869939496549457452793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26663246626331032971635195 39994869939496549457452793)
        ·
          refine ⟨29996152454622412093089595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39994869939496549457452793 29996152454622412093089595)
          ·
            refine ⟨44994228681933618139634393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29996152454622412093089595 44994228681933618139634393)
            ·
              refine ⟨33745671511450213604725795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44994228681933618139634393 33745671511450213604725795)
              ·
                refine ⟨50618507267175320407088693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33745671511450213604725795 50618507267175320407088693)
                ·
                  refine ⟨4745485056297686288164565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50618507267175320407088693 4745485056297686288164565)
                  ·
                    refine ⟨111222306006977022378857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4745485056297686288164565 111222306006977022378857)
                    ·
                      rfl

theorem cell22_324907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_324907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324907 prefixEnd_324907 := by exact prefixLift 324907
  have htrace : WordTrace (prefixWord ++ tailWord_324907) baseStart_324907 baseEnd_324907 := by
    simpa [prefixWord, tailWord_324907, baseEnd_324907] using wordTrace_append hprefix tailTrace_324907
  have hstable : (prefixWord ++ tailWord_324907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324907).length < 2 ^ (prefixWord ++ tailWord_324907).sum := by decide
  have hdescent : baseEnd_324907 < baseStart_324907 := by decide
  rcases family_descends (prefixWord ++ tailWord_324907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324913 : List Nat := [1, 2, 2, 3, 3, 3, 1, 1, 3, 3]
def baseStart_324913 : Nat := 118140960795 + 324913 * 2 ^ 59
def prefixEnd_324913 : Nat := 4983230072969 + 3 ^ 40 * 324913 * 2
def baseEnd_324913 : Nat := 111224359929595006728839

theorem tailTrace_324913 : CollatzResearch.WordTrace tailWord_324913 prefixEnd_324913 111224359929595006728839 := by
  unfold tailWord_324913
  simp only [CollatzResearch.WordTrace]
  refine ⟨11850550671903166567667393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7900367114602111045111595 11850550671903166567667393)
  ·
    refine ⟨8887913003927374925750545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11850550671903166567667393 8887913003927374925750545)
    ·
      refine ⟨6665934752945531194312909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8887913003927374925750545 6665934752945531194312909)
      ·
        refine ⟨2499725532354574197867341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6665934752945531194312909 2499725532354574197867341)
        ·
          refine ⟨937397074632965324200253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2499725532354574197867341 937397074632965324200253)
          ·
            refine ⟨351523902987361996575095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 937397074632965324200253 351523902987361996575095)
            ·
              refine ⟨527285854481042994862643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351523902987361996575095 527285854481042994862643)
              ·
                refine ⟨790928781721564492293965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527285854481042994862643 790928781721564492293965)
                ·
                  refine ⟨296598293145586684610237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790928781721564492293965 296598293145586684610237)
                  ·
                    refine ⟨111224359929595006728839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296598293145586684610237 111224359929595006728839)
                    ·
                      rfl

theorem cell22_324913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_324913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324913 prefixEnd_324913 := by exact prefixLift 324913
  have htrace : WordTrace (prefixWord ++ tailWord_324913) baseStart_324913 baseEnd_324913 := by
    simpa [prefixWord, tailWord_324913, baseEnd_324913] using wordTrace_append hprefix tailTrace_324913
  have hstable : (prefixWord ++ tailWord_324913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324913).length < 2 ^ (prefixWord ++ tailWord_324913).sum := by decide
  have hdescent : baseEnd_324913 < baseStart_324913 := by decide
  rcases family_descends (prefixWord ++ tailWord_324913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324926 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_324926 : Nat := 118140960795 + 324926 * 2 ^ 59
def prefixEnd_324926 : Nat := 4983230072969 + 3 ^ 40 * 324926 * 2
def baseEnd_324926 : Nat := 37076270031755768717933

theorem tailTrace_324926 : CollatzResearch.WordTrace tailWord_324926 prefixEnd_324926 37076270031755768717933 := by
  unfold tailWord_324926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1481378102607008723486329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7900683213904046525260421 1481378102607008723486329)
  ·
    refine ⟨1111033576955256542614747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1481378102607008723486329 1111033576955256542614747)
    ·
      refine ⟨1666550365432884813922121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1111033576955256542614747 1666550365432884813922121)
      ·
        refine ⟨1249912774074663610441591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1666550365432884813922121 1249912774074663610441591)
        ·
          refine ⟨1874869161111995415662387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249912774074663610441591 1874869161111995415662387)
          ·
            refine ⟨2812303741667993123493581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874869161111995415662387 2812303741667993123493581)
            ·
              refine ⟨1054613903125497421310093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2812303741667993123493581 1054613903125497421310093)
              ·
                refine ⟨395480213672061532991285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1054613903125497421310093 395480213672061532991285)
                ·
                  refine ⟨37076270031755768717933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 395480213672061532991285 37076270031755768717933)
                  ·
                    rfl

theorem cell22_324926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_324926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_324926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_324926 prefixEnd_324926 := by exact prefixLift 324926
  have htrace : WordTrace (prefixWord ++ tailWord_324926) baseStart_324926 baseEnd_324926 := by
    simpa [prefixWord, tailWord_324926, baseEnd_324926] using wordTrace_append hprefix tailTrace_324926
  have hstable : (prefixWord ++ tailWord_324926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324926).length < 2 ^ (prefixWord ++ tailWord_324926).sum := by decide
  have hdescent : baseEnd_324926 < baseStart_324926 := by decide
  rcases family_descends (prefixWord ++ tailWord_324926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325001 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 1, 6]
def baseStart_325001 : Nat := 118140960795 + 325001 * 2 ^ 59
def prefixEnd_325001 : Nat := 4983230072969 + 3 ^ 40 * 325001 * 2
def baseEnd_325001 : Nat := 111254484127992110528569

theorem tailTrace_325001 : CollatzResearch.WordTrace tailWord_325001 prefixEnd_325001 111254484127992110528569 := by
  unfold tailWord_325001
  simp only [CollatzResearch.WordTrace]
  refine ⟨11853760295584357596870857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7902506863722905064580571 11853760295584357596870857)
  ·
    refine ⟨8890320221688268197653143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11853760295584357596870857 8890320221688268197653143)
    ·
      refine ⟨13335480332532402296479715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8890320221688268197653143 13335480332532402296479715)
      ·
        refine ⟨20003220498798603444719573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13335480332532402296479715 20003220498798603444719573)
        ·
          refine ⟨468825480440592268235615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 20003220498798603444719573 468825480440592268235615)
          ·
            refine ⟨703238220660888402353423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468825480440592268235615 703238220660888402353423)
            ·
              refine ⟨1054857330991332603530135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703238220660888402353423 1054857330991332603530135)
              ·
                refine ⟨1582285996486998905295203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054857330991332603530135 1582285996486998905295203)
                ·
                  refine ⟨2373428994730498357942805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582285996486998905295203 2373428994730498357942805)
                  ·
                    refine ⟨111254484127992110528569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2373428994730498357942805 111254484127992110528569)
                    ·
                      rfl

theorem cell22_325001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_325001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325001 prefixEnd_325001 := by exact prefixLift 325001
  have htrace : WordTrace (prefixWord ++ tailWord_325001) baseStart_325001 baseEnd_325001 := by
    simpa [prefixWord, tailWord_325001, baseEnd_325001] using wordTrace_append hprefix tailTrace_325001
  have hstable : (prefixWord ++ tailWord_325001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325001).length < 2 ^ (prefixWord ++ tailWord_325001).sum := by decide
  have hdescent : baseEnd_325001 < baseStart_325001 := by decide
  rcases family_descends (prefixWord ++ tailWord_325001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325016 : List Nat := [2, 1, 2, 5, 2, 1, 9]
def baseStart_325016 : Nat := 118140960795 + 325016 * 2 ^ 59
def prefixEnd_325016 : Nat := 4983230072969 + 3 ^ 40 * 325016 * 2
def baseEnd_325016 : Nat := 4120726627205076718649

theorem tailTrace_325016 : CollatzResearch.WordTrace tailWord_325016 prefixEnd_325016 4120726627205076718649 := by
  unfold tailWord_325016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5927153695265007579333451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7902871593686676772444601 5927153695265007579333451)
  ·
    refine ⟨8890730542897511369000177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5927153695265007579333451 8890730542897511369000177)
    ·
      refine ⟨6668047907173133526750133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8890730542897511369000177 6668047907173133526750133)
      ·
        refine ⟨625129491297481268132825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6668047907173133526750133 625129491297481268132825)
        ·
          refine ⟨468847118473110951099619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625129491297481268132825 468847118473110951099619)
          ·
            refine ⟨703270677709666426649429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468847118473110951099619 703270677709666426649429)
            ·
              refine ⟨4120726627205076718649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 703270677709666426649429 4120726627205076718649)
              ·
                rfl

theorem cell22_325016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 9].length) (baseStart_325016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325016 prefixEnd_325016 := by exact prefixLift 325016
  have htrace : WordTrace (prefixWord ++ tailWord_325016) baseStart_325016 baseEnd_325016 := by
    simpa [prefixWord, tailWord_325016, baseEnd_325016] using wordTrace_append hprefix tailTrace_325016
  have hstable : (prefixWord ++ tailWord_325016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325016).length < 2 ^ (prefixWord ++ tailWord_325016).sum := by decide
  have hdescent : baseEnd_325016 < baseStart_325016 := by decide
  rcases family_descends (prefixWord ++ tailWord_325016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325020 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 4, 3]
def baseStart_325020 : Nat := 118140960795 + 325020 * 2 ^ 59
def prefixEnd_325020 : Nat := 4983230072969 + 3 ^ 40 * 325020 * 2
def baseEnd_325020 : Nat := 111260988216282394303511

theorem tailTrace_325020 : CollatzResearch.WordTrace tailWord_325020 prefixEnd_325020 111260988216282394303511 := by
  unfold tailWord_325020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5927226641257761920906257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7902968855010349227875009 5927226641257761920906257)
  ·
    refine ⟨4445419980943321440679693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5927226641257761920906257 4445419980943321440679693)
    ·
      refine ⟨1667032492853745540254885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4445419980943321440679693 1667032492853745540254885)
      ·
        refine ⟨312568592410077288797791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1667032492853745540254885 312568592410077288797791)
        ·
          refine ⟨468852888615115933196687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312568592410077288797791 468852888615115933196687)
          ·
            refine ⟨703279332922673899795031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468852888615115933196687 703279332922673899795031)
            ·
              refine ⟨1054918999384010849692547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703279332922673899795031 1054918999384010849692547)
              ·
                refine ⟨1582378499076016274538821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054918999384010849692547 1582378499076016274538821)
                ·
                  refine ⟨296695968576753051476029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1582378499076016274538821 296695968576753051476029)
                  ·
                    refine ⟨111260988216282394303511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296695968576753051476029 111260988216282394303511)
                    ·
                      rfl

theorem cell22_325020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_325020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325020 prefixEnd_325020 := by exact prefixLift 325020
  have htrace : WordTrace (prefixWord ++ tailWord_325020) baseStart_325020 baseEnd_325020 := by
    simpa [prefixWord, tailWord_325020, baseEnd_325020] using wordTrace_append hprefix tailTrace_325020
  have hstable : (prefixWord ++ tailWord_325020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325020).length < 2 ^ (prefixWord ++ tailWord_325020).sum := by decide
  have hdescent : baseEnd_325020 < baseStart_325020 := by decide
  rcases family_descends (prefixWord ++ tailWord_325020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325029 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_325029 : Nat := 118140960795 + 325029 * 2 ^ 59
def prefixEnd_325029 : Nat := 4983230072969 + 3 ^ 40 * 325029 * 2
def baseEnd_325029 : Nat := 111264069100209370828483

theorem tailTrace_325029 : CollatzResearch.WordTrace tailWord_325029 prefixEnd_325029 111264069100209370828483 := by
  unfold tailWord_325029
  simp only [CollatzResearch.WordTrace]
  refine ⟨11854781539482918378890141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7903187692988612252593427 11854781539482918378890141)
  ·
    refine ⟨4445543077306094392083803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11854781539482918378890141 4445543077306094392083803)
    ·
      refine ⟨6668314615959141588125705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4445543077306094392083803 6668314615959141588125705)
      ·
        refine ⟨5001235961969356191094279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6668314615959141588125705 5001235961969356191094279)
        ·
          refine ⟨7501853942954034286641419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5001235961969356191094279 7501853942954034286641419)
          ·
            refine ⟨11252780914431051429962129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7501853942954034286641419 11252780914431051429962129)
            ·
              refine ⟨8439585685823288572471597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11252780914431051429962129 8439585685823288572471597)
              ·
                refine ⟨3164844632183733214676849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8439585685823288572471597 3164844632183733214676849)
                ·
                  refine ⟨2373633474137799911007637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3164844632183733214676849 2373633474137799911007637)
                  ·
                    refine ⟨111264069100209370828483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2373633474137799911007637 111264069100209370828483)
                    ·
                      rfl

theorem cell22_325029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_325029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325029 prefixEnd_325029 := by exact prefixLift 325029
  have htrace : WordTrace (prefixWord ++ tailWord_325029) baseStart_325029 baseEnd_325029 := by
    simpa [prefixWord, tailWord_325029, baseEnd_325029] using wordTrace_append hprefix tailTrace_325029
  have hstable : (prefixWord ++ tailWord_325029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325029).length < 2 ^ (prefixWord ++ tailWord_325029).sum := by decide
  have hdescent : baseEnd_325029 < baseStart_325029 := by decide
  rcases family_descends (prefixWord ++ tailWord_325029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325037 : List Nat := [1, 5, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_325037 : Nat := 118140960795 + 325037 * 2 ^ 59
def prefixEnd_325037 : Nat := 4983230072969 + 3 ^ 40 * 325037 * 2
def baseEnd_325037 : Nat := 111266807663700016628459

theorem tailTrace_325037 : CollatzResearch.WordTrace tailWord_325037 prefixEnd_325037 111266807663700016628459 := by
  unfold tailWord_325037
  simp only [CollatzResearch.WordTrace]
  refine ⟨11855073323453935745181365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7903382215635957163454243 11855073323453935745181365)
  ·
    refine ⟨1111413124073806476110753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11855073323453935745181365 1111413124073806476110753)
    ·
      refine ⟨833559843055354857083065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1111413124073806476110753 833559843055354857083065)
      ·
        refine ⟨625169882291516142812299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 833559843055354857083065 625169882291516142812299)
        ·
          refine ⟨937754823437274214218449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625169882291516142812299 937754823437274214218449)
          ·
            refine ⟨703316117577955660663837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 937754823437274214218449 703316117577955660663837)
            ·
              refine ⟨263743544091733372748939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 703316117577955660663837 263743544091733372748939)
              ·
                refine ⟨395615316137600059123409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263743544091733372748939 395615316137600059123409)
                ·
                  refine ⟨296711487103200044342557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395615316137600059123409 296711487103200044342557)
                  ·
                    refine ⟨111266807663700016628459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296711487103200044342557 111266807663700016628459)
                    ·
                      rfl

theorem cell22_325037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_325037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325037 prefixEnd_325037 := by exact prefixLift 325037
  have htrace : WordTrace (prefixWord ++ tailWord_325037) baseStart_325037 baseEnd_325037 := by
    simpa [prefixWord, tailWord_325037, baseEnd_325037] using wordTrace_append hprefix tailTrace_325037
  have hstable : (prefixWord ++ tailWord_325037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325037).length < 2 ^ (prefixWord ++ tailWord_325037).sum := by decide
  have hdescent : baseEnd_325037 < baseStart_325037 := by decide
  rcases family_descends (prefixWord ++ tailWord_325037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325059 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 1, 7]
def baseStart_325059 : Nat := 118140960795 + 325059 * 2 ^ 59
def prefixEnd_325059 : Nat := 4983230072969 + 3 ^ 40 * 325059 * 2
def baseEnd_325059 : Nat := 111274338713299292578391

theorem tailTrace_325059 : CollatzResearch.WordTrace tailWord_325059 prefixEnd_325059 111274338713299292578391 := by
  unfold tailWord_325059
  simp only [CollatzResearch.WordTrace]
  refine ⟨11855875729374233502482231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7903917152916155668321487 11855875729374233502482231)
  ·
    refine ⟨17783813594061350253723347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11855875729374233502482231 17783813594061350253723347)
    ·
      refine ⟨26675720391092025380585021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17783813594061350253723347 26675720391092025380585021)
      ·
        refine ⟨10003395146659509517719383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26675720391092025380585021 10003395146659509517719383)
        ·
          refine ⟨15005092719989264276579075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10003395146659509517719383 15005092719989264276579075)
          ·
            refine ⟨22507639079983896414868613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15005092719989264276579075 22507639079983896414868613)
            ·
              refine ⟨4220182327496980577787865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22507639079983896414868613 4220182327496980577787865)
              ·
                refine ⟨3165136745622735433340899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4220182327496980577787865 3165136745622735433340899)
                ·
                  refine ⟨4747705118434103150011349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3165136745622735433340899 4747705118434103150011349)
                  ·
                    refine ⟨111274338713299292578391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4747705118434103150011349 111274338713299292578391)
                    ·
                      rfl

theorem cell22_325059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_325059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325059 prefixEnd_325059 := by exact prefixLift 325059
  have htrace : WordTrace (prefixWord ++ tailWord_325059) baseStart_325059 baseEnd_325059 := by
    simpa [prefixWord, tailWord_325059, baseEnd_325059] using wordTrace_append hprefix tailTrace_325059
  have hstable : (prefixWord ++ tailWord_325059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325059).length < 2 ^ (prefixWord ++ tailWord_325059).sum := by decide
  have hdescent : baseEnd_325059 < baseStart_325059 := by decide
  rcases family_descends (prefixWord ++ tailWord_325059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325078 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_325078 : Nat := 118140960795 + 325078 * 2 ^ 59
def prefixEnd_325078 : Nat := 4983230072969 + 3 ^ 40 * 325078 * 2
def baseEnd_325078 : Nat := 37093614267196525451111

theorem tailTrace_325078 : CollatzResearch.WordTrace tailWord_325078 prefixEnd_325078 37093614267196525451111 := by
  unfold tailWord_325078
  simp only [CollatzResearch.WordTrace]
  refine ⟨741035544769087484213993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7904379144203599831615925 741035544769087484213993)
  ·
    refine ⟨555776658576815613160495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 741035544769087484213993 555776658576815613160495)
    ·
      refine ⟨833664987865223419740743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555776658576815613160495 833664987865223419740743)
      ·
        refine ⟨1250497481797835129611115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833664987865223419740743 1250497481797835129611115)
        ·
          refine ⟨1875746222696752694416673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250497481797835129611115 1875746222696752694416673)
          ·
            refine ⟨1406809667022564520812505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1875746222696752694416673 1406809667022564520812505)
            ·
              refine ⟨1055107250266923390609379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1406809667022564520812505 1055107250266923390609379)
              ·
                refine ⟨1582660875400385085914069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055107250266923390609379 1582660875400385085914069)
                ·
                  refine ⟨37093614267196525451111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1582660875400385085914069 37093614267196525451111)
                  ·
                    rfl

theorem cell22_325078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_325078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325078 prefixEnd_325078 := by exact prefixLift 325078
  have htrace : WordTrace (prefixWord ++ tailWord_325078) baseStart_325078 baseEnd_325078 := by
    simpa [prefixWord, tailWord_325078, baseEnd_325078] using wordTrace_append hprefix tailTrace_325078
  have hstable : (prefixWord ++ tailWord_325078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325078).length < 2 ^ (prefixWord ++ tailWord_325078).sum := by decide
  have hdescent : baseEnd_325078 < baseStart_325078 := by decide
  rcases family_descends (prefixWord ++ tailWord_325078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325082 : List Nat := [3, 1, 1, 2, 3, 3, 3, 2, 1, 3]
def baseStart_325082 : Nat := 118140960795 + 325082 * 2 ^ 59
def prefixEnd_325082 : Nat := 4983230072969 + 3 ^ 40 * 325082 * 2
def baseEnd_325082 : Nat := 111282212083334899253321

theorem tailTrace_325082 : CollatzResearch.WordTrace tailWord_325082 prefixEnd_325082 111282212083334899253321 := by
  unfold tailWord_325082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2964178652072727107642375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7904476405527272287046333 2964178652072727107642375)
  ·
    refine ⟨4446267978109090661463563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2964178652072727107642375 4446267978109090661463563)
    ·
      refine ⟨6669401967163635992195345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4446267978109090661463563 6669401967163635992195345)
      ·
        refine ⟨5002051475372726994146509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6669401967163635992195345 5002051475372726994146509)
        ·
          refine ⟨1875769303264772622804941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5002051475372726994146509 1875769303264772622804941)
          ·
            refine ⟨703413488724289733551853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1875769303264772622804941 703413488724289733551853)
            ·
              refine ⟨263780058271608650081945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 703413488724289733551853 263780058271608650081945)
              ·
                refine ⟨197835043703706487561459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263780058271608650081945 197835043703706487561459)
                ·
                  refine ⟨296752565555559731342189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197835043703706487561459 296752565555559731342189)
                  ·
                    refine ⟨111282212083334899253321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296752565555559731342189 111282212083334899253321)
                    ·
                      rfl

theorem cell22_325082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_325082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325082 prefixEnd_325082 := by exact prefixLift 325082
  have htrace : WordTrace (prefixWord ++ tailWord_325082) baseStart_325082 baseEnd_325082 := by
    simpa [prefixWord, tailWord_325082, baseEnd_325082] using wordTrace_append hprefix tailTrace_325082
  have hstable : (prefixWord ++ tailWord_325082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325082).length < 2 ^ (prefixWord ++ tailWord_325082).sum := by decide
  have hdescent : baseEnd_325082 < baseStart_325082 := by decide
  rcases family_descends (prefixWord ++ tailWord_325082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325095 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 5]
def baseStart_325095 : Nat := 118140960795 + 325095 * 2 ^ 59
def prefixEnd_325095 : Nat := 4983230072969 + 3 ^ 40 * 325095 * 2
def baseEnd_325095 : Nat := 37095554083002399559427

theorem tailTrace_325095 : CollatzResearch.WordTrace tailWord_325095 prefixEnd_325095 37095554083002399559427 := by
  unfold tailWord_325095
  simp only [CollatzResearch.WordTrace]
  refine ⟨11857188757243811650792739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7904792504829207767195159 11857188757243811650792739)
  ·
    refine ⟨17785783135865717476189109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11857188757243811650792739 17785783135865717476189109)
    ·
      refine ⟨1667417168987411013392729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17785783135865717476189109 1667417168987411013392729)
      ·
        refine ⟨1250562876740558260044547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1667417168987411013392729 1250562876740558260044547)
        ·
          refine ⟨1875844315110837390066821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250562876740558260044547 1875844315110837390066821)
          ·
            refine ⟨351720809083282010637529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1875844315110837390066821 351720809083282010637529)
            ·
              refine ⟨263790606812461507978147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351720809083282010637529 263790606812461507978147)
              ·
                refine ⟨395685910218692261967221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263790606812461507978147 395685910218692261967221)
                ·
                  refine ⟨37095554083002399559427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 395685910218692261967221 37095554083002399559427)
                  ·
                    rfl

theorem cell22_325095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 5].length) (baseStart_325095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325095 prefixEnd_325095 := by exact prefixLift 325095
  have htrace : WordTrace (prefixWord ++ tailWord_325095) baseStart_325095 baseEnd_325095 := by
    simpa [prefixWord, tailWord_325095, baseEnd_325095] using wordTrace_append hprefix tailTrace_325095
  have hstable : (prefixWord ++ tailWord_325095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325095).length < 2 ^ (prefixWord ++ tailWord_325095).sum := by decide
  have hdescent : baseEnd_325095 < baseStart_325095 := by decide
  rcases family_descends (prefixWord ++ tailWord_325095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325133 : List Nat := [1, 7, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_325133 : Nat := 118140960795 + 325133 * 2 ^ 59
def prefixEnd_325133 : Nat := 4983230072969 + 3 ^ 40 * 325133 * 2
def baseEnd_325133 : Nat := 111299670425587766228165

theorem tailTrace_325133 : CollatzResearch.WordTrace tailWord_325133 prefixEnd_325133 111299670425587766228165 := by
  unfold tailWord_325133
  simp only [CollatzResearch.WordTrace]
  refine ⟨11858574731106144140676053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7905716487404096093784035 11858574731106144140676053)
  ·
    refine ⟨277935345260300253297095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11858574731106144140676053 277935345260300253297095)
    ·
      refine ⟨416903017890450379945643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277935345260300253297095 416903017890450379945643)
      ·
        refine ⟨625354526835675569918465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416903017890450379945643 625354526835675569918465)
        ·
          refine ⟨469015895126756677438849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625354526835675569918465 469015895126756677438849)
          ·
            refine ⟨351761921345067508079137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469015895126756677438849 351761921345067508079137)
            ·
              refine ⟨263821441008800631059353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351761921345067508079137 263821441008800631059353)
              ·
                refine ⟨197866080756600473294515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263821441008800631059353 197866080756600473294515)
                ·
                  refine ⟨296799121134900709941773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197866080756600473294515 296799121134900709941773)
                  ·
                    refine ⟨111299670425587766228165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296799121134900709941773 111299670425587766228165)
                    ·
                      rfl

theorem cell22_325133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_325133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325133 prefixEnd_325133 := by exact prefixLift 325133
  have htrace : WordTrace (prefixWord ++ tailWord_325133) baseStart_325133 baseEnd_325133 := by
    simpa [prefixWord, tailWord_325133, baseEnd_325133] using wordTrace_append hprefix tailTrace_325133
  have hstable : (prefixWord ++ tailWord_325133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325133).length < 2 ^ (prefixWord ++ tailWord_325133).sum := by decide
  have hdescent : baseEnd_325133 < baseStart_325133 := by decide
  rcases family_descends (prefixWord ++ tailWord_325133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325151 : List Nat := [1, 1, 2, 4, 1, 1, 5, 7]
def baseStart_325151 : Nat := 118140960795 + 325151 * 2 ^ 59
def prefixEnd_325151 : Nat := 4983230072969 + 3 ^ 40 * 325151 * 2
def baseEnd_325151 : Nat := 12367314688160191030901

theorem tailTrace_325151 : CollatzResearch.WordTrace tailWord_325151 prefixEnd_325151 12367314688160191030901 := by
  unfold tailWord_325151
  simp only [CollatzResearch.WordTrace]
  refine ⟨11859231245040933214831307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7906154163360622143220871 11859231245040933214831307)
  ·
    refine ⟨17788846867561399822246961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11859231245040933214831307 17788846867561399822246961)
    ·
      refine ⟨13341635150671049866685221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17788846867561399822246961 13341635150671049866685221)
      ·
        refine ⟨2501556590750821850003479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13341635150671049866685221 2501556590750821850003479)
        ·
          refine ⟨3752334886126232775005219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501556590750821850003479 3752334886126232775005219)
          ·
            refine ⟨5628502329189349162507829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3752334886126232775005219 5628502329189349162507829)
            ·
              refine ⟨527672093361501483985109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5628502329189349162507829 527672093361501483985109)
              ·
                refine ⟨12367314688160191030901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 527672093361501483985109 12367314688160191030901)
                ·
                  rfl

theorem cell22_325151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 7].length) (baseStart_325151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325151 prefixEnd_325151 := by exact prefixLift 325151
  have htrace : WordTrace (prefixWord ++ tailWord_325151) baseStart_325151 baseEnd_325151 := by
    simpa [prefixWord, tailWord_325151, baseEnd_325151] using wordTrace_append hprefix tailTrace_325151
  have hstable : (prefixWord ++ tailWord_325151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325151).length < 2 ^ (prefixWord ++ tailWord_325151).sum := by decide
  have hdescent : baseEnd_325151 < baseStart_325151 := by decide
  rcases family_descends (prefixWord ++ tailWord_325151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325200 : List Nat := [2, 1, 1, 1, 1, 3, 3, 6, 1, 3]
def baseStart_325200 : Nat := 118140960795 + 325200 * 2 ^ 59
def prefixEnd_325200 : Nat := 4983230072969 + 3 ^ 40 * 325200 * 2
def baseEnd_325200 : Nat := 111322605894821924802959

theorem tailTrace_325200 : CollatzResearch.WordTrace tailWord_325200 prefixEnd_325200 111322605894821924802959 := by
  unfold tailWord_325200
  simp only [CollatzResearch.WordTrace]
  refine ⟨5930509210931707291682527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7907345614575609722243369 5930509210931707291682527)
  ·
    refine ⟨8895763816397560937523791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5930509210931707291682527 8895763816397560937523791)
    ·
      refine ⟨13343645724596341406285687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8895763816397560937523791 13343645724596341406285687)
      ·
        refine ⟨20015468586894512109428531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13343645724596341406285687 20015468586894512109428531)
        ·
          refine ⟨30023202880341768164142797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20015468586894512109428531 30023202880341768164142797)
          ·
            refine ⟨11258701080128163061553549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30023202880341768164142797 11258701080128163061553549)
            ·
              refine ⟨4222012905048061148082581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11258701080128163061553549 4222012905048061148082581)
              ·
                refine ⟨197906854924127866316371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4222012905048061148082581 197906854924127866316371)
                ·
                  refine ⟨296860282386191799474557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197906854924127866316371 296860282386191799474557)
                  ·
                    refine ⟨111322605894821924802959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296860282386191799474557 111322605894821924802959)
                    ·
                      rfl

theorem cell22_325200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 6, 1, 3].length) (baseStart_325200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325200 prefixEnd_325200 := by exact prefixLift 325200
  have htrace : WordTrace (prefixWord ++ tailWord_325200) baseStart_325200 baseEnd_325200 := by
    simpa [prefixWord, tailWord_325200, baseEnd_325200] using wordTrace_append hprefix tailTrace_325200
  have hstable : (prefixWord ++ tailWord_325200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325200).length < 2 ^ (prefixWord ++ tailWord_325200).sum := by decide
  have hdescent : baseEnd_325200 < baseStart_325200 := by decide
  rcases family_descends (prefixWord ++ tailWord_325200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325206 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_325206 : Nat := 118140960795 + 325206 * 2 ^ 59
def prefixEnd_325206 : Nat := 4983230072969 + 3 ^ 40 * 325206 * 2
def baseEnd_325206 : Nat := 111324659817439909152941

theorem tailTrace_325206 : CollatzResearch.WordTrace tailWord_325206 prefixEnd_325206 111324659817439909152941 := by
  unfold tailWord_325206
  simp only [CollatzResearch.WordTrace]
  refine ⟨741327328740104850505217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7907491506561118405388981 741327328740104850505217)
  ·
    refine ⟨555995496555078637878913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 741327328740104850505217 555995496555078637878913)
    ·
      refine ⟨416996622416308978409185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 555995496555078637878913 416996622416308978409185)
      ·
        refine ⟨312747466812231733806889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416996622416308978409185 312747466812231733806889)
        ·
          refine ⟨234560600109173800355167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312747466812231733806889 234560600109173800355167)
          ·
            refine ⟨351840900163760700532751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234560600109173800355167 351840900163760700532751)
            ·
              refine ⟨527761350245641050799127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351840900163760700532751 527761350245641050799127)
              ·
                refine ⟨791642025368461576198691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527761350245641050799127 791642025368461576198691)
                ·
                  refine ⟨1187463038052692364298037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791642025368461576198691 1187463038052692364298037)
                  ·
                    refine ⟨111324659817439909152941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1187463038052692364298037 111324659817439909152941)
                    ·
                      rfl

theorem cell22_325206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_325206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325206 prefixEnd_325206 := by exact prefixLift 325206
  have htrace : WordTrace (prefixWord ++ tailWord_325206) baseStart_325206 baseEnd_325206 := by
    simpa [prefixWord, tailWord_325206, baseEnd_325206] using wordTrace_append hprefix tailTrace_325206
  have hstable : (prefixWord ++ tailWord_325206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325206).length < 2 ^ (prefixWord ++ tailWord_325206).sum := by decide
  have hdescent : baseEnd_325206 < baseStart_325206 := by decide
  rcases family_descends (prefixWord ++ tailWord_325206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325234 : List Nat := [3, 2, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_325234 : Nat := 118140960795 + 325234 * 2 ^ 59
def prefixEnd_325234 : Nat := 4983230072969 + 3 ^ 40 * 325234 * 2
def baseEnd_325234 : Nat := 111334244789657169452855

theorem tailTrace_325234 : CollatzResearch.WordTrace tailWord_325234 prefixEnd_325234 111334244789657169452855 := by
  unfold tailWord_325234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2965564625935059597525689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7908172335826825593401837 2965564625935059597525689)
  ·
    refine ⟨2224173469451294698144267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2965564625935059597525689 2224173469451294698144267)
    ·
      refine ⟨3336260204176942047216401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2224173469451294698144267 3336260204176942047216401)
      ·
        refine ⟨2502195153132706535412301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3336260204176942047216401 2502195153132706535412301)
        ·
          refine ⟨938323182424764950779613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2502195153132706535412301 938323182424764950779613)
          ·
            refine ⟨351871193409286856542355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 938323182424764950779613 351871193409286856542355)
            ·
              refine ⟨527806790113930284813533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351871193409286856542355 527806790113930284813533)
              ·
                refine ⟨197927546292723856805075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 527806790113930284813533 197927546292723856805075)
                ·
                  refine ⟨296891319439085785207613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197927546292723856805075 296891319439085785207613)
                  ·
                    refine ⟨111334244789657169452855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296891319439085785207613 111334244789657169452855)
                    ·
                      rfl

theorem cell22_325234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_325234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325234 prefixEnd_325234 := by exact prefixLift 325234
  have htrace : WordTrace (prefixWord ++ tailWord_325234) baseStart_325234 baseEnd_325234 := by
    simpa [prefixWord, tailWord_325234, baseEnd_325234] using wordTrace_append hprefix tailTrace_325234
  have hstable : (prefixWord ++ tailWord_325234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325234).length < 2 ^ (prefixWord ++ tailWord_325234).sum := by decide
  have hdescent : baseEnd_325234 < baseStart_325234 := by decide
  rcases family_descends (prefixWord ++ tailWord_325234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325243 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 1, 4]
def baseStart_325243 : Nat := 118140960795 + 325243 * 2 ^ 59
def prefixEnd_325243 : Nat := 4983230072969 + 3 ^ 40 * 325243 * 2
def baseEnd_325243 : Nat := 111337325673584145977827

theorem tailTrace_325243 : CollatzResearch.WordTrace tailWord_325243 prefixEnd_325243 111337325673584145977827 := by
  unfold tailWord_325243
  simp only [CollatzResearch.WordTrace]
  refine ⟨11862586760707632927180383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7908391173805088618120255 11862586760707632927180383)
  ·
    refine ⟨17793880141061449390770575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11862586760707632927180383 17793880141061449390770575)
    ·
      refine ⟨26690820211592174086155863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17793880141061449390770575 26690820211592174086155863)
      ·
        refine ⟨40036230317388261129233795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26690820211592174086155863 40036230317388261129233795)
        ·
          refine ⟨60054345476082391693850693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40036230317388261129233795 60054345476082391693850693)
          ·
            refine ⟨11260189776765448442597005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60054345476082391693850693 11260189776765448442597005)
            ·
              refine ⟨4222571166287043165973877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11260189776765448442597005 4222571166287043165973877)
              ·
                refine ⟨395866046839410296810051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4222571166287043165973877 395866046839410296810051)
                ·
                  refine ⟨593799070259115445215077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395866046839410296810051 593799070259115445215077)
                  ·
                    refine ⟨111337325673584145977827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 593799070259115445215077 111337325673584145977827)
                    ·
                      rfl

theorem cell22_325243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 1, 4].length) (baseStart_325243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325243 prefixEnd_325243 := by exact prefixLift 325243
  have htrace : WordTrace (prefixWord ++ tailWord_325243) baseStart_325243 baseEnd_325243 := by
    simpa [prefixWord, tailWord_325243, baseEnd_325243] using wordTrace_append hprefix tailTrace_325243
  have hstable : (prefixWord ++ tailWord_325243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325243).length < 2 ^ (prefixWord ++ tailWord_325243).sum := by decide
  have hdescent : baseEnd_325243 < baseStart_325243 := by decide
  rcases family_descends (prefixWord ++ tailWord_325243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325273 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 6, 3]
def baseStart_325273 : Nat := 118140960795 + 325273 * 2 ^ 59
def prefixEnd_325273 : Nat := 4983230072969 + 3 ^ 40 * 325273 * 2
def baseEnd_325273 : Nat := 111347595286674067727735

theorem tailTrace_325273 : CollatzResearch.WordTrace tailWord_325273 prefixEnd_325273 111347595286674067727735 := by
  unfold tailWord_325273
  simp only [CollatzResearch.WordTrace]
  refine ⟨11863680950598948050772473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7909120633732632033848315 11863680950598948050772473)
  ·
    refine ⟨8897760712949211038079355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11863680950598948050772473 8897760712949211038079355)
    ·
      refine ⟨13346641069423816557119033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8897760712949211038079355 13346641069423816557119033)
      ·
        refine ⟨10009980802067862417839275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13346641069423816557119033 10009980802067862417839275)
        ·
          refine ⟨15014971203101793626758913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10009980802067862417839275 15014971203101793626758913)
          ·
            refine ⟨11261228402326345220069185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15014971203101793626758913 11261228402326345220069185)
            ·
              refine ⟨8445921301744758915051889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11261228402326345220069185 8445921301744758915051889)
              ·
                refine ⟨6334440976308569186288917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8445921301744758915051889 6334440976308569186288917)
                ·
                  refine ⟨296926920764464180607293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6334440976308569186288917 296926920764464180607293)
                  ·
                    refine ⟨111347595286674067727735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296926920764464180607293 111347595286674067727735)
                    ·
                      rfl

theorem cell22_325273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 3].length) (baseStart_325273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325273 prefixEnd_325273 := by exact prefixLift 325273
  have htrace : WordTrace (prefixWord ++ tailWord_325273) baseStart_325273 baseEnd_325273 := by
    simpa [prefixWord, tailWord_325273, baseEnd_325273] using wordTrace_append hprefix tailTrace_325273
  have hstable : (prefixWord ++ tailWord_325273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325273).length < 2 ^ (prefixWord ++ tailWord_325273).sum := by decide
  have hdescent : baseEnd_325273 < baseStart_325273 := by decide
  rcases family_descends (prefixWord ++ tailWord_325273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325335 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 3, 3]
def baseStart_325335 : Nat := 118140960795 + 325335 * 2 ^ 59
def prefixEnd_325335 : Nat := 4983230072969 + 3 ^ 40 * 325335 * 2
def baseEnd_325335 : Nat := 111368819153726572677545

theorem tailTrace_325335 : CollatzResearch.WordTrace tailWord_325335 prefixEnd_325335 111368819153726572677545 := by
  unfold tailWord_325335
  simp only [CollatzResearch.WordTrace]
  refine ⟨11865942276374332639529459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7910628184249555093019639 11865942276374332639529459)
  ·
    refine ⟨17798913414561498959294189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11865942276374332639529459 17798913414561498959294189)
    ·
      refine ⟨6674592530460562109735321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17798913414561498959294189 6674592530460562109735321)
      ·
        refine ⟨5005944397845421582301491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6674592530460562109735321 5005944397845421582301491)
        ·
          refine ⟨7508916596768132373452237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5005944397845421582301491 7508916596768132373452237)
          ·
            refine ⟨2815843723788049640044589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7508916596768132373452237 2815843723788049640044589)
            ·
              refine ⟨1055941396420518615016721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2815843723788049640044589 1055941396420518615016721)
              ·
                refine ⟨791956047315388961262541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055941396420518615016721 791956047315388961262541)
                ·
                  refine ⟨296983517743270860473453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791956047315388961262541 296983517743270860473453)
                  ·
                    refine ⟨111368819153726572677545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296983517743270860473453 111368819153726572677545)
                    ·
                      rfl

theorem cell22_325335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_325335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325335 prefixEnd_325335 := by exact prefixLift 325335
  have htrace : WordTrace (prefixWord ++ tailWord_325335) baseStart_325335 baseEnd_325335 := by
    simpa [prefixWord, tailWord_325335, baseEnd_325335] using wordTrace_append hprefix tailTrace_325335
  have hstable : (prefixWord ++ tailWord_325335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325335).length < 2 ^ (prefixWord ++ tailWord_325335).sum := by decide
  have hdescent : baseEnd_325335 < baseStart_325335 := by decide
  rcases family_descends (prefixWord ++ tailWord_325335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325348 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 7]
def baseStart_325348 : Nat := 118140960795 + 325348 * 2 ^ 59
def prefixEnd_325348 : Nat := 4983230072969 + 3 ^ 40 * 325348 * 2
def baseEnd_325348 : Nat := 37124423106466290700835

theorem tailTrace_325348 : CollatzResearch.WordTrace tailWord_325348 prefixEnd_325348 37124423106466290700835 := by
  unfold tailWord_325348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5933208212663617929876349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7910944283551490573168465 5933208212663617929876349)
  ·
    refine ⟨2224953079748856723703631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5933208212663617929876349 2224953079748856723703631)
    ·
      refine ⟨3337429619623285085555447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2224953079748856723703631 3337429619623285085555447)
      ·
        refine ⟨5006144429434927628333171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337429619623285085555447 5006144429434927628333171)
        ·
          refine ⟨7509216644152391442499757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5006144429434927628333171 7509216644152391442499757)
          ·
            refine ⟨2815956241557146790937409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7509216644152391442499757 2815956241557146790937409)
            ·
              refine ⟨2111967181167860093203057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2815956241557146790937409 2111967181167860093203057)
              ·
                refine ⟨1583975385875895069902293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2111967181167860093203057 1583975385875895069902293)
                ·
                  refine ⟨37124423106466290700835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1583975385875895069902293 37124423106466290700835)
                  ·
                    rfl

theorem cell22_325348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_325348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325348 prefixEnd_325348 := by exact prefixLift 325348
  have htrace : WordTrace (prefixWord ++ tailWord_325348) baseStart_325348 baseEnd_325348 := by
    simpa [prefixWord, tailWord_325348, baseEnd_325348] using wordTrace_append hprefix tailTrace_325348
  have hstable : (prefixWord ++ tailWord_325348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325348).length < 2 ^ (prefixWord ++ tailWord_325348).sum := by decide
  have hdescent : baseEnd_325348 < baseStart_325348 := by decide
  rcases family_descends (prefixWord ++ tailWord_325348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325363 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 2, 5]
def baseStart_325363 : Nat := 118140960795 + 325363 * 2 ^ 59
def prefixEnd_325363 : Nat := 4983230072969 + 3 ^ 40 * 325363 * 2
def baseEnd_325363 : Nat := 111378404125943832977459

theorem tailTrace_325363 : CollatzResearch.WordTrace tailWord_325363 prefixEnd_325363 111378404125943832977459 := by
  unfold tailWord_325363
  simp only [CollatzResearch.WordTrace]
  refine ⟨11866963520272893421548743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7911309013515262281032495 11866963520272893421548743)
  ·
    refine ⟨17800445280409340132323115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11866963520272893421548743 17800445280409340132323115)
    ·
      refine ⟨26700667920614010198484673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17800445280409340132323115 26700667920614010198484673)
      ·
        refine ⟨20025500940460507648863505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26700667920614010198484673 20025500940460507648863505)
        ·
          refine ⟨15019125705345380736647629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20025500940460507648863505 15019125705345380736647629)
          ·
            refine ⟨5632172139504517776242861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15019125705345380736647629 5632172139504517776242861)
            ·
              refine ⟨2112064552314194166091073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5632172139504517776242861 2112064552314194166091073)
              ·
                refine ⟨1584048414235645624568305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2112064552314194166091073 1584048414235645624568305)
                ·
                  refine ⟨1188036310676734218426229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1584048414235645624568305 1188036310676734218426229)
                  ·
                    refine ⟨111378404125943832977459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1188036310676734218426229 111378404125943832977459)
                    ·
                      rfl

theorem cell22_325363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_325363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325363 prefixEnd_325363 := by exact prefixLift 325363
  have htrace : WordTrace (prefixWord ++ tailWord_325363) baseStart_325363 baseEnd_325363 := by
    simpa [prefixWord, tailWord_325363, baseEnd_325363] using wordTrace_append hprefix tailTrace_325363
  have hstable : (prefixWord ++ tailWord_325363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325363).length < 2 ^ (prefixWord ++ tailWord_325363).sum := by decide
  have hdescent : baseEnd_325363 < baseStart_325363 := by decide
  rcases family_descends (prefixWord ++ tailWord_325363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325380 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_325380 : Nat := 118140960795 + 325380 * 2 ^ 59
def prefixEnd_325380 : Nat := 4983230072969 + 3 ^ 40 * 325380 * 2
def baseEnd_325380 : Nat := 111384223573361455302407

theorem tailTrace_325380 : CollatzResearch.WordTrace tailWord_325380 prefixEnd_325380 111384223573361455302407 := by
  unfold tailWord_325380
  simp only [CollatzResearch.WordTrace]
  refine ⟨5933791780605652662458797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7911722374140870216611729 5933791780605652662458797)
  ·
    refine ⟨2225171917727119748422049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5933791780605652662458797 2225171917727119748422049)
    ·
      refine ⟨1668878938295339811316537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2225171917727119748422049 1668878938295339811316537)
      ·
        refine ⟨1251659203721504858487403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1668878938295339811316537 1251659203721504858487403)
        ·
          refine ⟨1877488805582257287731105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251659203721504858487403 1877488805582257287731105)
          ·
            refine ⟨1408116604186692965798329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1877488805582257287731105 1408116604186692965798329)
            ·
              refine ⟨1056087453140019724348747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408116604186692965798329 1056087453140019724348747)
              ·
                refine ⟨1584131179710029586523121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056087453140019724348747 1584131179710029586523121)
                ·
                  refine ⟨1188098384782522189892341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1584131179710029586523121 1188098384782522189892341)
                  ·
                    refine ⟨111384223573361455302407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1188098384782522189892341 111384223573361455302407)
                    ·
                      rfl

theorem cell22_325380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_325380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325380 prefixEnd_325380 := by exact prefixLift 325380
  have htrace : WordTrace (prefixWord ++ tailWord_325380) baseStart_325380 baseEnd_325380 := by
    simpa [prefixWord, tailWord_325380, baseEnd_325380] using wordTrace_append hprefix tailTrace_325380
  have hstable : (prefixWord ++ tailWord_325380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325380).length < 2 ^ (prefixWord ++ tailWord_325380).sum := by decide
  have hdescent : baseEnd_325380 < baseStart_325380 := by decide
  rcases family_descends (prefixWord ++ tailWord_325380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325412 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_325412 : Nat := 118140960795 + 325412 * 2 ^ 59
def prefixEnd_325412 : Nat := 4983230072969 + 3 ^ 40 * 325412 * 2
def baseEnd_325412 : Nat := 111395177827324038502309

theorem tailTrace_325412 : CollatzResearch.WordTrace tailWord_325412 prefixEnd_325412 111395177827324038502309 := by
  unfold tailWord_325412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5934375348547687395041245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7912500464730249860054993 5934375348547687395041245)
  ·
    refine ⟨2225390755705382773140467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5934375348547687395041245 2225390755705382773140467)
    ·
      refine ⟨3338086133558074159710701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2225390755705382773140467 3338086133558074159710701)
      ·
        refine ⟨1251782300084277809891513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3338086133558074159710701 1251782300084277809891513)
        ·
          refine ⟨938836725063208357418635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1251782300084277809891513 938836725063208357418635)
          ·
            refine ⟨1408255087594812536127953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938836725063208357418635 1408255087594812536127953)
            ·
              refine ⟨1056191315696109402095965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408255087594812536127953 1056191315696109402095965)
              ·
                refine ⟨396071743386041025785987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1056191315696109402095965 396071743386041025785987)
                ·
                  refine ⟨594107615079061538678981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396071743386041025785987 594107615079061538678981)
                  ·
                    refine ⟨111395177827324038502309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 594107615079061538678981 111395177827324038502309)
                    ·
                      rfl

theorem cell22_325412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_325412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325412 prefixEnd_325412 := by exact prefixLift 325412
  have htrace : WordTrace (prefixWord ++ tailWord_325412) baseStart_325412 baseEnd_325412 := by
    simpa [prefixWord, tailWord_325412, baseEnd_325412] using wordTrace_append hprefix tailTrace_325412
  have hstable : (prefixWord ++ tailWord_325412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325412).length < 2 ^ (prefixWord ++ tailWord_325412).sum := by decide
  have hdescent : baseEnd_325412 < baseStart_325412 := by decide
  rcases family_descends (prefixWord ++ tailWord_325412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325427 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 6]
def baseStart_325427 : Nat := 118140960795 + 325427 * 2 ^ 59
def prefixEnd_325427 : Nat := 4983230072969 + 3 ^ 40 * 325427 * 2
def baseEnd_325427 : Nat := 37133437544622999792421

theorem tailTrace_325427 : CollatzResearch.WordTrace tailWord_325427 prefixEnd_325427 37133437544622999792421 := by
  unfold tailWord_325427
  simp only [CollatzResearch.WordTrace]
  refine ⟨11869297792041032351878535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7912865194694021567919023 11869297792041032351878535)
  ·
    refine ⟨17803946688061548527817803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11869297792041032351878535 17803946688061548527817803)
    ·
      refine ⟨26705920032092322791726705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17803946688061548527817803 26705920032092322791726705)
      ·
        refine ⟨20029440024069242093795029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26705920032092322791726705 20029440024069242093795029)
        ·
          refine ⟨469440000564122861573321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 20029440024069242093795029 469440000564122861573321)
          ·
            refine ⟨352080000423092146179991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469440000564122861573321 352080000423092146179991)
            ·
              refine ⟨528120000634638219269987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352080000423092146179991 528120000634638219269987)
              ·
                refine ⟨792180000951957328904981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528120000634638219269987 792180000951957328904981)
                ·
                  refine ⟨37133437544622999792421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 792180000951957328904981 37133437544622999792421)
                  ·
                    rfl

theorem cell22_325427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 6].length) (baseStart_325427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325427 prefixEnd_325427 := by exact prefixLift 325427
  have htrace : WordTrace (prefixWord ++ tailWord_325427) baseStart_325427 baseEnd_325427 := by
    simpa [prefixWord, tailWord_325427, baseEnd_325427] using wordTrace_append hprefix tailTrace_325427
  have hstable : (prefixWord ++ tailWord_325427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325427).length < 2 ^ (prefixWord ++ tailWord_325427).sum := by decide
  have hdescent : baseEnd_325427 < baseStart_325427 := by decide
  rcases family_descends (prefixWord ++ tailWord_325427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325446 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_325446 : Nat := 118140960795 + 325446 * 2 ^ 59
def prefixEnd_325446 : Nat := 4983230072969 + 3 ^ 40 * 325446 * 2
def baseEnd_325446 : Nat := 111406816722159283152205

theorem tailTrace_325446 : CollatzResearch.WordTrace tailWord_325446 prefixEnd_325446 111406816722159283152205 := by
  unfold tailWord_325446
  simp only [CollatzResearch.WordTrace]
  refine ⟨370937211842881206150631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7913327185981465731213461 370937211842881206150631)
  ·
    refine ⟨556405817764321809225947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 370937211842881206150631 556405817764321809225947)
    ·
      refine ⟨834608726646482713838921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556405817764321809225947 834608726646482713838921)
      ·
        refine ⟨625956544984862035379191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 834608726646482713838921 625956544984862035379191)
        ·
          refine ⟨938934817477293053068787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625956544984862035379191 938934817477293053068787)
          ·
            refine ⟨1408402226215939579603181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938934817477293053068787 1408402226215939579603181)
            ·
              refine ⟨528150834830977342351193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1408402226215939579603181 528150834830977342351193)
              ·
                refine ⟨396113126123233006763395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528150834830977342351193 396113126123233006763395)
                ·
                  refine ⟨594169689184849510145093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396113126123233006763395 594169689184849510145093)
                  ·
                    refine ⟨111406816722159283152205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 594169689184849510145093 111406816722159283152205)
                    ·
                      rfl

theorem cell22_325446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_325446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325446 prefixEnd_325446 := by exact prefixLift 325446
  have htrace : WordTrace (prefixWord ++ tailWord_325446) baseStart_325446 baseEnd_325446 := by
    simpa [prefixWord, tailWord_325446, baseEnd_325446] using wordTrace_append hprefix tailTrace_325446
  have hstable : (prefixWord ++ tailWord_325446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325446).length < 2 ^ (prefixWord ++ tailWord_325446).sum := by decide
  have hdescent : baseEnd_325446 < baseStart_325446 := by decide
  rcases family_descends (prefixWord ++ tailWord_325446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325457 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 2, 4]
def baseStart_325457 : Nat := 118140960795 + 325457 * 2 ^ 59
def prefixEnd_325457 : Nat := 4983230072969 + 3 ^ 40 * 325457 * 2
def baseEnd_325457 : Nat := 111410582246958921127171

theorem tailTrace_325457 : CollatzResearch.WordTrace tailWord_325457 prefixEnd_325457 111410582246958921127171 := by
  unfold tailWord_325457
  simp only [CollatzResearch.WordTrace]
  refine ⟨11870391981932347475470625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7913594654621564983647083 11870391981932347475470625)
  ·
    refine ⟨8902793986449260606602969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11870391981932347475470625 8902793986449260606602969)
    ·
      refine ⟨6677095489836945454952227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8902793986449260606602969 6677095489836945454952227)
      ·
        refine ⟨10015643234755418182428341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6677095489836945454952227 10015643234755418182428341)
        ·
          refine ⟨938966553258320454602657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10015643234755418182428341 938966553258320454602657)
          ·
            refine ⟨704224914943740340951993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 938966553258320454602657 704224914943740340951993)
            ·
              refine ⟨528168686207805255713995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704224914943740340951993 528168686207805255713995)
              ·
                refine ⟨792253029311707883570993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528168686207805255713995 792253029311707883570993)
                ·
                  refine ⟨594189771983780912678245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 792253029311707883570993 594189771983780912678245)
                  ·
                    refine ⟨111410582246958921127171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 594189771983780912678245 111410582246958921127171)
                    ·
                      rfl

theorem cell22_325457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_325457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325457 prefixEnd_325457 := by exact prefixLift 325457
  have htrace : WordTrace (prefixWord ++ tailWord_325457) baseStart_325457 baseEnd_325457 := by
    simpa [prefixWord, tailWord_325457, baseEnd_325457] using wordTrace_append hprefix tailTrace_325457
  have hstable : (prefixWord ++ tailWord_325457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325457).length < 2 ^ (prefixWord ++ tailWord_325457).sum := by decide
  have hdescent : baseEnd_325457 < baseStart_325457 := by decide
  rcases family_descends (prefixWord ++ tailWord_325457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325485 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_325485 : Nat := 118140960795 + 325485 * 2 ^ 59
def prefixEnd_325485 : Nat := 4983230072969 + 3 ^ 40 * 325485 * 2
def baseEnd_325485 : Nat := 111420167219176181427085

theorem tailTrace_325485 : CollatzResearch.WordTrace tailWord_325485 prefixEnd_325485 111420167219176181427085 := by
  unfold tailWord_325485
  simp only [CollatzResearch.WordTrace]
  refine ⟨11871413225830908257489909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7914275483887272171659939 11871413225830908257489909)
  ·
    refine ⟨1112944989921647649139679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11871413225830908257489909 1112944989921647649139679)
    ·
      refine ⟨1669417484882471473709519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112944989921647649139679 1669417484882471473709519)
      ·
        refine ⟨2504126227323707210564279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669417484882471473709519 2504126227323707210564279)
        ·
          refine ⟨3756189340985560815846419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504126227323707210564279 3756189340985560815846419)
          ·
            refine ⟨5634284011478341223769629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756189340985560815846419 5634284011478341223769629)
            ·
              refine ⟨2112856504304377958913611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5634284011478341223769629 2112856504304377958913611)
              ·
                refine ⟨3169284756456566938370417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2112856504304377958913611 3169284756456566938370417)
                ·
                  refine ⟨2376963567342425203777813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3169284756456566938370417 2376963567342425203777813)
                  ·
                    refine ⟨111420167219176181427085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2376963567342425203777813 111420167219176181427085)
                    ·
                      rfl

theorem cell22_325485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_325485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325485 prefixEnd_325485 := by exact prefixLift 325485
  have htrace : WordTrace (prefixWord ++ tailWord_325485) baseStart_325485 baseEnd_325485 := by
    simpa [prefixWord, tailWord_325485, baseEnd_325485] using wordTrace_append hprefix tailTrace_325485
  have hstable : (prefixWord ++ tailWord_325485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325485).length < 2 ^ (prefixWord ++ tailWord_325485).sum := by decide
  have hdescent : baseEnd_325485 < baseStart_325485 := by decide
  rcases family_descends (prefixWord ++ tailWord_325485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325532 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_325532 : Nat := 118140960795 + 325532 * 2 ^ 59
def prefixEnd_325532 : Nat := 4983230072969 + 3 ^ 40 * 325532 * 2
def baseEnd_325532 : Nat := 111436256279683725501941

theorem tailTrace_325532 : CollatzResearch.WordTrace tailWord_325532 prefixEnd_325532 111436256279683725501941 := by
  unfold tailWord_325532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5936563728330317642225425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7915418304440423522967233 5936563728330317642225425)
  ·
    refine ⟨4452422796247738231669069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5936563728330317642225425 4452422796247738231669069)
    ·
      refine ⟨1669658548592901836875901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4452422796247738231669069 1669658548592901836875901)
      ·
        refine ⟨626121955722338188828463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1669658548592901836875901 626121955722338188828463)
        ·
          refine ⟨939182933583507283242695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626121955722338188828463 939182933583507283242695)
          ·
            refine ⟨1408774400375260924864043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939182933583507283242695 1408774400375260924864043)
            ·
              refine ⟨2113161600562891387296065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408774400375260924864043 2113161600562891387296065)
              ·
                refine ⟨1584871200422168540472049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2113161600562891387296065 1584871200422168540472049)
                ·
                  refine ⟨1188653400316626405354037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1584871200422168540472049 1188653400316626405354037)
                  ·
                    refine ⟨111436256279683725501941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1188653400316626405354037 111436256279683725501941)
                    ·
                      rfl

theorem cell22_325532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_325532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325532 prefixEnd_325532 := by exact prefixLift 325532
  have htrace : WordTrace (prefixWord ++ tailWord_325532) baseStart_325532 baseEnd_325532 := by
    simpa [prefixWord, tailWord_325532, baseEnd_325532] using wordTrace_append hprefix tailTrace_325532
  have hstable : (prefixWord ++ tailWord_325532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325532).length < 2 ^ (prefixWord ++ tailWord_325532).sum := by decide
  have hdescent : baseEnd_325532 < baseStart_325532 := by decide
  rcases family_descends (prefixWord ++ tailWord_325532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325592 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 2, 4]
def baseStart_325592 : Nat := 118140960795 + 325592 * 2 ^ 59
def prefixEnd_325592 : Nat := 4983230072969 + 3 ^ 40 * 325592 * 2
def baseEnd_325592 : Nat := 111456795505863569001757

theorem tailTrace_325592 : CollatzResearch.WordTrace tailWord_325592 prefixEnd_325592 111456795505863569001757 := by
  unfold tailWord_325592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5937657918221632765817515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7916877224295510354423353 5937657918221632765817515)
  ·
    refine ⟨8906486877332449148726273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5937657918221632765817515 8906486877332449148726273)
    ·
      refine ⟨6679865157999336861544705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8906486877332449148726273 6679865157999336861544705)
      ·
        refine ⟨5009898868499502646158529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6679865157999336861544705 5009898868499502646158529)
        ·
          refine ⟨3757424151374626984618897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5009898868499502646158529 3757424151374626984618897)
          ·
            refine ⟨2818068113530970238464173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3757424151374626984618897 2818068113530970238464173)
            ·
              refine ⟨1056775542574113839424065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2818068113530970238464173 1056775542574113839424065)
              ·
                refine ⟨792581656930585379568049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1056775542574113839424065 792581656930585379568049)
                ·
                  refine ⟨594436242697939034676037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 792581656930585379568049 594436242697939034676037)
                  ·
                    refine ⟨111456795505863569001757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 594436242697939034676037 111456795505863569001757)
                    ·
                      rfl

theorem cell22_325592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_325592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325592 prefixEnd_325592 := by exact prefixLift 325592
  have htrace : WordTrace (prefixWord ++ tailWord_325592) baseStart_325592 baseEnd_325592 := by
    simpa [prefixWord, tailWord_325592, baseEnd_325592] using wordTrace_append hprefix tailTrace_325592
  have hstable : (prefixWord ++ tailWord_325592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325592).length < 2 ^ (prefixWord ++ tailWord_325592).sum := by decide
  have hdescent : baseEnd_325592 < baseStart_325592 := by decide
  rcases family_descends (prefixWord ++ tailWord_325592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325635 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 9]
def baseStart_325635 : Nat := 118140960795 + 325635 * 2 ^ 59
def prefixEnd_325635 : Nat := 4983230072969 + 3 ^ 40 * 325635 * 2
def baseEnd_325635 : Nat := 37157171761541930058875

theorem tailTrace_325635 : CollatzResearch.WordTrace tailWord_325635 prefixEnd_325635 37157171761541930058875 := by
  unfold tailWord_325635
  simp only [CollatzResearch.WordTrace]
  refine ⟨11876884175287483875450359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7917922783524989250300239 11876884175287483875450359)
  ·
    refine ⟨17815326262931225813175539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11876884175287483875450359 17815326262931225813175539)
    ·
      refine ⟨26722989394396838719763309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17815326262931225813175539 26722989394396838719763309)
      ·
        refine ⟨10021121022898814519911241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26722989394396838719763309 10021121022898814519911241)
        ·
          refine ⟨7515840767174110889933431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10021121022898814519911241 7515840767174110889933431)
          ·
            refine ⟨11273761150761166334900147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7515840767174110889933431 11273761150761166334900147)
            ·
              refine ⟨16910641726141749502350221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11273761150761166334900147 16910641726141749502350221)
              ·
                refine ⟨6341490647303156063381333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16910641726141749502350221 6341490647303156063381333)
                ·
                  refine ⟨37157171761541930058875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6341490647303156063381333 37157171761541930058875)
                  ·
                    rfl

theorem cell22_325635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 9].length) (baseStart_325635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325635 prefixEnd_325635 := by exact prefixLift 325635
  have htrace : WordTrace (prefixWord ++ tailWord_325635) baseStart_325635 baseEnd_325635 := by
    simpa [prefixWord, tailWord_325635, baseEnd_325635] using wordTrace_append hprefix tailTrace_325635
  have hstable : (prefixWord ++ tailWord_325635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325635).length < 2 ^ (prefixWord ++ tailWord_325635).sum := by decide
  have hdescent : baseEnd_325635 < baseStart_325635 := by decide
  rcases family_descends (prefixWord ++ tailWord_325635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325656 : List Nat := [2, 1, 2, 3, 2, 1, 3, 4, 1, 3]
def baseStart_325656 : Nat := 118140960795 + 325656 * 2 ^ 59
def prefixEnd_325656 : Nat := 4983230072969 + 3 ^ 40 * 325656 * 2
def baseEnd_325656 : Nat := 111478704013788735401561

theorem tailTrace_325656 : CollatzResearch.WordTrace tailWord_325656 prefixEnd_325656 111478704013788735401561 := by
  unfold tailWord_325656
  simp only [CollatzResearch.WordTrace]
  refine ⟨5938825054105702230982411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7918433405474269641309881 5938825054105702230982411)
  ·
    refine ⟨8908237581158553346473617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5938825054105702230982411 8908237581158553346473617)
    ·
      refine ⟨6681178185868915009855213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8908237581158553346473617 6681178185868915009855213)
      ·
        refine ⟨2505441819700843128695705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6681178185868915009855213 2505441819700843128695705)
        ·
          refine ⟨1879081364775632346521779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2505441819700843128695705 1879081364775632346521779)
          ·
            refine ⟨2818622047163448519782669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879081364775632346521779 2818622047163448519782669)
            ·
              refine ⟨1056983267686293194918501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2818622047163448519782669 1056983267686293194918501)
              ·
                refine ⟨198184362691179974047219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1056983267686293194918501 198184362691179974047219)
                ·
                  refine ⟨297276544036769961070829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198184362691179974047219 297276544036769961070829)
                  ·
                    refine ⟨111478704013788735401561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 297276544036769961070829 111478704013788735401561)
                    ·
                      rfl

theorem cell22_325656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_325656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325656 prefixEnd_325656 := by exact prefixLift 325656
  have htrace : WordTrace (prefixWord ++ tailWord_325656) baseStart_325656 baseEnd_325656 := by
    simpa [prefixWord, tailWord_325656, baseEnd_325656] using wordTrace_append hprefix tailTrace_325656
  have hstable : (prefixWord ++ tailWord_325656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325656).length < 2 ^ (prefixWord ++ tailWord_325656).sum := by decide
  have hdescent : baseEnd_325656 < baseStart_325656 := by decide
  rcases family_descends (prefixWord ++ tailWord_325656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325667 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 2, 5]
def baseStart_325667 : Nat := 118140960795 + 325667 * 2 ^ 59
def prefixEnd_325667 : Nat := 4983230072969 + 3 ^ 40 * 325667 * 2
def baseEnd_325667 : Nat := 111482469538588373376527

theorem tailTrace_325667 : CollatzResearch.WordTrace tailWord_325667 prefixEnd_325667 111482469538588373376527 := by
  unfold tailWord_325667
  simp only [CollatzResearch.WordTrace]
  refine ⟨11878051311171553340615255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7918700874114368893743503 11878051311171553340615255)
  ·
    refine ⟨17817076966757330010922883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11878051311171553340615255 17817076966757330010922883)
    ·
      refine ⟨26725615450135995016384325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17817076966757330010922883 26725615450135995016384325)
      ·
        refine ⟨5011052896900499065572061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26725615450135995016384325 5011052896900499065572061)
        ·
          refine ⟨1879144836337687149589523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5011052896900499065572061 1879144836337687149589523)
          ·
            refine ⟨2818717254506530724384285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879144836337687149589523 2818717254506530724384285)
            ·
              refine ⟨1057018970439949021644107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2818717254506530724384285 1057018970439949021644107)
              ·
                refine ⟨1585528455659923532466161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057018970439949021644107 1585528455659923532466161)
                ·
                  refine ⟨1189146341744942649349621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1585528455659923532466161 1189146341744942649349621)
                  ·
                    refine ⟨111482469538588373376527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1189146341744942649349621 111482469538588373376527)
                    ·
                      rfl

theorem cell22_325667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 5].length) (baseStart_325667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325667 prefixEnd_325667 := by exact prefixLift 325667
  have htrace : WordTrace (prefixWord ++ tailWord_325667) baseStart_325667 baseEnd_325667 := by
    simpa [prefixWord, tailWord_325667, baseEnd_325667] using wordTrace_append hprefix tailTrace_325667
  have hstable : (prefixWord ++ tailWord_325667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325667).length < 2 ^ (prefixWord ++ tailWord_325667).sum := by decide
  have hdescent : baseEnd_325667 < baseStart_325667 := by decide
  rcases family_descends (prefixWord ++ tailWord_325667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325727 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 6, 4]
def baseStart_325727 : Nat := 118140960795 + 325727 * 2 ^ 59
def prefixEnd_325727 : Nat := 4983230072969 + 3 ^ 40 * 325727 * 2
def baseEnd_325727 : Nat := 111503008764768216876343

theorem tailTrace_325727 : CollatzResearch.WordTrace tailWord_325727 prefixEnd_325727 111503008764768216876343 := by
  unfold tailWord_325727
  simp only [CollatzResearch.WordTrace]
  refine ⟨11880239690954183587799435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7920159793969455725199623 11880239690954183587799435)
  ·
    refine ⟨17820359536431275381699153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11880239690954183587799435 17820359536431275381699153)
    ·
      refine ⟨13365269652323456536274365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17820359536431275381699153 13365269652323456536274365)
      ·
        refine ⟨5011976119621296201102887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13365269652323456536274365 5011976119621296201102887)
        ·
          refine ⟨7517964179431944301654331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5011976119621296201102887 7517964179431944301654331)
          ·
            refine ⟨11276946269147916452481497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7517964179431944301654331 11276946269147916452481497)
            ·
              refine ⟨8457709701860937339361123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11276946269147916452481497 8457709701860937339361123)
              ·
                refine ⟨12686564552791406009041685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8457709701860937339361123 12686564552791406009041685)
                ·
                  refine ⟨594682713412097156673829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12686564552791406009041685 594682713412097156673829)
                  ·
                    refine ⟨111503008764768216876343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 594682713412097156673829 111503008764768216876343)
                    ·
                      rfl

theorem cell22_325727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_325727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325727 prefixEnd_325727 := by exact prefixLift 325727
  have htrace : WordTrace (prefixWord ++ tailWord_325727) baseStart_325727 baseEnd_325727 := by
    simpa [prefixWord, tailWord_325727, baseEnd_325727] using wordTrace_append hprefix tailTrace_325727
  have hstable : (prefixWord ++ tailWord_325727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325727).length < 2 ^ (prefixWord ++ tailWord_325727).sum := by decide
  have hdescent : baseEnd_325727 < baseStart_325727 := by decide
  rcases family_descends (prefixWord ++ tailWord_325727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325761 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 2, 4]
def baseStart_325761 : Nat := 118140960795 + 325761 * 2 ^ 59
def prefixEnd_325761 : Nat := 4983230072969 + 3 ^ 40 * 325761 * 2
def baseEnd_325761 : Nat := 111514647659603461526239

theorem tailTrace_325761 : CollatzResearch.WordTrace tailWord_325761 prefixEnd_325761 111514647659603461526239 := by
  unfold tailWord_325761
  simp only [CollatzResearch.WordTrace]
  refine ⟨11881479772831007394537137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7920986515220671596358091 11881479772831007394537137)
  ·
    refine ⟨8911109829623255545902853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11881479772831007394537137 8911109829623255545902853)
    ·
      refine ⟨1670833093054360414856785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8911109829623255545902853 1670833093054360414856785)
      ·
        refine ⟨1253124819790770311142589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1670833093054360414856785 1253124819790770311142589)
        ·
          refine ⟨469921807421538866678471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1253124819790770311142589 469921807421538866678471)
          ·
            refine ⟨704882711132308300017707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469921807421538866678471 704882711132308300017707)
            ·
              refine ⟨1057324066698462450026561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704882711132308300017707 1057324066698462450026561)
              ·
                refine ⟨792993050023846837519921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1057324066698462450026561 792993050023846837519921)
                ·
                  refine ⟨594744787517885128139941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 792993050023846837519921 594744787517885128139941)
                  ·
                    refine ⟨111514647659603461526239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 594744787517885128139941 111514647659603461526239)
                    ·
                      rfl

theorem cell22_325761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_325761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325761 prefixEnd_325761 := by exact prefixLift 325761
  have htrace : WordTrace (prefixWord ++ tailWord_325761) baseStart_325761 baseEnd_325761 := by
    simpa [prefixWord, tailWord_325761, baseEnd_325761] using wordTrace_append hprefix tailTrace_325761
  have hstable : (prefixWord ++ tailWord_325761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325761).length < 2 ^ (prefixWord ++ tailWord_325761).sum := by decide
  have hdescent : baseEnd_325761 < baseStart_325761 := by decide
  rcases family_descends (prefixWord ++ tailWord_325761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325780 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_325780 : Nat := 118140960795 + 325780 * 2 ^ 59
def prefixEnd_325780 : Nat := 4983230072969 + 3 ^ 40 * 325780 * 2
def baseEnd_325780 : Nat := 111521151747893745301181

theorem tailTrace_325780 : CollatzResearch.WordTrace tailWord_325780 prefixEnd_325780 111521151747893745301181 := by
  unfold tailWord_325780
  simp only [CollatzResearch.WordTrace]
  refine ⟨5941086379881086819739397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7921448506508115759652529 5941086379881086819739397)
  ·
    refine ⟨1113953696227703778701137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5941086379881086819739397 1113953696227703778701137)
    ·
      refine ⟨835465272170777834025853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1113953696227703778701137 835465272170777834025853)
      ·
        refine ⟨313299477064041687759695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 835465272170777834025853 313299477064041687759695)
        ·
          refine ⟨469949215596062531639543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313299477064041687759695 469949215596062531639543)
          ·
            refine ⟨704923823394093797459315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469949215596062531639543 704923823394093797459315)
            ·
              refine ⟨1057385735091140696188973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704923823394093797459315 1057385735091140696188973)
              ·
                refine ⟨396519650659177761070865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1057385735091140696188973 396519650659177761070865)
                ·
                  refine ⟨297389737994383320803149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396519650659177761070865 297389737994383320803149)
                  ·
                    refine ⟨111521151747893745301181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 297389737994383320803149 111521151747893745301181)
                    ·
                      rfl

theorem cell22_325780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_325780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325780 prefixEnd_325780 := by exact prefixLift 325780
  have htrace : WordTrace (prefixWord ++ tailWord_325780) baseStart_325780 baseEnd_325780 := by
    simpa [prefixWord, tailWord_325780, baseEnd_325780] using wordTrace_append hprefix tailTrace_325780
  have hstable : (prefixWord ++ tailWord_325780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325780).length < 2 ^ (prefixWord ++ tailWord_325780).sum := by decide
  have hdescent : baseEnd_325780 < baseStart_325780 := by decide
  rcases family_descends (prefixWord ++ tailWord_325780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325834 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_325834 : Nat := 118140960795 + 325834 * 2 ^ 59
def prefixEnd_325834 : Nat := 4983230072969 + 3 ^ 40 * 325834 * 2
def baseEnd_325834 : Nat := 111539637051455604451015

theorem tailTrace_325834 : CollatzResearch.WordTrace tailWord_325834 prefixEnd_325834 111539637051455604451015 := by
  unfold tailWord_325834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971035575391635215486139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7922761534377693907963037 2971035575391635215486139)
  ·
    refine ⟨4456553363087452823229209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2971035575391635215486139 4456553363087452823229209)
    ·
      refine ⟨3342415022315589617421907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4456553363087452823229209 3342415022315589617421907)
      ·
        refine ⟨5013622533473384426132861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3342415022315589617421907 5013622533473384426132861)
        ·
          refine ⟨1880108450052519159799823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5013622533473384426132861 1880108450052519159799823)
          ·
            refine ⟨2820162675078778739699735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880108450052519159799823 2820162675078778739699735)
            ·
              refine ⟨4230244012618168109549603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2820162675078778739699735 4230244012618168109549603)
              ·
                refine ⟨6345366018927252164324405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4230244012618168109549603 6345366018927252164324405)
                ·
                  refine ⟨594878064274429890405413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6345366018927252164324405 594878064274429890405413)
                  ·
                    refine ⟨111539637051455604451015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 594878064274429890405413 111539637051455604451015)
                    ·
                      rfl

theorem cell22_325834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_325834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325834 prefixEnd_325834 := by exact prefixLift 325834
  have htrace : WordTrace (prefixWord ++ tailWord_325834) baseStart_325834 baseEnd_325834 := by
    simpa [prefixWord, tailWord_325834, baseEnd_325834] using wordTrace_append hprefix tailTrace_325834
  have hstable : (prefixWord ++ tailWord_325834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325834).length < 2 ^ (prefixWord ++ tailWord_325834).sum := by decide
  have hdescent : baseEnd_325834 < baseStart_325834 := by decide
  rcases family_descends (prefixWord ++ tailWord_325834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325881 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 2, 3]
def baseStart_325881 : Nat := 118140960795 + 325881 * 2 ^ 59
def prefixEnd_325881 : Nat := 4983230072969 + 3 ^ 40 * 325881 * 2
def baseEnd_325881 : Nat := 111555726111963148525871

theorem tailTrace_325881 : CollatzResearch.WordTrace tailWord_325881 prefixEnd_325881 111555726111963148525871 := by
  unfold tailWord_325881
  simp only [CollatzResearch.WordTrace]
  refine ⟨11885856532396267888905497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7923904354930845259270331 11885856532396267888905497)
  ·
    refine ⟨8914392399297200916679123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11885856532396267888905497 8914392399297200916679123)
    ·
      refine ⟨13371588598945801375018685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8914392399297200916679123 13371588598945801375018685)
      ·
        refine ⟨5014345724604675515632007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13371588598945801375018685 5014345724604675515632007)
        ·
          refine ⟨7521518586907013273448011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5014345724604675515632007 7521518586907013273448011)
          ·
            refine ⟨11282277880360519910172017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7521518586907013273448011 11282277880360519910172017)
            ·
              refine ⟨8461708410270389932629013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11282277880360519910172017 8461708410270389932629013)
              ·
                refine ⟨396642581731424528091985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8461708410270389932629013 396642581731424528091985)
                ·
                  refine ⟨297481936298568396068989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396642581731424528091985 297481936298568396068989)
                  ·
                    refine ⟨111555726111963148525871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 297481936298568396068989 111555726111963148525871)
                    ·
                      rfl

theorem cell22_325881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 3].length) (baseStart_325881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325881 prefixEnd_325881 := by exact prefixLift 325881
  have htrace : WordTrace (prefixWord ++ tailWord_325881) baseStart_325881 baseEnd_325881 := by
    simpa [prefixWord, tailWord_325881, baseEnd_325881] using wordTrace_append hprefix tailTrace_325881
  have hstable : (prefixWord ++ tailWord_325881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325881).length < 2 ^ (prefixWord ++ tailWord_325881).sum := by decide
  have hdescent : baseEnd_325881 < baseStart_325881 := by decide
  rcases family_descends (prefixWord ++ tailWord_325881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325911 : List Nat := [1, 1, 3, 4, 1, 2, 4, 6]
def baseStart_325911 : Nat := 118140960795 + 325911 * 2 ^ 59
def prefixEnd_325911 : Nat := 4983230072969 + 3 ^ 40 * 325911 * 2
def baseEnd_325911 : Nat := 12396221747228118919531

theorem tailTrace_325911 : CollatzResearch.WordTrace tailWord_325911 prefixEnd_325911 12396221747228118919531 := by
  unfold tailWord_325911
  simp only [CollatzResearch.WordTrace]
  refine ⟨11886950722287583012497587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7924633814858388674998391 11886950722287583012497587)
  ·
    refine ⟨17830426083431374518746381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11886950722287583012497587 17830426083431374518746381)
    ·
      refine ⟨6686409781286765444529893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17830426083431374518746381 6686409781286765444529893)
      ·
        refine ⟨1253701833991268520849355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6686409781286765444529893 1253701833991268520849355)
        ·
          refine ⟨1880552750986902781274033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253701833991268520849355 1880552750986902781274033)
          ·
            refine ⟨1410414563240177085955525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1880552750986902781274033 1410414563240177085955525)
            ·
              refine ⟨264452730607533203616661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1410414563240177085955525 264452730607533203616661)
              ·
                refine ⟨12396221747228118919531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 264452730607533203616661 12396221747228118919531)
                ·
                  rfl

theorem cell22_325911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 6].length) (baseStart_325911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325911 prefixEnd_325911 := by exact prefixLift 325911
  have htrace : WordTrace (prefixWord ++ tailWord_325911) baseStart_325911 baseEnd_325911 := by
    simpa [prefixWord, tailWord_325911, baseEnd_325911] using wordTrace_append hprefix tailTrace_325911
  have hstable : (prefixWord ++ tailWord_325911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325911).length < 2 ^ (prefixWord ++ tailWord_325911).sum := by decide
  have hdescent : baseEnd_325911 < baseStart_325911 := by decide
  rcases family_descends (prefixWord ++ tailWord_325911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325917 : List Nat := [1, 4, 2, 3, 3, 1, 1, 3, 4]
def baseStart_325917 : Nat := 118140960795 + 325917 * 2 ^ 59
def prefixEnd_325917 : Nat := 4983230072969 + 3 ^ 40 * 325917 * 2
def baseEnd_325917 : Nat := 37189349882557018208587

theorem tailTrace_325917 : CollatzResearch.WordTrace tailWord_325917 prefixEnd_325917 37189349882557018208587 := by
  unfold tailWord_325917
  simp only [CollatzResearch.WordTrace]
  refine ⟨11887169560265846037216005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7924779706843897358144003 11887169560265846037216005)
  ·
    refine ⟨2228844292549846131978001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11887169560265846037216005 2228844292549846131978001)
    ·
      refine ⟨1671633219412384598983501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2228844292549846131978001 1671633219412384598983501)
      ·
        refine ⟨626862457279644224618813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1671633219412384598983501 626862457279644224618813)
        ·
          refine ⟨235073421479866584232055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 626862457279644224618813 235073421479866584232055)
          ·
            refine ⟨352610132219799876348083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235073421479866584232055 352610132219799876348083)
            ·
              refine ⟨528915198329699814522125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352610132219799876348083 528915198329699814522125)
              ·
                refine ⟨198343199373637430445797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 528915198329699814522125 198343199373637430445797)
                ·
                  refine ⟨37189349882557018208587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198343199373637430445797 37189349882557018208587)
                  ·
                    rfl

theorem cell22_325917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_325917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325917 prefixEnd_325917 := by exact prefixLift 325917
  have htrace : WordTrace (prefixWord ++ tailWord_325917) baseStart_325917 baseEnd_325917 := by
    simpa [prefixWord, tailWord_325917, baseEnd_325917] using wordTrace_append hprefix tailTrace_325917
  have hstable : (prefixWord ++ tailWord_325917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325917).length < 2 ^ (prefixWord ++ tailWord_325917).sum := by decide
  have hdescent : baseEnd_325917 < baseStart_325917 := by decide
  rcases family_descends (prefixWord ++ tailWord_325917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325928 : List Nat := [2, 1, 5, 1, 4, 1, 8]
def baseStart_325928 : Nat := 118140960795 + 325928 * 2 ^ 59
def prefixEnd_325928 : Nat := 4983230072969 + 3 ^ 40 * 325928 * 2
def baseEnd_325928 : Nat := 4132289450832247874101

theorem tailTrace_325928 : CollatzResearch.WordTrace tailWord_325928 prefixEnd_325928 4132289450832247874101 := by
  unfold tailWord_325928
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943785381612997457933219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7925047175483996610577625 5943785381612997457933219)
  ·
    refine ⟨8915678072419496186899829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5943785381612997457933219 8915678072419496186899829)
    ·
      refine ⟨835844819289327767521859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8915678072419496186899829 835844819289327767521859)
      ·
        refine ⟨1253767228933991651282789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835844819289327767521859 1253767228933991651282789)
        ·
          refine ⟨235081355425123434615523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1253767228933991651282789 235081355425123434615523)
          ·
            refine ⟨352622033137685151923285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235081355425123434615523 352622033137685151923285)
            ·
              refine ⟨4132289450832247874101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 352622033137685151923285 4132289450832247874101)
              ·
                rfl

theorem cell22_325928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 8].length) (baseStart_325928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325928 prefixEnd_325928 := by exact prefixLift 325928
  have htrace : WordTrace (prefixWord ++ tailWord_325928) baseStart_325928 baseEnd_325928 := by
    simpa [prefixWord, tailWord_325928, baseEnd_325928] using wordTrace_append hprefix tailTrace_325928
  have hstable : (prefixWord ++ tailWord_325928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325928).length < 2 ^ (prefixWord ++ tailWord_325928).sum := by decide
  have hdescent : baseEnd_325928 < baseStart_325928 := by decide
  rcases family_descends (prefixWord ++ tailWord_325928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325939 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 7]
def baseStart_325939 : Nat := 118140960795 + 325939 * 2 ^ 59
def prefixEnd_325939 : Nat := 4983230072969 + 3 ^ 40 * 325939 * 2
def baseEnd_325939 : Nat := 37191860232423443525231

theorem tailTrace_325939 : CollatzResearch.WordTrace tailWord_325939 prefixEnd_325939 37191860232423443525231 := by
  unfold tailWord_325939
  simp only [CollatzResearch.WordTrace]
  refine ⟨11887971966186143794516871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7925314644124095863011247 11887971966186143794516871)
  ·
    refine ⟨17831957949279215691775307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11887971966186143794516871 17831957949279215691775307)
    ·
      refine ⟨26747936923918823537662961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17831957949279215691775307 26747936923918823537662961)
      ·
        refine ⟨20060952692939117653247221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26747936923918823537662961 20060952692939117653247221)
        ·
          refine ⟨1880714314963042279991927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20060952692939117653247221 1880714314963042279991927)
          ·
            refine ⟨2821071472444563419987891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880714314963042279991927 2821071472444563419987891)
            ·
              refine ⟨4231607208666845129981837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821071472444563419987891 4231607208666845129981837)
              ·
                refine ⟨1586852703250066923743189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4231607208666845129981837 1586852703250066923743189)
                ·
                  refine ⟨37191860232423443525231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1586852703250066923743189 37191860232423443525231)
                  ·
                    rfl

theorem cell22_325939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 7].length) (baseStart_325939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325939 prefixEnd_325939 := by exact prefixLift 325939
  have htrace : WordTrace (prefixWord ++ tailWord_325939) baseStart_325939 baseEnd_325939 := by
    simpa [prefixWord, tailWord_325939, baseEnd_325939] using wordTrace_append hprefix tailTrace_325939
  have hstable : (prefixWord ++ tailWord_325939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325939).length < 2 ^ (prefixWord ++ tailWord_325939).sum := by decide
  have hdescent : baseEnd_325939 < baseStart_325939 := by decide
  rcases family_descends (prefixWord ++ tailWord_325939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325943 : List Nat := [1, 1, 3, 1, 2, 1, 1, 8, 1, 3]
def baseStart_325943 : Nat := 118140960795 + 325943 * 2 ^ 59
def prefixEnd_325943 : Nat := 4983230072969 + 3 ^ 40 * 325943 * 2
def baseEnd_325943 : Nat := 111576949979015653475681

theorem tailTrace_325943 : CollatzResearch.WordTrace tailWord_325943 prefixEnd_325943 111576949979015653475681 := by
  unfold tailWord_325943
  simp only [CollatzResearch.WordTrace]
  refine ⟨11888117858171652477662483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7925411905447768318441655 11888117858171652477662483)
  ·
    refine ⟨17832176787257478716493725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11888117858171652477662483 17832176787257478716493725)
    ·
      refine ⟨6687066295221554518685147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17832176787257478716493725 6687066295221554518685147)
      ·
        refine ⟨10030599442832331778027721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6687066295221554518685147 10030599442832331778027721)
        ·
          refine ⟨7522949582124248833520791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10030599442832331778027721 7522949582124248833520791)
          ·
            refine ⟨11284424373186373250281187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7522949582124248833520791 11284424373186373250281187)
            ·
              refine ⟨16926636559779559875421781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11284424373186373250281187 16926636559779559875421781)
              ·
                refine ⟨198359022184916717290099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 16926636559779559875421781 198359022184916717290099)
                ·
                  refine ⟨297538533277375075935149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198359022184916717290099 297538533277375075935149)
                  ·
                    refine ⟨111576949979015653475681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 297538533277375075935149 111576949979015653475681)
                    ·
                      rfl

theorem cell22_325943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_325943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325943 prefixEnd_325943 := by exact prefixLift 325943
  have htrace : WordTrace (prefixWord ++ tailWord_325943) baseStart_325943 baseEnd_325943 := by
    simpa [prefixWord, tailWord_325943, baseEnd_325943] using wordTrace_append hprefix tailTrace_325943
  have hstable : (prefixWord ++ tailWord_325943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325943).length < 2 ^ (prefixWord ++ tailWord_325943).sum := by decide
  have hdescent : baseEnd_325943 < baseStart_325943 := by decide
  rcases family_descends (prefixWord ++ tailWord_325943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325994 : List Nat := [3, 1, 3, 3, 1, 3, 2, 2, 1, 3]
def baseStart_325994 : Nat := 118140960795 + 325994 * 2 ^ 59
def prefixEnd_325994 : Nat := 4983230072969 + 3 ^ 40 * 325994 * 2
def baseEnd_325994 : Nat := 111594408321268520450525

theorem tailTrace_325994 : CollatzResearch.WordTrace tailWord_325994 prefixEnd_325994 111594408321268520450525 := by
  unfold tailWord_325994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2972494495246722046942259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7926651987324592125179357 2972494495246722046942259)
  ·
    refine ⟨4458741742870083070413389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2972494495246722046942259 4458741742870083070413389)
    ·
      refine ⟨1672028153576281151405021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4458741742870083070413389 1672028153576281151405021)
      ·
        refine ⟨627010557591105431776883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1672028153576281151405021 627010557591105431776883)
        ·
          refine ⟨940515836386658147665325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627010557591105431776883 940515836386658147665325)
          ·
            refine ⟨352693438644996805374497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 940515836386658147665325 352693438644996805374497)
            ·
              refine ⟨264520078983747604030873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352693438644996805374497 264520078983747604030873)
              ·
                refine ⟨198390059237810703023155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264520078983747604030873 198390059237810703023155)
                ·
                  refine ⟨297585088856716054534733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198390059237810703023155 297585088856716054534733)
                  ·
                    refine ⟨111594408321268520450525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 297585088856716054534733 111594408321268520450525)
                    ·
                      rfl

theorem cell22_325994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_325994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_325994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_325994 prefixEnd_325994 := by exact prefixLift 325994
  have htrace : WordTrace (prefixWord ++ tailWord_325994) baseStart_325994 baseEnd_325994 := by
    simpa [prefixWord, tailWord_325994, baseEnd_325994] using wordTrace_append hprefix tailTrace_325994
  have hstable : (prefixWord ++ tailWord_325994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325994).length < 2 ^ (prefixWord ++ tailWord_325994).sum := by decide
  have hdescent : baseEnd_325994 < baseStart_325994 := by decide
  rcases family_descends (prefixWord ++ tailWord_325994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326016 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 8, 3]
def baseStart_326016 : Nat := 118140960795 + 326016 * 2 ^ 59
def prefixEnd_326016 : Nat := 4983230072969 + 3 ^ 40 * 326016 * 2
def baseEnd_326016 : Nat := 111601939370867796400457

theorem tailTrace_326016 : CollatzResearch.WordTrace tailWord_326016 prefixEnd_326016 111601939370867796400457 := by
  unfold tailWord_326016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5945390193453592972534951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7927186924604790630046601 5945390193453592972534951)
  ·
    refine ⟨8918085290180389458802427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5945390193453592972534951 8918085290180389458802427)
    ·
      refine ⟨13377127935270584188203641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8918085290180389458802427 13377127935270584188203641)
      ·
        refine ⟨10032845951452938141152731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13377127935270584188203641 10032845951452938141152731)
        ·
          refine ⟨15049268927179407211729097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10032845951452938141152731 15049268927179407211729097)
          ·
            refine ⟨11286951695384555408796823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15049268927179407211729097 11286951695384555408796823)
            ·
              refine ⟨16930427543076833113195235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11286951695384555408796823 16930427543076833113195235)
              ·
                refine ⟨25395641314615249669792853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16930427543076833113195235 25395641314615249669792853)
                ·
                  refine ⟨297605171655647457067885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25395641314615249669792853 297605171655647457067885)
                  ·
                    refine ⟨111601939370867796400457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 297605171655647457067885 111601939370867796400457)
                    ·
                      rfl

theorem cell22_326016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8, 3].length) (baseStart_326016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326016 prefixEnd_326016 := by exact prefixLift 326016
  have htrace : WordTrace (prefixWord ++ tailWord_326016) baseStart_326016 baseEnd_326016 := by
    simpa [prefixWord, tailWord_326016, baseEnd_326016] using wordTrace_append hprefix tailTrace_326016
  have hstable : (prefixWord ++ tailWord_326016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326016).length < 2 ^ (prefixWord ++ tailWord_326016).sum := by decide
  have hdescent : baseEnd_326016 < baseStart_326016 := by decide
  rcases family_descends (prefixWord ++ tailWord_326016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326112 : List Nat := [2, 1, 1, 3, 1, 1, 7, 2, 1, 3]
def baseStart_326112 : Nat := 118140960795 + 326112 * 2 ^ 59
def prefixEnd_326112 : Nat := 4983230072969 + 3 ^ 40 * 326112 * 2
def baseEnd_326112 : Nat := 111634802132755546000163

theorem tailTrace_326112 : CollatzResearch.WordTrace tailWord_326112 prefixEnd_326112 111634802132755546000163 := by
  unfold tailWord_326112
  simp only [CollatzResearch.WordTrace]
  refine ⟨5947140897279697170282295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7929521196372929560376393 5947140897279697170282295)
  ·
    refine ⟨8920711345919545755423443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5947140897279697170282295 8920711345919545755423443)
    ·
      refine ⟨13381067018879318633135165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8920711345919545755423443 13381067018879318633135165)
      ·
        refine ⟨5017900132079744487425687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13381067018879318633135165 5017900132079744487425687)
        ·
          refine ⟨7526850198119616731138531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5017900132079744487425687 7526850198119616731138531)
          ·
            refine ⟨11290275297179425096707797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7526850198119616731138531 11290275297179425096707797)
            ·
              refine ⟨264615827277642775704089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11290275297179425096707797 264615827277642775704089)
              ·
                refine ⟨198461870458232081778067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264615827277642775704089 198461870458232081778067)
                ·
                  refine ⟨297692805687348122667101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198461870458232081778067 297692805687348122667101)
                  ·
                    refine ⟨111634802132755546000163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 297692805687348122667101 111634802132755546000163)
                    ·
                      rfl

theorem cell22_326112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 1, 3].length) (baseStart_326112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326112 prefixEnd_326112 := by exact prefixLift 326112
  have htrace : WordTrace (prefixWord ++ tailWord_326112) baseStart_326112 baseEnd_326112 := by
    simpa [prefixWord, tailWord_326112, baseEnd_326112] using wordTrace_append hprefix tailTrace_326112
  have hstable : (prefixWord ++ tailWord_326112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326112).length < 2 ^ (prefixWord ++ tailWord_326112).sum := by decide
  have hdescent : baseEnd_326112 < baseStart_326112 := by decide
  rcases family_descends (prefixWord ++ tailWord_326112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326125 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 5]
def baseStart_326125 : Nat := 118140960795 + 326125 * 2 ^ 59
def prefixEnd_326125 : Nat := 4983230072969 + 3 ^ 40 * 326125 * 2
def baseEnd_326125 : Nat := 37213084099475948475041

theorem tailTrace_326125 : CollatzResearch.WordTrace tailWord_326125 prefixEnd_326125 37213084099475948475041 := by
  unfold tailWord_326125
  simp only [CollatzResearch.WordTrace]
  refine ⟨11894755943512297560787829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7929837295674865040525219 11894755943512297560787829)
  ·
    refine ⟨1115133369704277896323859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11894755943512297560787829 1115133369704277896323859)
    ·
      refine ⟨1672700054556416844485789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1115133369704277896323859 1672700054556416844485789)
      ·
        refine ⟨627262520458656316682171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1672700054556416844485789 627262520458656316682171)
        ·
          refine ⟨940893780687984475023257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627262520458656316682171 940893780687984475023257)
          ·
            refine ⟨705670335515988356267443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 940893780687984475023257 705670335515988356267443)
            ·
              refine ⟨1058505503273982534401165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705670335515988356267443 1058505503273982534401165)
              ·
                refine ⟨396939563727743450400437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1058505503273982534401165 396939563727743450400437)
                ·
                  refine ⟨37213084099475948475041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 396939563727743450400437 37213084099475948475041)
                  ·
                    rfl

theorem cell22_326125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_326125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326125 prefixEnd_326125 := by exact prefixLift 326125
  have htrace : WordTrace (prefixWord ++ tailWord_326125) baseStart_326125 baseEnd_326125 := by
    simpa [prefixWord, tailWord_326125, baseEnd_326125] using wordTrace_append hprefix tailTrace_326125
  have hstable : (prefixWord ++ tailWord_326125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326125).length < 2 ^ (prefixWord ++ tailWord_326125).sum := by decide
  have hdescent : baseEnd_326125 < baseStart_326125 := by decide
  rcases family_descends (prefixWord ++ tailWord_326125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326136 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 8]
def baseStart_326136 : Nat := 118140960795 + 326136 * 2 ^ 59
def prefixEnd_326136 : Nat := 4983230072969 + 3 ^ 40 * 326136 * 2
def baseEnd_326136 : Nat := 37214339274409161133363

theorem tailTrace_326136 : CollatzResearch.WordTrace tailWord_326136 prefixEnd_326136 37214339274409161133363 := by
  unfold tailWord_326136
  simp only [CollatzResearch.WordTrace]
  refine ⟨5947578573236223219719131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7930104764314964292958841 5947578573236223219719131)
  ·
    refine ⟨8921367859854334829578697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5947578573236223219719131 8921367859854334829578697)
    ·
      refine ⟨6691025894890751122184023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8921367859854334829578697 6691025894890751122184023)
      ·
        refine ⟨10036538842336126683276035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6691025894890751122184023 10036538842336126683276035)
        ·
          refine ⟨15054808263504190024914053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10036538842336126683276035 15054808263504190024914053)
          ·
            refine ⟨2822776549407035629671385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15054808263504190024914053 2822776549407035629671385)
            ·
              refine ⟨2117082412055276722253539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2822776549407035629671385 2117082412055276722253539)
              ·
                refine ⟨3175623618082915083380309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117082412055276722253539 3175623618082915083380309)
                ·
                  refine ⟨37214339274409161133363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3175623618082915083380309 37214339274409161133363)
                  ·
                    rfl

theorem cell22_326136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_326136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326136 prefixEnd_326136 := by exact prefixLift 326136
  have htrace : WordTrace (prefixWord ++ tailWord_326136) baseStart_326136 baseEnd_326136 := by
    simpa [prefixWord, tailWord_326136, baseEnd_326136] using wordTrace_append hprefix tailTrace_326136
  have hstable : (prefixWord ++ tailWord_326136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326136).length < 2 ^ (prefixWord ++ tailWord_326136).sum := by decide
  have hdescent : baseEnd_326136 < baseStart_326136 := by decide
  rcases family_descends (prefixWord ++ tailWord_326136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326138 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_326138 : Nat := 118140960795 + 326138 * 2 ^ 59
def prefixEnd_326138 : Nat := 4983230072969 + 3 ^ 40 * 326138 * 2
def baseEnd_326138 : Nat := 111643702464100144850083

theorem tailTrace_326138 : CollatzResearch.WordTrace tailWord_326138 prefixEnd_326138 111643702464100144850083 := by
  unfold tailWord_326138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2973807523116300195252767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7930153394976800520674045 2973807523116300195252767)
  ·
    refine ⟨4460711284674450292879151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2973807523116300195252767 4460711284674450292879151)
    ·
      refine ⟨6691066927011675439318727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4460711284674450292879151 6691066927011675439318727)
      ·
        refine ⟨10036600390517513158978091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6691066927011675439318727 10036600390517513158978091)
        ·
          refine ⟨15054900585776269738467137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10036600390517513158978091 15054900585776269738467137)
          ·
            refine ⟨11291175439332202303850353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15054900585776269738467137 11291175439332202303850353)
            ·
              refine ⟨8468381579499151727887765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11291175439332202303850353 8468381579499151727887765)
              ·
                refine ⟨396955386539022737244739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8468381579499151727887765 396955386539022737244739)
                ·
                  refine ⟨595433079808534105867109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396955386539022737244739 595433079808534105867109)
                  ·
                    refine ⟨111643702464100144850083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 595433079808534105867109 111643702464100144850083)
                    ·
                      rfl

theorem cell22_326138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_326138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326138 prefixEnd_326138 := by exact prefixLift 326138
  have htrace : WordTrace (prefixWord ++ tailWord_326138) baseStart_326138 baseEnd_326138 := by
    simpa [prefixWord, tailWord_326138, baseEnd_326138] using wordTrace_append hprefix tailTrace_326138
  have hstable : (prefixWord ++ tailWord_326138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326138).length < 2 ^ (prefixWord ++ tailWord_326138).sum := by decide
  have hdescent : baseEnd_326138 < baseStart_326138 := by decide
  rcases family_descends (prefixWord ++ tailWord_326138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326206 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_326206 : Nat := 118140960795 + 326206 * 2 ^ 59
def prefixEnd_326206 : Nat := 4983230072969 + 3 ^ 40 * 326206 * 2
def baseEnd_326206 : Nat := 111666980253770634149875

theorem tailTrace_326206 : CollatzResearch.WordTrace tailWord_326206 prefixEnd_326206 111666980253770634149875 := by
  unfold tailWord_326206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487213782027356049310809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7931806837479232262990981 1487213782027356049310809)
  ·
    refine ⟨1115410336520517036983107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1487213782027356049310809 1115410336520517036983107)
    ·
      refine ⟨1673115504780775555474661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1115410336520517036983107 1673115504780775555474661)
      ·
        refine ⟨313709157146395416651499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1673115504780775555474661 313709157146395416651499)
        ·
          refine ⟨470563735719593124977249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313709157146395416651499 470563735719593124977249)
          ·
            refine ⟨352922801789694843732937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470563735719593124977249 352922801789694843732937)
            ·
              refine ⟨264692101342271132799703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352922801789694843732937 264692101342271132799703)
              ·
                refine ⟨397038152013406699199555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264692101342271132799703 397038152013406699199555)
                ·
                  refine ⟨595557228020110048799333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397038152013406699199555 595557228020110048799333)
                  ·
                    refine ⟨111666980253770634149875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 595557228020110048799333 111666980253770634149875)
                    ·
                      rfl

theorem cell22_326206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_326206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326206 prefixEnd_326206 := by exact prefixLift 326206
  have htrace : WordTrace (prefixWord ++ tailWord_326206) baseStart_326206 baseEnd_326206 := by
    simpa [prefixWord, tailWord_326206, baseEnd_326206] using wordTrace_append hprefix tailTrace_326206
  have hstable : (prefixWord ++ tailWord_326206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326206).length < 2 ^ (prefixWord ++ tailWord_326206).sum := by decide
  have hdescent : baseEnd_326206 < baseStart_326206 := by decide
  rcases family_descends (prefixWord ++ tailWord_326206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326333 : List Nat := [1, 4, 1, 2, 1, 13]
def baseStart_326333 : Nat := 118140960795 + 326333 * 2 ^ 59
def prefixEnd_326333 : Nat := 4983230072969 + 3 ^ 40 * 326333 * 2
def baseEnd_326333 : Nat := 1379141419125736249685

theorem tailTrace_326333 : CollatzResearch.WordTrace tailWord_326333 prefixEnd_326333 1379141419125736249685 := by
  unfold tailWord_326333
  simp only [CollatzResearch.WordTrace]
  refine ⟨11902342326758749084359653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7934894884505832722906435 11902342326758749084359653)
  ·
    refine ⟨2231689186267265453317435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11902342326758749084359653 2231689186267265453317435)
    ·
      refine ⟨3347533779400898179976153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2231689186267265453317435 3347533779400898179976153)
      ·
        refine ⟨2510650334550673634982115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3347533779400898179976153 2510650334550673634982115)
        ·
          refine ⟨3765975501826010452473173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2510650334550673634982115 3765975501826010452473173)
          ·
            refine ⟨1379141419125736249685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 3765975501826010452473173 1379141419125736249685)
            ·
              rfl

theorem cell22_326333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 13].length) (baseStart_326333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326333 prefixEnd_326333 := by exact prefixLift 326333
  have htrace : WordTrace (prefixWord ++ tailWord_326333) baseStart_326333 baseEnd_326333 := by
    simpa [prefixWord, tailWord_326333, baseEnd_326333] using wordTrace_append hprefix tailTrace_326333
  have hstable : (prefixWord ++ tailWord_326333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326333).length < 2 ^ (prefixWord ++ tailWord_326333).sum := by decide
  have hdescent : baseEnd_326333 < baseStart_326333 := by decide
  rcases family_descends (prefixWord ++ tailWord_326333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326335 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 2, 4]
def baseStart_326335 : Nat := 118140960795 + 326335 * 2 ^ 59
def prefixEnd_326335 : Nat := 4983230072969 + 3 ^ 40 * 326335 * 2
def baseEnd_326335 : Nat := 111711139590057297674479

theorem tailTrace_326335 : CollatzResearch.WordTrace tailWord_326335 prefixEnd_326335 111711139590057297674479 := by
  unfold tailWord_326335
  simp only [CollatzResearch.WordTrace]
  refine ⟨11902415272751503425932459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7934943515167668950621639 11902415272751503425932459)
  ·
    refine ⟨17853622909127255138898689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11902415272751503425932459 17853622909127255138898689)
    ·
      refine ⟨13390217181845441354174017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17853622909127255138898689 13390217181845441354174017)
      ·
        refine ⟨10042662886384081015630513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13390217181845441354174017 10042662886384081015630513)
        ·
          refine ⟨7531997164788060761722885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10042662886384081015630513 7531997164788060761722885)
          ·
            refine ⟨1412249468397761392823041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7531997164788060761722885 1412249468397761392823041)
            ·
              refine ⟨1059187101298321044617281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1412249468397761392823041 1059187101298321044617281)
              ·
                refine ⟨794390325973740783462961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1059187101298321044617281 794390325973740783462961)
                ·
                  refine ⟨595792744480305587597221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 794390325973740783462961 595792744480305587597221)
                  ·
                    refine ⟨111711139590057297674479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 595792744480305587597221 111711139590057297674479)
                    ·
                      rfl

theorem cell22_326335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_326335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326335 prefixEnd_326335 := by exact prefixLift 326335
  have htrace : WordTrace (prefixWord ++ tailWord_326335) baseStart_326335 baseEnd_326335 := by
    simpa [prefixWord, tailWord_326335, baseEnd_326335] using wordTrace_append hprefix tailTrace_326335
  have hstable : (prefixWord ++ tailWord_326335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326335).length < 2 ^ (prefixWord ++ tailWord_326335).sum := by decide
  have hdescent : baseEnd_326335 < baseStart_326335 := by decide
  rcases family_descends (prefixWord ++ tailWord_326335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326350 : List Nat := [4, 1, 1, 1, 3, 2, 3, 7]
def baseStart_326350 : Nat := 118140960795 + 326350 * 2 ^ 59
def prefixEnd_326350 : Nat := 4983230072969 + 3 ^ 40 * 326350 * 2
def baseEnd_326350 : Nat := 12412919377400250949937

theorem tailTrace_326350 : CollatzResearch.WordTrace tailWord_326350 prefixEnd_326350 12412919377400250949937 := by
  unfold tailWord_326350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487870295962145123466063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7935308245131440658485669 1487870295962145123466063)
  ·
    refine ⟨2231805443943217685199095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1487870295962145123466063 2231805443943217685199095)
    ·
      refine ⟨3347708165914826527798643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2231805443943217685199095 3347708165914826527798643)
      ·
        refine ⟨5021562248872239791697965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3347708165914826527798643 5021562248872239791697965)
        ·
          refine ⟨1883085843327089921886737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5021562248872239791697965 1883085843327089921886737)
          ·
            refine ⟨1412314382495317441415053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1883085843327089921886737 1412314382495317441415053)
            ·
              refine ⟨529617893435744040530645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1412314382495317441415053 529617893435744040530645)
              ·
                refine ⟨12412919377400250949937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 529617893435744040530645 12412919377400250949937)
                ·
                  rfl

theorem cell22_326350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_326350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326350 prefixEnd_326350 := by exact prefixLift 326350
  have htrace : WordTrace (prefixWord ++ tailWord_326350) baseStart_326350 baseEnd_326350 := by
    simpa [prefixWord, tailWord_326350, baseEnd_326350] using wordTrace_append hprefix tailTrace_326350
  have hstable : (prefixWord ++ tailWord_326350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326350).length < 2 ^ (prefixWord ++ tailWord_326350).sum := by decide
  have hdescent : baseEnd_326350 < baseStart_326350 := by decide
  rcases family_descends (prefixWord ++ tailWord_326350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326410 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_326410 : Nat := 118140960795 + 326410 * 2 ^ 59
def prefixEnd_326410 : Nat := 4983230072969 + 3 ^ 40 * 326410 * 2
def baseEnd_326410 : Nat := 111736813622782102049249

theorem tailTrace_326410 : CollatzResearch.WordTrace tailWord_326410 prefixEnd_326410 111736813622782102049249 := by
  unfold tailWord_326410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2976287686869947808728171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7936767164986527489941789 2976287686869947808728171)
  ·
    refine ⟨4464431530304921713092257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2976287686869947808728171 4464431530304921713092257)
    ·
      refine ⟨3348323647728691284819193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4464431530304921713092257 3348323647728691284819193)
      ·
        refine ⟨2511242735796518463614395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3348323647728691284819193 2511242735796518463614395)
        ·
          refine ⟨3766864103694777695421593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511242735796518463614395 3766864103694777695421593)
          ·
            refine ⟨2825148077771083271566195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3766864103694777695421593 2825148077771083271566195)
            ·
              refine ⟨4237722116656624907349293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825148077771083271566195 4237722116656624907349293)
              ·
                refine ⟨1589145793746234340255985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4237722116656624907349293 1589145793746234340255985)
                ·
                  refine ⟨1191859345309675755191989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1589145793746234340255985 1191859345309675755191989)
                  ·
                    refine ⟨111736813622782102049249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1191859345309675755191989 111736813622782102049249)
                    ·
                      rfl

theorem cell22_326410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_326410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326410 prefixEnd_326410 := by exact prefixLift 326410
  have htrace : WordTrace (prefixWord ++ tailWord_326410) baseStart_326410 baseEnd_326410 := by
    simpa [prefixWord, tailWord_326410, baseEnd_326410] using wordTrace_append hprefix tailTrace_326410
  have hstable : (prefixWord ++ tailWord_326410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326410).length < 2 ^ (prefixWord ++ tailWord_326410).sum := by decide
  have hdescent : baseEnd_326410 < baseStart_326410 := by decide
  rcases family_descends (prefixWord ++ tailWord_326410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326485 : List Nat := [1, 3, 2, 2, 2, 1, 1, 10]
def baseStart_326485 : Nat := 118140960795 + 326485 * 2 ^ 59
def prefixEnd_326485 : Nat := 4983230072969 + 3 ^ 40 * 326485 * 2
def baseEnd_326485 : Nat := 12418054183945211824891

theorem tailTrace_326485 : CollatzResearch.WordTrace tailWord_326485 prefixEnd_326485 12418054183945211824891 := by
  unfold tailWord_326485
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907886222208079043892909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7938590814805386029261939 11907886222208079043892909)
  ·
    refine ⟨4465457333328029641459841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11907886222208079043892909 4465457333328029641459841)
    ·
      refine ⟨3349092999996022231094881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4465457333328029641459841 3349092999996022231094881)
      ·
        refine ⟨2511819749997016673321161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3349092999996022231094881 2511819749997016673321161)
        ·
          refine ⟨1883864812497762504990871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2511819749997016673321161 1883864812497762504990871)
          ·
            refine ⟨2825797218746643757486307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883864812497762504990871 2825797218746643757486307)
            ·
              refine ⟨4238695828119965636229461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825797218746643757486307 4238695828119965636229461)
              ·
                refine ⟨12418054183945211824891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4238695828119965636229461 12418054183945211824891)
                ·
                  rfl

theorem cell22_326485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 10].length) (baseStart_326485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326485 prefixEnd_326485 := by exact prefixLift 326485
  have htrace : WordTrace (prefixWord ++ tailWord_326485) baseStart_326485 baseEnd_326485 := by
    simpa [prefixWord, tailWord_326485, baseEnd_326485] using wordTrace_append hprefix tailTrace_326485
  have hstable : (prefixWord ++ tailWord_326485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326485).length < 2 ^ (prefixWord ++ tailWord_326485).sum := by decide
  have hdescent : baseEnd_326485 < baseStart_326485 := by decide
  rcases family_descends (prefixWord ++ tailWord_326485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326487 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 2, 4]
def baseStart_326487 : Nat := 118140960795 + 326487 * 2 ^ 59
def prefixEnd_326487 : Nat := 4983230072969 + 3 ^ 40 * 326487 * 2
def baseEnd_326487 : Nat := 111763172296379567874013

theorem tailTrace_326487 : CollatzResearch.WordTrace tailWord_326487 prefixEnd_326487 111763172296379567874013 := by
  unfold tailWord_326487
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907959168200833385465715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7938639445467222256977143 11907959168200833385465715)
  ·
    refine ⟨17861938752301250078198573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11907959168200833385465715 17861938752301250078198573)
    ·
      refine ⟨6698227032112968779324465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17861938752301250078198573 6698227032112968779324465)
      ·
        refine ⟨5023670274084726584493349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6698227032112968779324465 5023670274084726584493349)
        ·
          refine ⟨941938176390886234592503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5023670274084726584493349 941938176390886234592503)
          ·
            refine ⟨1412907264586329351888755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941938176390886234592503 1412907264586329351888755)
            ·
              refine ⟨2119360896879494027833133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412907264586329351888755 2119360896879494027833133)
              ·
                refine ⟨794760336329810260437425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2119360896879494027833133 794760336329810260437425)
                ·
                  refine ⟨596070252247357695328069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 794760336329810260437425 596070252247357695328069)
                  ·
                    refine ⟨111763172296379567874013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 596070252247357695328069 111763172296379567874013)
                    ·
                      rfl

theorem cell22_326487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_326487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326487 prefixEnd_326487 := by exact prefixLift 326487
  have htrace : WordTrace (prefixWord ++ tailWord_326487) baseStart_326487 baseEnd_326487 := by
    simpa [prefixWord, tailWord_326487, baseEnd_326487] using wordTrace_append hprefix tailTrace_326487
  have hstable : (prefixWord ++ tailWord_326487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326487).length < 2 ^ (prefixWord ++ tailWord_326487).sum := by decide
  have hdescent : baseEnd_326487 < baseStart_326487 := by decide
  rcases family_descends (prefixWord ++ tailWord_326487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326515 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 2, 6]
def baseStart_326515 : Nat := 118140960795 + 326515 * 2 ^ 59
def prefixEnd_326515 : Nat := 4983230072969 + 3 ^ 40 * 326515 * 2
def baseEnd_326515 : Nat := 111772757268596828173927

theorem tailTrace_326515 : CollatzResearch.WordTrace tailWord_326515 prefixEnd_326515 111772757268596828173927 := by
  unfold tailWord_326515
  simp only [CollatzResearch.WordTrace]
  refine ⟨11908980412099394167484999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7939320274732929444989999 11908980412099394167484999)
  ·
    refine ⟨17863470618149091251227499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11908980412099394167484999 17863470618149091251227499)
    ·
      refine ⟨26795205927223636876841249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17863470618149091251227499 26795205927223636876841249)
      ·
        refine ⟨20096404445417727657630937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26795205927223636876841249 20096404445417727657630937)
        ·
          refine ⟨15072303334063295743223203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20096404445417727657630937 15072303334063295743223203)
          ·
            refine ⟨22608455001094943614834805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15072303334063295743223203 22608455001094943614834805)
            ·
              refine ⟨2119542656352650963890763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22608455001094943614834805 2119542656352650963890763)
              ·
                refine ⟨3179313984528976445836145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119542656352650963890763 3179313984528976445836145)
                ·
                  refine ⟨2384485488396732334377109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3179313984528976445836145 2384485488396732334377109)
                  ·
                    refine ⟨111772757268596828173927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2384485488396732334377109 111772757268596828173927)
                    ·
                      rfl

theorem cell22_326515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_326515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326515 prefixEnd_326515 := by exact prefixLift 326515
  have htrace : WordTrace (prefixWord ++ tailWord_326515) baseStart_326515 baseEnd_326515 := by
    simpa [prefixWord, tailWord_326515, baseEnd_326515] using wordTrace_append hprefix tailTrace_326515
  have hstable : (prefixWord ++ tailWord_326515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326515).length < 2 ^ (prefixWord ++ tailWord_326515).sum := by decide
  have hdescent : baseEnd_326515 < baseStart_326515 := by decide
  rcases family_descends (prefixWord ++ tailWord_326515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326545 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_326545 : Nat := 118140960795 + 326545 * 2 ^ 59
def prefixEnd_326545 : Nat := 4983230072969 + 3 ^ 40 * 326545 * 2
def baseEnd_326545 : Nat := 111783026881686749923835

theorem tailTrace_326545 : CollatzResearch.WordTrace tailWord_326545 prefixEnd_326545 111783026881686749923835 := by
  unfold tailWord_326545
  simp only [CollatzResearch.WordTrace]
  refine ⟨11910074601990709291077089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7940049734660472860718059 11910074601990709291077089)
  ·
    refine ⟨8932555951493031968307817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11910074601990709291077089 8932555951493031968307817)
    ·
      refine ⟨6699416963619773976230863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8932555951493031968307817 6699416963619773976230863)
      ·
        refine ⟨10049125445429660964346295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6699416963619773976230863 10049125445429660964346295)
        ·
          refine ⟨15073688168144491446519443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10049125445429660964346295 15073688168144491446519443)
          ·
            refine ⟨22610532252216737169779165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15073688168144491446519443 22610532252216737169779165)
            ·
              refine ⟨8478949594581276438667187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22610532252216737169779165 8478949594581276438667187)
              ·
                refine ⟨12718424391871914658000781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8478949594581276438667187 12718424391871914658000781)
                ·
                  refine ⟨4769409146951967996750293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12718424391871914658000781 4769409146951967996750293)
                  ·
                    refine ⟨111783026881686749923835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4769409146951967996750293 111783026881686749923835)
                    ·
                      rfl

theorem cell22_326545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_326545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326545 prefixEnd_326545 := by exact prefixLift 326545
  have htrace : WordTrace (prefixWord ++ tailWord_326545) baseStart_326545 baseEnd_326545 := by
    simpa [prefixWord, tailWord_326545, baseEnd_326545] using wordTrace_append hprefix tailTrace_326545
  have hstable : (prefixWord ++ tailWord_326545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326545).length < 2 ^ (prefixWord ++ tailWord_326545).sum := by decide
  have hdescent : baseEnd_326545 < baseStart_326545 := by decide
  rcases family_descends (prefixWord ++ tailWord_326545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326551 : List Nat := [1, 1, 3, 3, 1, 2, 4, 3, 1, 3]
def baseStart_326551 : Nat := 118140960795 + 326551 * 2 ^ 59
def prefixEnd_326551 : Nat := 4983230072969 + 3 ^ 40 * 326551 * 2
def baseEnd_326551 : Nat := 111785080804304734273817

theorem tailTrace_326551 : CollatzResearch.WordTrace tailWord_326551 prefixEnd_326551 111785080804304734273817 := by
  unfold tailWord_326551
  simp only [CollatzResearch.WordTrace]
  refine ⟨11910293439968972315795507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7940195626645981543863671 11910293439968972315795507)
  ·
    refine ⟨17865440159953458473693261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11910293439968972315795507 17865440159953458473693261)
    ·
      refine ⟨6699540059982546927634973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17865440159953458473693261 6699540059982546927634973)
      ·
        refine ⟨2512327522493455097863115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6699540059982546927634973 2512327522493455097863115)
        ·
          refine ⟨3768491283740182646794673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512327522493455097863115 3768491283740182646794673)
          ·
            refine ⟨2826368462805136985096005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3768491283740182646794673 2826368462805136985096005)
            ·
              refine ⟨529944086775963184705501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2826368462805136985096005 529944086775963184705501)
              ·
                refine ⟨198729032540986194264563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 529944086775963184705501 198729032540986194264563)
                ·
                  refine ⟨298093548811479291396845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198729032540986194264563 298093548811479291396845)
                  ·
                    refine ⟨111785080804304734273817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 298093548811479291396845 111785080804304734273817)
                    ·
                      rfl

theorem cell22_326551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_326551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326551 prefixEnd_326551 := by exact prefixLift 326551
  have htrace : WordTrace (prefixWord ++ tailWord_326551) baseStart_326551 baseEnd_326551 := by
    simpa [prefixWord, tailWord_326551, baseEnd_326551] using wordTrace_append hprefix tailTrace_326551
  have hstable : (prefixWord ++ tailWord_326551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326551).length < 2 ^ (prefixWord ++ tailWord_326551).sum := by decide
  have hdescent : baseEnd_326551 < baseStart_326551 := by decide
  rcases family_descends (prefixWord ++ tailWord_326551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326592 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 6]
def baseStart_326592 : Nat := 118140960795 + 326592 * 2 ^ 59
def prefixEnd_326592 : Nat := 4983230072969 + 3 ^ 40 * 326592 * 2
def baseEnd_326592 : Nat := 37266371980731431332897

theorem tailTrace_326592 : CollatzResearch.WordTrace tailWord_326592 prefixEnd_326592 37266371980731431332897 := by
  unfold tailWord_326592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5955894416410218159019015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7941192555213624212025353 5955894416410218159019015)
  ·
    refine ⟨8933841624615327238528523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5955894416410218159019015 8933841624615327238528523)
    ·
      refine ⟨13400762436922990857792785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8933841624615327238528523 13400762436922990857792785)
      ·
        refine ⟨10050571827692243143344589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13400762436922990857792785 10050571827692243143344589)
        ·
          refine ⟨3768964435384591178754221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10050571827692243143344589 3768964435384591178754221)
          ·
            refine ⟨1413361663269221692032833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3768964435384591178754221 1413361663269221692032833)
            ·
              refine ⟨1060021247451916269024625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1413361663269221692032833 1060021247451916269024625)
              ·
                refine ⟨795015935588937201768469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060021247451916269024625 795015935588937201768469)
                ·
                  refine ⟨37266371980731431332897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 795015935588937201768469 37266371980731431332897)
                  ·
                    rfl

theorem cell22_326592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_326592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326592 prefixEnd_326592 := by exact prefixLift 326592
  have htrace : WordTrace (prefixWord ++ tailWord_326592) baseStart_326592 baseEnd_326592 := by
    simpa [prefixWord, tailWord_326592, baseEnd_326592] using wordTrace_append hprefix tailTrace_326592
  have hstable : (prefixWord ++ tailWord_326592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326592).length < 2 ^ (prefixWord ++ tailWord_326592).sum := by decide
  have hdescent : baseEnd_326592 < baseStart_326592 := by decide
  rcases family_descends (prefixWord ++ tailWord_326592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326626 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_326626 : Nat := 118140960795 + 326626 * 2 ^ 59
def prefixEnd_326626 : Nat := 4983230072969 + 3 ^ 40 * 326626 * 2
def baseEnd_326626 : Nat := 37270251612343179549529

theorem tailTrace_326626 : CollatzResearch.WordTrace tailWord_326626 prefixEnd_326626 37270251612343179549529 := by
  unfold tailWord_326626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2978257228674315031193933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7942019276464840083183821 2978257228674315031193933)
  ·
    refine ⟨1116846460752868136697725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2978257228674315031193933 1116846460752868136697725)
    ·
      refine ⟨418817422782325551261647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1116846460752868136697725 418817422782325551261647)
      ·
        refine ⟨628226134173488326892471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418817422782325551261647 628226134173488326892471)
        ·
          refine ⟨942339201260232490338707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628226134173488326892471 942339201260232490338707)
          ·
            refine ⟨1413508801890348735508061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942339201260232490338707 1413508801890348735508061)
            ·
              refine ⟨530065800708880775815523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1413508801890348735508061 530065800708880775815523)
              ·
                refine ⟨795098701063321163723285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530065800708880775815523 795098701063321163723285)
                ·
                  refine ⟨37270251612343179549529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 795098701063321163723285 37270251612343179549529)
                  ·
                    rfl

theorem cell22_326626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_326626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326626 prefixEnd_326626 := by exact prefixLift 326626
  have htrace : WordTrace (prefixWord ++ tailWord_326626) baseStart_326626 baseEnd_326626 := by
    simpa [prefixWord, tailWord_326626, baseEnd_326626] using wordTrace_append hprefix tailTrace_326626
  have hstable : (prefixWord ++ tailWord_326626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326626).length < 2 ^ (prefixWord ++ tailWord_326626).sum := by decide
  have hdescent : baseEnd_326626 < baseStart_326626 := by decide
  rcases family_descends (prefixWord ++ tailWord_326626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326641 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 2, 3]
def baseStart_326641 : Nat := 118140960795 + 326641 * 2 ^ 59
def prefixEnd_326641 : Nat := 4983230072969 + 3 ^ 40 * 326641 * 2
def baseEnd_326641 : Nat := 111815889643574499523541

theorem tailTrace_326641 : CollatzResearch.WordTrace tailWord_326641 prefixEnd_326641 111815889643574499523541 := by
  unfold tailWord_326641
  simp only [CollatzResearch.WordTrace]
  refine ⟨11913576009642917686571777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7942384006428611791047851 11913576009642917686571777)
  ·
    refine ⟨8935182007232188264928833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11913576009642917686571777 8935182007232188264928833)
    ·
      refine ⟨6701386505424141198696625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8935182007232188264928833 6701386505424141198696625)
      ·
        refine ⟨5026039879068105899022469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6701386505424141198696625 5026039879068105899022469)
        ·
          refine ⟨942382477325269856066713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5026039879068105899022469 942382477325269856066713)
          ·
            refine ⟨706786857993952392050035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 942382477325269856066713 706786857993952392050035)
            ·
              refine ⟨1060180286990928588075053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706786857993952392050035 1060180286990928588075053)
              ·
                refine ⟨397567607621598220528145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1060180286990928588075053 397567607621598220528145)
                ·
                  refine ⟨298175705716198665396109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397567607621598220528145 298175705716198665396109)
                  ·
                    refine ⟨111815889643574499523541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 298175705716198665396109 111815889643574499523541)
                    ·
                      rfl

theorem cell22_326641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_326641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326641 prefixEnd_326641 := by exact prefixLift 326641
  have htrace : WordTrace (prefixWord ++ tailWord_326641) baseStart_326641 baseEnd_326641 := by
    simpa [prefixWord, tailWord_326641, baseEnd_326641] using wordTrace_append hprefix tailTrace_326641
  have hstable : (prefixWord ++ tailWord_326641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326641).length < 2 ^ (prefixWord ++ tailWord_326641).sum := by decide
  have hdescent : baseEnd_326641 < baseStart_326641 := by decide
  rcases family_descends (prefixWord ++ tailWord_326641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326645 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 1, 4]
def baseStart_326645 : Nat := 118140960795 + 326645 * 2 ^ 59
def prefixEnd_326645 : Nat := 4983230072969 + 3 ^ 40 * 326645 * 2
def baseEnd_326645 : Nat := 111817258925319822423529

theorem tailTrace_326645 : CollatzResearch.WordTrace tailWord_326645 prefixEnd_326645 111817258925319822423529 := by
  unfold tailWord_326645
  simp only [CollatzResearch.WordTrace]
  refine ⟨11913721901628426369717389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7942481267752284246478259 11913721901628426369717389)
  ·
    refine ⟨4467645713110659888644021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11913721901628426369717389 4467645713110659888644021)
    ·
      refine ⟨418841785604124364560377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4467645713110659888644021 418841785604124364560377)
      ·
        refine ⟨314131339203093273420283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418841785604124364560377 314131339203093273420283)
        ·
          refine ⟨471197008804639910130425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314131339203093273420283 471197008804639910130425)
          ·
            refine ⟨353397756603479932597819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471197008804639910130425 353397756603479932597819)
            ·
              refine ⟨530096634905219898896729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353397756603479932597819 530096634905219898896729)
              ·
                refine ⟨397572476178914924172547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 530096634905219898896729 397572476178914924172547)
                ·
                  refine ⟨596358714268372386258821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397572476178914924172547 596358714268372386258821)
                  ·
                    refine ⟨111817258925319822423529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 596358714268372386258821 111817258925319822423529)
                    ·
                      rfl

theorem cell22_326645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_326645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326645 prefixEnd_326645 := by exact prefixLift 326645
  have htrace : WordTrace (prefixWord ++ tailWord_326645) baseStart_326645 baseEnd_326645 := by
    simpa [prefixWord, tailWord_326645, baseEnd_326645] using wordTrace_append hprefix tailTrace_326645
  have hstable : (prefixWord ++ tailWord_326645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326645).length < 2 ^ (prefixWord ++ tailWord_326645).sum := by decide
  have hdescent : baseEnd_326645 < baseStart_326645 := by decide
  rcases family_descends (prefixWord ++ tailWord_326645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326658 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_326658 : Nat := 118140960795 + 326658 * 2 ^ 59
def prefixEnd_326658 : Nat := 4983230072969 + 3 ^ 40 * 326658 * 2
def baseEnd_326658 : Nat := 111821709090992121848489

theorem tailTrace_326658 : CollatzResearch.WordTrace tailWord_326658 prefixEnd_326658 111821709090992121848489 := by
  unfold tailWord_326658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2978549012645332397485157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7942797367054219726627085 2978549012645332397485157)
  ·
    refine ⟨558477939870999824528467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2978549012645332397485157 558477939870999824528467)
    ·
      refine ⟨837716909806499736792701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 558477939870999824528467 837716909806499736792701)
      ·
        refine ⟨314143841177437401297263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 837716909806499736792701 314143841177437401297263)
        ·
          refine ⟨471215761766156101945895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314143841177437401297263 471215761766156101945895)
          ·
            refine ⟨706823642649234152918843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471215761766156101945895 706823642649234152918843)
            ·
              refine ⟨1060235463973851229378265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706823642649234152918843 1060235463973851229378265)
              ·
                refine ⟨795176597980388422033699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060235463973851229378265 795176597980388422033699)
                ·
                  refine ⟨1192764896970582633050549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 795176597980388422033699 1192764896970582633050549)
                  ·
                    refine ⟨111821709090992121848489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1192764896970582633050549 111821709090992121848489)
                    ·
                      rfl

theorem cell22_326658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_326658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326658 prefixEnd_326658 := by exact prefixLift 326658
  have htrace : WordTrace (prefixWord ++ tailWord_326658) baseStart_326658 baseEnd_326658 := by
    simpa [prefixWord, tailWord_326658, baseEnd_326658] using wordTrace_append hprefix tailTrace_326658
  have hstable : (prefixWord ++ tailWord_326658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326658).length < 2 ^ (prefixWord ++ tailWord_326658).sum := by decide
  have hdescent : baseEnd_326658 < baseStart_326658 := by decide
  rcases family_descends (prefixWord ++ tailWord_326658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326688 : List Nat := [2, 1, 1, 7, 2, 1, 1, 7]
def baseStart_326688 : Nat := 118140960795 + 326688 * 2 ^ 59
def prefixEnd_326688 : Nat := 4983230072969 + 3 ^ 40 * 326688 * 2
def baseEnd_326688 : Nat := 12425775411564671510933

theorem tailTrace_326688 : CollatzResearch.WordTrace tailWord_326688 prefixEnd_326688 12425775411564671510933 := by
  unfold tailWord_326688
  simp only [CollatzResearch.WordTrace]
  refine ⟨5957645120236322356766359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7943526826981763142355145 5957645120236322356766359)
  ·
    refine ⟨8936467680354483535149539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5957645120236322356766359 8936467680354483535149539)
    ·
      refine ⟨13404701520531725302724309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8936467680354483535149539 13404701520531725302724309)
      ·
        refine ⟨314172691887462311782601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13404701520531725302724309 314172691887462311782601)
        ·
          refine ⟨235629518915596733836951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314172691887462311782601 235629518915596733836951)
          ·
            refine ⟨353444278373395100755427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235629518915596733836951 353444278373395100755427)
            ·
              refine ⟨530166417560092651133141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353444278373395100755427 530166417560092651133141)
              ·
                refine ⟨12425775411564671510933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 530166417560092651133141 12425775411564671510933)
                ·
                  rfl

theorem cell22_326688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 7].length) (baseStart_326688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326688 prefixEnd_326688 := by exact prefixLift 326688
  have htrace : WordTrace (prefixWord ++ tailWord_326688) baseStart_326688 baseEnd_326688 := by
    simpa [prefixWord, tailWord_326688, baseEnd_326688] using wordTrace_append hprefix tailTrace_326688
  have hstable : (prefixWord ++ tailWord_326688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326688).length < 2 ^ (prefixWord ++ tailWord_326688).sum := by decide
  have hdescent : baseEnd_326688 < baseStart_326688 := by decide
  rcases family_descends (prefixWord ++ tailWord_326688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326733 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 5]
def baseStart_326733 : Nat := 118140960795 + 326733 * 2 ^ 59
def prefixEnd_326733 : Nat := 4983230072969 + 3 ^ 40 * 326733 * 2
def baseEnd_326733 : Nat := 37282461041238975407753

theorem tailTrace_326733 : CollatzResearch.WordTrace tailWord_326733 prefixEnd_326733 37282461041238975407753 := by
  unfold tailWord_326733
  simp only [CollatzResearch.WordTrace]
  refine ⟨11916931525309617398920853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7944621016873078265947235 11916931525309617398920853)
  ·
    refine ⟨558606165248888315574415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11916931525309617398920853 558606165248888315574415)
    ·
      refine ⟨837909247873332473361623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 558606165248888315574415 837909247873332473361623)
      ·
        refine ⟨1256863871809998710042435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837909247873332473361623 1256863871809998710042435)
        ·
          refine ⟨1885295807714998065063653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256863871809998710042435 1885295807714998065063653)
          ·
            refine ⟨353492963946562137199435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1885295807714998065063653 353492963946562137199435)
            ·
              refine ⟨530239445919843205799153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353492963946562137199435 530239445919843205799153)
              ·
                refine ⟨397679584439882404349365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 530239445919843205799153 397679584439882404349365)
                ·
                  refine ⟨37282461041238975407753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 397679584439882404349365 37282461041238975407753)
                  ·
                    rfl

theorem cell22_326733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_326733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326733 prefixEnd_326733 := by exact prefixLift 326733
  have htrace : WordTrace (prefixWord ++ tailWord_326733) baseStart_326733 baseEnd_326733 := by
    simpa [prefixWord, tailWord_326733, baseEnd_326733] using wordTrace_append hprefix tailTrace_326733
  have hstable : (prefixWord ++ tailWord_326733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326733).length < 2 ^ (prefixWord ++ tailWord_326733).sum := by decide
  have hdescent : baseEnd_326733 < baseStart_326733 := by decide
  rcases family_descends (prefixWord ++ tailWord_326733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326744 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 6]
def baseStart_326744 : Nat := 118140960795 + 326744 * 2 ^ 59
def prefixEnd_326744 : Nat := 4983230072969 + 3 ^ 40 * 326744 * 2
def baseEnd_326744 : Nat := 37283716216172188066075

theorem tailTrace_326744 : CollatzResearch.WordTrace tailWord_326744 prefixEnd_326744 37283716216172188066075 := by
  unfold tailWord_326744
  simp only [CollatzResearch.WordTrace]
  refine ⟨5958666364134883138785643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7944888485513177518380857 5958666364134883138785643)
  ·
    refine ⟨8937999546202324708178465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5958666364134883138785643 8937999546202324708178465)
    ·
      refine ⟨6703499659651743531133849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8937999546202324708178465 6703499659651743531133849)
      ·
        refine ⟨5027624744738807648350387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6703499659651743531133849 5027624744738807648350387)
        ·
          refine ⟨7541437117108211472525581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5027624744738807648350387 7541437117108211472525581)
          ·
            refine ⟨2828038918915579302197093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7541437117108211472525581 2828038918915579302197093)
            ·
              refine ⟨530257297296671119161955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2828038918915579302197093 530257297296671119161955)
              ·
                refine ⟨795385945945006678742933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530257297296671119161955 795385945945006678742933)
                ·
                  refine ⟨37283716216172188066075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 795385945945006678742933 37283716216172188066075)
                  ·
                    rfl

theorem cell22_326744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_326744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326744 prefixEnd_326744 := by exact prefixLift 326744
  have htrace : WordTrace (prefixWord ++ tailWord_326744) baseStart_326744 baseEnd_326744 := by
    simpa [prefixWord, tailWord_326744, baseEnd_326744] using wordTrace_append hprefix tailTrace_326744
  have hstable : (prefixWord ++ tailWord_326744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326744).length < 2 ^ (prefixWord ++ tailWord_326744).sum := by decide
  have hdescent : baseEnd_326744 < baseStart_326744 := by decide
  rcases family_descends (prefixWord ++ tailWord_326744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326810 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 2, 3]
def baseStart_326810 : Nat := 118140960795 + 326810 * 2 ^ 59
def prefixEnd_326810 : Nat := 4983230072969 + 3 ^ 40 * 326810 * 2
def baseEnd_326810 : Nat := 111873741797314392048023

theorem tailTrace_326810 : CollatzResearch.WordTrace tailWord_326810 prefixEnd_326810 111873741797314392048023 := by
  unfold tailWord_326810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2979934986507664887368471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7946493297353773032982589 2979934986507664887368471)
  ·
    refine ⟨4469902479761497331052707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2979934986507664887368471 4469902479761497331052707)
    ·
      refine ⟨6704853719642245996579061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4469902479761497331052707 6704853719642245996579061)
      ·
        refine ⟨628580036216460562179287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6704853719642245996579061 628580036216460562179287)
        ·
          refine ⟨942870054324690843268931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628580036216460562179287 942870054324690843268931)
          ·
            refine ⟨1414305081487036264903397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942870054324690843268931 1414305081487036264903397)
            ·
              refine ⟨265182202778819299669387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1414305081487036264903397 265182202778819299669387)
              ·
                refine ⟨397773304168228949504081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265182202778819299669387 397773304168228949504081)
                ·
                  refine ⟨298329978126171712128061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397773304168228949504081 298329978126171712128061)
                  ·
                    refine ⟨111873741797314392048023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 298329978126171712128061 111873741797314392048023)
                    ·
                      rfl

theorem cell22_326810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_326810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326810 prefixEnd_326810 := by exact prefixLift 326810
  have htrace : WordTrace (prefixWord ++ tailWord_326810) baseStart_326810 baseEnd_326810 := by
    simpa [prefixWord, tailWord_326810, baseEnd_326810] using wordTrace_append hprefix tailTrace_326810
  have hstable : (prefixWord ++ tailWord_326810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326810).length < 2 ^ (prefixWord ++ tailWord_326810).sum := by decide
  have hdescent : baseEnd_326810 < baseStart_326810 := by decide
  rcases family_descends (prefixWord ++ tailWord_326810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326866 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_326866 : Nat := 118140960795 + 326866 * 2 ^ 59
def prefixEnd_326866 : Nat := 4983230072969 + 3 ^ 40 * 326866 * 2
def baseEnd_326866 : Nat := 111892911741748912647851

theorem tailTrace_326866 : CollatzResearch.WordTrace tailWord_326866 prefixEnd_326866 111892911741748912647851 := by
  unfold tailWord_326866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2980445608456945278378113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7947854955885187409008301 2980445608456945278378113)
  ·
    refine ⟨2235334206342708958783585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2980445608456945278378113 2235334206342708958783585)
    ·
      refine ⟨1676500654757031719087689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2235334206342708958783585 1676500654757031719087689)
      ·
        refine ⟨1257375491067773789315767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1676500654757031719087689 1257375491067773789315767)
        ·
          refine ⟨1886063236601660683973651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257375491067773789315767 1886063236601660683973651)
          ·
            refine ⟨2829094854902491025960477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886063236601660683973651 2829094854902491025960477)
            ·
              refine ⟨1060910570588434134735179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2829094854902491025960477 1060910570588434134735179)
              ·
                refine ⟨1591365855882651202102769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060910570588434134735179 1591365855882651202102769)
                ·
                  refine ⟨1193524391911988401577077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1591365855882651202102769 1193524391911988401577077)
                  ·
                    refine ⟨111892911741748912647851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1193524391911988401577077 111892911741748912647851)
                    ·
                      rfl

theorem cell22_326866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_326866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326866 prefixEnd_326866 := by exact prefixLift 326866
  have htrace : WordTrace (prefixWord ++ tailWord_326866) baseStart_326866 baseEnd_326866 := by
    simpa [prefixWord, tailWord_326866, baseEnd_326866] using wordTrace_append hprefix tailTrace_326866
  have hstable : (prefixWord ++ tailWord_326866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326866).length < 2 ^ (prefixWord ++ tailWord_326866).sum := by decide
  have hdescent : baseEnd_326866 < baseStart_326866 := by decide
  rcases family_descends (prefixWord ++ tailWord_326866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326879 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 8]
def baseStart_326879 : Nat := 118140960795 + 326879 * 2 ^ 59
def prefixEnd_326879 : Nat := 4983230072969 + 3 ^ 40 * 326879 * 2
def baseEnd_326879 : Nat := 37299120635807070690937

theorem tailTrace_326879 : CollatzResearch.WordTrace tailWord_326879 prefixEnd_326879 37299120635807070690937 := by
  unfold tailWord_326879
  simp only [CollatzResearch.WordTrace]
  refine ⟨11922256582780684333735691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7948171055187122889157127 11922256582780684333735691)
  ·
    refine ⟨17883384874171026500603537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11922256582780684333735691 17883384874171026500603537)
    ·
      refine ⟨13412538655628269875452653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17883384874171026500603537 13412538655628269875452653)
      ·
        refine ⟨5029701995860601203294745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13412538655628269875452653 5029701995860601203294745)
        ·
          refine ⟨3772276496895450902471059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5029701995860601203294745 3772276496895450902471059)
          ·
            refine ⟨5658414745343176353706589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772276496895450902471059 5658414745343176353706589)
            ·
              refine ⟨2121905529503691132639971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5658414745343176353706589 2121905529503691132639971)
              ·
                refine ⟨3182858294255536698959957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2121905529503691132639971 3182858294255536698959957)
                ·
                  refine ⟨37299120635807070690937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3182858294255536698959957 37299120635807070690937)
                  ·
                    rfl

theorem cell22_326879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 8].length) (baseStart_326879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326879 prefixEnd_326879 := by exact prefixLift 326879
  have htrace : WordTrace (prefixWord ++ tailWord_326879) baseStart_326879 baseEnd_326879 := by
    simpa [prefixWord, tailWord_326879, baseEnd_326879] using wordTrace_append hprefix tailTrace_326879
  have hstable : (prefixWord ++ tailWord_326879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326879).length < 2 ^ (prefixWord ++ tailWord_326879).sum := by decide
  have hdescent : baseEnd_326879 < baseStart_326879 := by decide
  rcases family_descends (prefixWord ++ tailWord_326879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326881 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 3, 4]
def baseStart_326881 : Nat := 118140960795 + 326881 * 2 ^ 59
def prefixEnd_326881 : Nat := 4983230072969 + 3 ^ 40 * 326881 * 2
def baseEnd_326881 : Nat := 111898046548293873522805

theorem tailTrace_326881 : CollatzResearch.WordTrace tailWord_326881 prefixEnd_326881 111898046548293873522805 := by
  unfold tailWord_326881
  simp only [CollatzResearch.WordTrace]
  refine ⟨11922329528773438675308497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7948219685848959116872331 11922329528773438675308497)
  ·
    refine ⟨8941747146580079006481373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11922329528773438675308497 8941747146580079006481373)
    ·
      refine ⟨3353155179967529627430515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8941747146580079006481373 3353155179967529627430515)
      ·
        refine ⟨5029732769951294441145773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3353155179967529627430515 5029732769951294441145773)
        ·
          refine ⟨1886149788731735415429665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5029732769951294441145773 1886149788731735415429665)
          ·
            refine ⟨1414612341548801561572249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1886149788731735415429665 1414612341548801561572249)
            ·
              refine ⟨1060959256161601171179187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414612341548801561572249 1060959256161601171179187)
              ·
                refine ⟨1591438884242401756768781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060959256161601171179187 1591438884242401756768781)
                ·
                  refine ⟨596789581590900658788293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1591438884242401756768781 596789581590900658788293)
                  ·
                    refine ⟨111898046548293873522805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 596789581590900658788293 111898046548293873522805)
                    ·
                      rfl

theorem cell22_326881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_326881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326881 prefixEnd_326881 := by exact prefixLift 326881
  have htrace : WordTrace (prefixWord ++ tailWord_326881) baseStart_326881 baseEnd_326881 := by
    simpa [prefixWord, tailWord_326881, baseEnd_326881] using wordTrace_append hprefix tailTrace_326881
  have hstable : (prefixWord ++ tailWord_326881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326881).length < 2 ^ (prefixWord ++ tailWord_326881).sum := by decide
  have hdescent : baseEnd_326881 < baseStart_326881 := by decide
  rcases family_descends (prefixWord ++ tailWord_326881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326913 : List Nat := [1, 2, 4, 1, 1, 3, 2, 4, 4]
def baseStart_326913 : Nat := 118140960795 + 326913 * 2 ^ 59
def prefixEnd_326913 : Nat := 4983230072969 + 3 ^ 40 * 326913 * 2
def baseEnd_326913 : Nat := 37303000267418818907569

theorem tailTrace_326913 : CollatzResearch.WordTrace tailWord_326913 prefixEnd_326913 37303000267418818907569 := by
  unfold tailWord_326913
  simp only [CollatzResearch.WordTrace]
  refine ⟨11923496664657508140473393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7948997776438338760315595 11923496664657508140473393)
  ·
    refine ⟨8942622498493131105355045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11923496664657508140473393 8942622498493131105355045)
    ·
      refine ⟨1676741718467462082254071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8942622498493131105355045 1676741718467462082254071)
      ·
        refine ⟨2515112577701193123381107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676741718467462082254071 2515112577701193123381107)
        ·
          refine ⟨3772668866551789685071661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515112577701193123381107 3772668866551789685071661)
          ·
            refine ⟨1414750824956921131901873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3772668866551789685071661 1414750824956921131901873)
            ·
              refine ⟨1061063118717690848926405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414750824956921131901873 1061063118717690848926405)
              ·
                refine ⟨198949334759567034173701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1061063118717690848926405 198949334759567034173701)
                ·
                  refine ⟨37303000267418818907569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198949334759567034173701 37303000267418818907569)
                  ·
                    rfl

theorem cell22_326913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 4].length) (baseStart_326913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326913 prefixEnd_326913 := by exact prefixLift 326913
  have htrace : WordTrace (prefixWord ++ tailWord_326913) baseStart_326913 baseEnd_326913 := by
    simpa [prefixWord, tailWord_326913, baseEnd_326913] using wordTrace_append hprefix tailTrace_326913
  have hstable : (prefixWord ++ tailWord_326913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326913).length < 2 ^ (prefixWord ++ tailWord_326913).sum := by decide
  have hdescent : baseEnd_326913 < baseStart_326913 := by decide
  rcases family_descends (prefixWord ++ tailWord_326913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326926 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_326926 : Nat := 118140960795 + 326926 * 2 ^ 59
def prefixEnd_326926 : Nat := 4983230072969 + 3 ^ 40 * 326926 * 2
def baseEnd_326926 : Nat := 111913450967928756147667

theorem tailTrace_326926 : CollatzResearch.WordTrace tailWord_326926 prefixEnd_326926 111913450967928756147667 := by
  unfold tailWord_326926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490496351701301420087079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7949313875740274240464421 1490496351701301420087079)
  ·
    refine ⟨2235744527551952130130619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1490496351701301420087079 2235744527551952130130619)
    ·
      refine ⟨3353616791327928195195929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2235744527551952130130619 3353616791327928195195929)
      ·
        refine ⟨2515212593495946146396947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3353616791327928195195929 2515212593495946146396947)
        ·
          refine ⟨3772818890243919219595421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515212593495946146396947 3772818890243919219595421)
          ·
            refine ⟨1414807083841469707348283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3772818890243919219595421 1414807083841469707348283)
            ·
              refine ⟨2122210625762204561022425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414807083841469707348283 2122210625762204561022425)
              ·
                refine ⟨1591657969321653420766819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2122210625762204561022425 1591657969321653420766819)
                ·
                  refine ⟨2387486953982480131150229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591657969321653420766819 2387486953982480131150229)
                  ·
                    refine ⟨111913450967928756147667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2387486953982480131150229 111913450967928756147667)
                    ·
                      rfl

theorem cell22_326926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_326926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326926 prefixEnd_326926 := by exact prefixLift 326926
  have htrace : WordTrace (prefixWord ++ tailWord_326926) baseStart_326926 baseEnd_326926 := by
    simpa [prefixWord, tailWord_326926, baseEnd_326926] using wordTrace_append hprefix tailTrace_326926
  have hstable : (prefixWord ++ tailWord_326926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326926).length < 2 ^ (prefixWord ++ tailWord_326926).sum := by decide
  have hdescent : baseEnd_326926 < baseStart_326926 := by decide
  rcases family_descends (prefixWord ++ tailWord_326926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326939 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 1, 9]
def baseStart_326939 : Nat := 118140960795 + 326939 * 2 ^ 59
def prefixEnd_326939 : Nat := 4983230072969 + 3 ^ 40 * 326939 * 2
def baseEnd_326939 : Nat := 111917901133601055572627

theorem tailTrace_326939 : CollatzResearch.WordTrace tailWord_326939 prefixEnd_326939 111917901133601055572627 := by
  unfold tailWord_326939
  simp only [CollatzResearch.WordTrace]
  refine ⟨11924444962563314580919871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7949629975042209720613247 11924444962563314580919871)
  ·
    refine ⟨17886667443844971871379807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11924444962563314580919871 17886667443844971871379807)
    ·
      refine ⟨26830001165767457807069711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17886667443844971871379807 26830001165767457807069711)
      ·
        refine ⟨40245001748651186710604567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26830001165767457807069711 40245001748651186710604567)
        ·
          refine ⟨60367502622976780065906851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40245001748651186710604567 60367502622976780065906851)
          ·
            refine ⟨90551253934465170098860277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60367502622976780065906851 90551253934465170098860277)
            ·
              refine ⟨8489180056356109696768151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90551253934465170098860277 8489180056356109696768151)
              ·
                refine ⟨12733770084534164545152227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8489180056356109696768151 12733770084534164545152227)
                ·
                  refine ⟨19100655126801246817728341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12733770084534164545152227 19100655126801246817728341)
                  ·
                    refine ⟨111917901133601055572627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 19100655126801246817728341 111917901133601055572627)
                    ·
                      rfl

theorem cell22_326939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_326939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_326939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_326939 prefixEnd_326939 := by exact prefixLift 326939
  have htrace : WordTrace (prefixWord ++ tailWord_326939) baseStart_326939 baseEnd_326939 := by
    simpa [prefixWord, tailWord_326939, baseEnd_326939] using wordTrace_append hprefix tailTrace_326939
  have hstable : (prefixWord ++ tailWord_326939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326939).length < 2 ^ (prefixWord ++ tailWord_326939).sum := by decide
  have hdescent : baseEnd_326939 < baseStart_326939 := by decide
  rcases family_descends (prefixWord ++ tailWord_326939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327031 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 6]
def baseStart_327031 : Nat := 118140960795 + 327031 * 2 ^ 59
def prefixEnd_327031 : Nat := 4983230072969 + 3 ^ 40 * 327031 * 2
def baseEnd_327031 : Nat := 37316464871247827424115

theorem tailTrace_327031 : CollatzResearch.WordTrace tailWord_327031 prefixEnd_327031 37316464871247827424115 := by
  unfold tailWord_327031
  simp only [CollatzResearch.WordTrace]
  refine ⟨11927800478230014293268947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7951866985486676195512631 11927800478230014293268947)
  ·
    refine ⟨17891700717345021439903421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11927800478230014293268947 17891700717345021439903421)
    ·
      refine ⟨6709387769004383039963783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17891700717345021439903421 6709387769004383039963783)
      ·
        refine ⟨10064081653506574559945675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6709387769004383039963783 10064081653506574559945675)
        ·
          refine ⟨15096122480259861839918513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10064081653506574559945675 15096122480259861839918513)
          ·
            refine ⟨11322091860194896379938885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15096122480259861839918513 11322091860194896379938885)
            ·
              refine ⟨2122892223786543071238541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11322091860194896379938885 2122892223786543071238541)
              ·
                refine ⟨796084583919953651714453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2122892223786543071238541 796084583919953651714453)
                ·
                  refine ⟨37316464871247827424115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 796084583919953651714453 37316464871247827424115)
                  ·
                    rfl

theorem cell22_327031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 6].length) (baseStart_327031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327031 prefixEnd_327031 := by exact prefixLift 327031
  have htrace : WordTrace (prefixWord ++ tailWord_327031) baseStart_327031 baseEnd_327031 := by
    simpa [prefixWord, tailWord_327031, baseEnd_327031] using wordTrace_append hprefix tailTrace_327031
  have hstable : (prefixWord ++ tailWord_327031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327031).length < 2 ^ (prefixWord ++ tailWord_327031).sum := by decide
  have hdescent : baseEnd_327031 < baseStart_327031 := by decide
  rcases family_descends (prefixWord ++ tailWord_327031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327048 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 6]
def baseStart_327048 : Nat := 118140960795 + 327048 * 2 ^ 59
def prefixEnd_327048 : Nat := 4983230072969 + 3 ^ 40 * 327048 * 2
def baseEnd_327048 : Nat := 37318404687053701532431

theorem tailTrace_327048 : CollatzResearch.WordTrace tailWord_327048 prefixEnd_327048 37318404687053701532431 := by
  unfold tailWord_327048
  simp only [CollatzResearch.WordTrace]
  refine ⟨5964210259584213098318899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7952280346112284131091865 5964210259584213098318899)
  ·
    refine ⟨8946315389376319647478349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5964210259584213098318899 8946315389376319647478349)
    ·
      refine ⟨3354868271016119867804381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8946315389376319647478349 3354868271016119867804381)
      ·
        refine ⟨1258075601631044950426643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3354868271016119867804381 1258075601631044950426643)
        ·
          refine ⟨1887113402446567425639965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258075601631044950426643 1887113402446567425639965)
          ·
            refine ⟨707667525917462784614987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1887113402446567425639965 707667525917462784614987)
            ·
              refine ⟨1061501288876194176922481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707667525917462784614987 1061501288876194176922481)
              ·
                refine ⟨796125966657145632691861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061501288876194176922481 796125966657145632691861)
                ·
                  refine ⟨37318404687053701532431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 796125966657145632691861 37318404687053701532431)
                  ·
                    rfl

theorem cell22_327048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_327048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327048 prefixEnd_327048 := by exact prefixLift 327048
  have htrace : WordTrace (prefixWord ++ tailWord_327048) baseStart_327048 baseEnd_327048 := by
    simpa [prefixWord, tailWord_327048, baseEnd_327048] using wordTrace_append hprefix tailTrace_327048
  have hstable : (prefixWord ++ tailWord_327048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327048).length < 2 ^ (prefixWord ++ tailWord_327048).sum := by decide
  have hdescent : baseEnd_327048 < baseStart_327048 := by decide
  rcases family_descends (prefixWord ++ tailWord_327048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327063 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 4, 3]
def baseStart_327063 : Nat := 118140960795 + 327063 * 2 ^ 59
def prefixEnd_327063 : Nat := 4983230072969 + 3 ^ 40 * 327063 * 2
def baseEnd_327063 : Nat := 111960348867706065472247

theorem tailTrace_327063 : CollatzResearch.WordTrace tailWord_327063 prefixEnd_327063 111960348867706065472247 := by
  unfold tailWord_327063
  simp only [CollatzResearch.WordTrace]
  refine ⟨11928967614114083758433843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7952645076076055838955895 11928967614114083758433843)
  ·
    refine ⟨17893451421171125637650765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11928967614114083758433843 17893451421171125637650765)
    ·
      refine ⟨6710044282939172114119037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17893451421171125637650765 6710044282939172114119037)
      ·
        refine ⟨2516266606102189542794639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6710044282939172114119037 2516266606102189542794639)
        ·
          refine ⟨3774399909153284314191959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2516266606102189542794639 3774399909153284314191959)
          ·
            refine ⟨5661599863729926471287939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3774399909153284314191959 5661599863729926471287939)
            ·
              refine ⟨8492399795594889706931909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5661599863729926471287939 8492399795594889706931909)
              ·
                refine ⟨1592324961674041820049733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8492399795594889706931909 1592324961674041820049733)
                ·
                  refine ⟨298560930313882841259325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1592324961674041820049733 298560930313882841259325)
                  ·
                    refine ⟨111960348867706065472247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 298560930313882841259325 111960348867706065472247)
                    ·
                      rfl

theorem cell22_327063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_327063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327063 prefixEnd_327063 := by exact prefixLift 327063
  have htrace : WordTrace (prefixWord ++ tailWord_327063) baseStart_327063 baseEnd_327063 := by
    simpa [prefixWord, tailWord_327063, baseEnd_327063] using wordTrace_append hprefix tailTrace_327063
  have hstable : (prefixWord ++ tailWord_327063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327063).length < 2 ^ (prefixWord ++ tailWord_327063).sum := by decide
  have hdescent : baseEnd_327063 < baseStart_327063 := by decide
  rcases family_descends (prefixWord ++ tailWord_327063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327065 : List Nat := [1, 2, 1, 2, 1, 6, 2, 3, 4]
def baseStart_327065 : Nat := 118140960795 + 327065 * 2 ^ 59
def prefixEnd_327065 : Nat := 4983230072969 + 3 ^ 40 * 327065 * 2
def baseEnd_327065 : Nat := 37320344502859575640747

theorem tailTrace_327065 : CollatzResearch.WordTrace tailWord_327065 prefixEnd_327065 37320344502859575640747 := by
  unfold tailWord_327065
  simp only [CollatzResearch.WordTrace]
  refine ⟨11929040560106838100006649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7952693706737892066671099 11929040560106838100006649)
  ·
    refine ⟨8946780420080128575004987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11929040560106838100006649 8946780420080128575004987)
    ·
      refine ⟨13420170630120192862507481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8946780420080128575004987 13420170630120192862507481)
      ·
        refine ⟨10065127972590144646880611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13420170630120192862507481 10065127972590144646880611)
        ·
          refine ⟨15097691958885216970320917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10065127972590144646880611 15097691958885216970320917)
          ·
            refine ⟨707704310572744545483793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15097691958885216970320917 707704310572744545483793)
            ·
              refine ⟨530778232929558409112845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 707704310572744545483793 530778232929558409112845)
              ·
                refine ⟨199041837348584403417317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 530778232929558409112845 199041837348584403417317)
                ·
                  refine ⟨37320344502859575640747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199041837348584403417317 37320344502859575640747)
                  ·
                    rfl

theorem cell22_327065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 4].length) (baseStart_327065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327065 prefixEnd_327065 := by exact prefixLift 327065
  have htrace : WordTrace (prefixWord ++ tailWord_327065) baseStart_327065 baseEnd_327065 := by
    simpa [prefixWord, tailWord_327065, baseEnd_327065] using wordTrace_append hprefix tailTrace_327065
  have hstable : (prefixWord ++ tailWord_327065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327065).length < 2 ^ (prefixWord ++ tailWord_327065).sum := by decide
  have hdescent : baseEnd_327065 < baseStart_327065 := by decide
  rcases family_descends (prefixWord ++ tailWord_327065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327097 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 1, 5]
def baseStart_327097 : Nat := 118140960795 + 327097 * 2 ^ 59
def prefixEnd_327097 : Nat := 4983230072969 + 3 ^ 40 * 327097 * 2
def baseEnd_327097 : Nat := 111971987762541310122143

theorem tailTrace_327097 : CollatzResearch.WordTrace tailWord_327097 prefixEnd_327097 111971987762541310122143 := by
  unfold tailWord_327097
  simp only [CollatzResearch.WordTrace]
  refine ⟨11930207695990907565171545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7953471797327271710114363 11930207695990907565171545)
  ·
    refine ⟨8947655771993180673878659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11930207695990907565171545 8947655771993180673878659)
    ·
      refine ⟨13421483657989771010817989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8947655771993180673878659 13421483657989771010817989)
      ·
        refine ⟨2516528185873082064528373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13421483657989771010817989 2516528185873082064528373)
        ·
          refine ⟨235924517425601443549535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2516528185873082064528373 235924517425601443549535)
          ·
            refine ⟨353886776138402165324303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235924517425601443549535 353886776138402165324303)
            ·
              refine ⟨530830164207603247986455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353886776138402165324303 530830164207603247986455)
              ·
                refine ⟨796245246311404871979683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530830164207603247986455 796245246311404871979683)
                ·
                  refine ⟨1194367869467107307969525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796245246311404871979683 1194367869467107307969525)
                  ·
                    refine ⟨111971987762541310122143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1194367869467107307969525 111971987762541310122143)
                    ·
                      rfl

theorem cell22_327097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 1, 5].length) (baseStart_327097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327097 prefixEnd_327097 := by exact prefixLift 327097
  have htrace : WordTrace (prefixWord ++ tailWord_327097) baseStart_327097 baseEnd_327097 := by
    simpa [prefixWord, tailWord_327097, baseEnd_327097] using wordTrace_append hprefix tailTrace_327097
  have hstable : (prefixWord ++ tailWord_327097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327097).length < 2 ^ (prefixWord ++ tailWord_327097).sum := by decide
  have hdescent : baseEnd_327097 < baseStart_327097 := by decide
  rcases family_descends (prefixWord ++ tailWord_327097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327258 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 1, 8]
def baseStart_327258 : Nat := 118140960795 + 327258 * 2 ^ 59
def prefixEnd_327258 : Nat := 4983230072969 + 3 ^ 40 * 327258 * 2
def baseEnd_327258 : Nat := 112027101352790556846649

theorem tailTrace_327258 : CollatzResearch.WordTrace tailWord_327258 prefixEnd_327258 112027101352790556846649 := by
  unfold tailWord_327258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2984019962101908015445607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7957386565605088041188285 2984019962101908015445607)
  ·
    refine ⟨4476029943152862023168411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2984019962101908015445607 4476029943152862023168411)
    ·
      refine ⟨6714044914729293034752617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4476029943152862023168411 6714044914729293034752617)
      ·
        refine ⟨5035533686046969776064463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6714044914729293034752617 5035533686046969776064463)
        ·
          refine ⟨7553300529070454664096695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035533686046969776064463 7553300529070454664096695)
          ·
            refine ⟨11329950793605681996145043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7553300529070454664096695 11329950793605681996145043)
            ·
              refine ⟨16994926190408522994217565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11329950793605681996145043 16994926190408522994217565)
              ·
                refine ⟨6373097321403196122831587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16994926190408522994217565 6373097321403196122831587)
                ·
                  refine ⟨9559645982104794184247381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6373097321403196122831587 9559645982104794184247381)
                  ·
                    refine ⟨112027101352790556846649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9559645982104794184247381 112027101352790556846649)
                    ·
                      rfl

theorem cell22_327258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_327258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327258 prefixEnd_327258 := by exact prefixLift 327258
  have htrace : WordTrace (prefixWord ++ tailWord_327258) baseStart_327258 baseEnd_327258 := by
    simpa [prefixWord, tailWord_327258, baseEnd_327258] using wordTrace_append hprefix tailTrace_327258
  have hstable : (prefixWord ++ tailWord_327258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327258).length < 2 ^ (prefixWord ++ tailWord_327258).sum := by decide
  have hdescent : baseEnd_327258 < baseStart_327258 := by decide
  rcases family_descends (prefixWord ++ tailWord_327258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327354 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 1, 4]
def baseStart_327354 : Nat := 118140960795 + 327354 * 2 ^ 59
def prefixEnd_327354 : Nat := 4983230072969 + 3 ^ 40 * 327354 * 2
def baseEnd_327354 : Nat := 112059964114678306446355

theorem tailTrace_327354 : CollatzResearch.WordTrace tailWord_327354 prefixEnd_327354 112059964114678306446355 := by
  unfold tailWord_327354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2984895314014960114319279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7959720837373226971518077 2984895314014960114319279)
  ·
    refine ⟨4477342971022440171478919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2984895314014960114319279 4477342971022440171478919)
    ·
      refine ⟨6716014456533660257218379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4477342971022440171478919 6716014456533660257218379)
      ·
        refine ⟨10074021684800490385827569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6716014456533660257218379 10074021684800490385827569)
        ·
          refine ⟨7555516263600367789370677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10074021684800490385827569 7555516263600367789370677)
          ·
            refine ⟨708329649712534480253501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7555516263600367789370677 708329649712534480253501)
            ·
              refine ⟨265623618642200430095063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 708329649712534480253501 265623618642200430095063)
              ·
                refine ⟨398435427963300645142595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265623618642200430095063 398435427963300645142595)
                ·
                  refine ⟨597653141944950967713893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398435427963300645142595 597653141944950967713893)
                  ·
                    refine ⟨112059964114678306446355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 597653141944950967713893 112059964114678306446355)
                    ·
                      rfl

theorem cell22_327354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_327354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327354 prefixEnd_327354 := by exact prefixLift 327354
  have htrace : WordTrace (prefixWord ++ tailWord_327354) baseStart_327354 baseEnd_327354 := by
    simpa [prefixWord, tailWord_327354, baseEnd_327354] using wordTrace_append hprefix tailTrace_327354
  have hstable : (prefixWord ++ tailWord_327354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327354).length < 2 ^ (prefixWord ++ tailWord_327354).sum := by decide
  have hdescent : baseEnd_327354 < baseStart_327354 := by decide
  rcases family_descends (prefixWord ++ tailWord_327354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327397 : List Nat := [1, 3, 1, 4, 1, 1, 5, 6]
def baseStart_327397 : Nat := 118140960795 + 327397 * 2 ^ 59
def prefixEnd_327397 : Nat := 4983230072969 + 3 ^ 40 * 327397 * 2
def baseEnd_327397 : Nat := 12452742654826725291247

theorem tailTrace_327397 : CollatzResearch.WordTrace tailWord_327397 prefixEnd_327397 12452742654826725291247 := by
  unfold tailWord_327397
  simp only [CollatzResearch.WordTrace]
  refine ⟨11941149594904058801092445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7960766396602705867394963 11941149594904058801092445)
  ·
    refine ⟨4477931098089022050409667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11941149594904058801092445 4477931098089022050409667)
    ·
      refine ⟨6716896647133533075614501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4477931098089022050409667 6716896647133533075614501)
      ·
        refine ⟨1259418121337537451677719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6716896647133533075614501 1259418121337537451677719)
        ·
          refine ⟨1889127182006306177516579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259418121337537451677719 1889127182006306177516579)
          ·
            refine ⟨2833690773009459266274869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889127182006306177516579 2833690773009459266274869)
            ·
              refine ⟨265658509969636806213269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2833690773009459266274869 265658509969636806213269)
              ·
                refine ⟨12452742654826725291247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 265658509969636806213269 12452742654826725291247)
                ·
                  rfl

theorem cell22_327397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 6].length) (baseStart_327397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327397 prefixEnd_327397 := by exact prefixLift 327397
  have htrace : WordTrace (prefixWord ++ tailWord_327397) baseStart_327397 baseEnd_327397 := by
    simpa [prefixWord, tailWord_327397, baseEnd_327397] using wordTrace_append hprefix tailTrace_327397
  have hstable : (prefixWord ++ tailWord_327397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327397).length < 2 ^ (prefixWord ++ tailWord_327397).sum := by decide
  have hdescent : baseEnd_327397 < baseStart_327397 := by decide
  rcases family_descends (prefixWord ++ tailWord_327397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327399 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 1, 6]
def baseStart_327399 : Nat := 118140960795 + 327399 * 2 ^ 59
def prefixEnd_327399 : Nat := 4983230072969 + 3 ^ 40 * 327399 * 2
def baseEnd_327399 : Nat := 112075368534313189071217

theorem tailTrace_327399 : CollatzResearch.WordTrace tailWord_327399 prefixEnd_327399 112075368534313189071217 := by
  unfold tailWord_327399
  simp only [CollatzResearch.WordTrace]
  refine ⟨11941222540896813142665251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7960815027264542095110167 11941222540896813142665251)
  ·
    refine ⟨17911833811345219713997877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11941222540896813142665251 17911833811345219713997877)
    ·
      refine ⟨1679234419813614348187301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17911833811345219713997877 1679234419813614348187301)
      ·
        refine ⟨314856453715052690285119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1679234419813614348187301 314856453715052690285119)
        ·
          refine ⟨472284680572579035427679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314856453715052690285119 472284680572579035427679)
          ·
            refine ⟨708427020858868553141519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472284680572579035427679 708427020858868553141519)
            ·
              refine ⟨1062640531288302829712279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708427020858868553141519 1062640531288302829712279)
              ·
                refine ⟨1593960796932454244568419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062640531288302829712279 1593960796932454244568419)
                ·
                  refine ⟨2390941195398681366852629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593960796932454244568419 2390941195398681366852629)
                  ·
                    refine ⟨112075368534313189071217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2390941195398681366852629 112075368534313189071217)
                    ·
                      rfl

theorem cell22_327399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_327399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327399 prefixEnd_327399 := by exact prefixLift 327399
  have htrace : WordTrace (prefixWord ++ tailWord_327399) baseStart_327399 baseEnd_327399 := by
    simpa [prefixWord, tailWord_327399, baseEnd_327399] using wordTrace_append hprefix tailTrace_327399
  have hstable : (prefixWord ++ tailWord_327399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327399).length < 2 ^ (prefixWord ++ tailWord_327399).sum := by decide
  have hdescent : baseEnd_327399 < baseStart_327399 := by decide
  rcases family_descends (prefixWord ++ tailWord_327399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327506 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_327506 : Nat := 118140960795 + 327506 * 2 ^ 59
def prefixEnd_327506 : Nat := 4983230072969 + 3 ^ 40 * 327506 * 2
def baseEnd_327506 : Nat := 112111996821000576645889

theorem tailTrace_327506 : CollatzResearch.WordTrace tailWord_327506 prefixEnd_327506 112111996821000576645889 := by
  unfold tailWord_327506
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986281287877292604202593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7963416767672780277873581 2986281287877292604202593)
  ·
    refine ⟨2239710965907969453151945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2986281287877292604202593 2239710965907969453151945)
    ·
      refine ⟨1679783224430977089863959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2239710965907969453151945 1679783224430977089863959)
      ·
        refine ⟨2519674836646465634795939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1679783224430977089863959 2519674836646465634795939)
        ·
          refine ⟨3779512254969698452193909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2519674836646465634795939 3779512254969698452193909)
          ·
            refine ⟨354329273903409229893179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3779512254969698452193909 354329273903409229893179)
            ·
              refine ⟨531493910855113844839769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354329273903409229893179 531493910855113844839769)
              ·
                refine ⟨398620433141335383629827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531493910855113844839769 398620433141335383629827)
                ·
                  refine ⟨597930649712003075444741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398620433141335383629827 597930649712003075444741)
                  ·
                    refine ⟨112111996821000576645889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 597930649712003075444741 112111996821000576645889)
                    ·
                      rfl

theorem cell22_327506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_327506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327506 prefixEnd_327506 := by exact prefixLift 327506
  have htrace : WordTrace (prefixWord ++ tailWord_327506) baseStart_327506 baseEnd_327506 := by
    simpa [prefixWord, tailWord_327506, baseEnd_327506] using wordTrace_append hprefix tailTrace_327506
  have hstable : (prefixWord ++ tailWord_327506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327506).length < 2 ^ (prefixWord ++ tailWord_327506).sum := by decide
  have hdescent : baseEnd_327506 < baseStart_327506 := by decide
  rcases family_descends (prefixWord ++ tailWord_327506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327574 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_327574 : Nat := 118140960795 + 327574 * 2 ^ 59
def prefixEnd_327574 : Nat := 4983230072969 + 3 ^ 40 * 327574 * 2
def baseEnd_327574 : Nat := 112135274610671065945681

theorem tailTrace_327574 : CollatzResearch.WordTrace tailWord_327574 prefixEnd_327574 112135274610671065945681 := by
  unfold tailWord_327574
  simp only [CollatzResearch.WordTrace]
  refine ⟨746725332203926126892861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7965070210175212020190517 746725332203926126892861)
  ·
    refine ⟨280021999576472297584823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 746725332203926126892861 280021999576472297584823)
    ·
      refine ⟨420032999364708446377235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280021999576472297584823 420032999364708446377235)
      ·
        refine ⟨630049499047062669565853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420032999364708446377235 630049499047062669565853)
        ·
          refine ⟨236268562142648501087195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 630049499047062669565853 236268562142648501087195)
          ·
            refine ⟨354402843213972751630793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236268562142648501087195 354402843213972751630793)
            ·
              refine ⟨265802132410479563723095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354402843213972751630793 265802132410479563723095)
              ·
                refine ⟨398703198615719345584643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265802132410479563723095 398703198615719345584643)
                ·
                  refine ⟨598054797923579018376965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398703198615719345584643 598054797923579018376965)
                  ·
                    refine ⟨112135274610671065945681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 598054797923579018376965 112135274610671065945681)
                    ·
                      rfl

theorem cell22_327574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_327574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327574 prefixEnd_327574 := by exact prefixLift 327574
  have htrace : WordTrace (prefixWord ++ tailWord_327574) baseStart_327574 baseEnd_327574 := by
    simpa [prefixWord, tailWord_327574, baseEnd_327574] using wordTrace_append hprefix tailTrace_327574
  have hstable : (prefixWord ++ tailWord_327574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327574).length < 2 ^ (prefixWord ++ tailWord_327574).sum := by decide
  have hdescent : baseEnd_327574 < baseStart_327574 := by decide
  rcases family_descends (prefixWord ++ tailWord_327574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327714 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_327714 : Nat := 118140960795 + 327714 * 2 ^ 59
def prefixEnd_327714 : Nat := 4983230072969 + 3 ^ 40 * 327714 * 2
def baseEnd_327714 : Nat := 112183199471757367445251

theorem tailTrace_327714 : CollatzResearch.WordTrace tailWord_327714 prefixEnd_327714 112183199471757367445251 := by
  unfold tailWord_327714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2988177883688905485095549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7968474356503747960254797 2988177883688905485095549)
  ·
    refine ⟨1120566706383339556910831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2988177883688905485095549 1120566706383339556910831)
    ·
      refine ⟨1680850059575009335366247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1120566706383339556910831 1680850059575009335366247)
      ·
        refine ⟨2521275089362514003049371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680850059575009335366247 2521275089362514003049371)
        ·
          refine ⟨3781912634043771004574057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2521275089362514003049371 3781912634043771004574057)
          ·
            refine ⟨2836434475532828253430543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3781912634043771004574057 2836434475532828253430543)
            ·
              refine ⟨4254651713299242380145815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2836434475532828253430543 4254651713299242380145815)
              ·
                refine ⟨6381977569948863570218723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4254651713299242380145815 6381977569948863570218723)
                ·
                  refine ⟨9572966354923295355328085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6381977569948863570218723 9572966354923295355328085)
                  ·
                    refine ⟨112183199471757367445251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9572966354923295355328085 112183199471757367445251)
                    ·
                      rfl

theorem cell22_327714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_327714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327714 prefixEnd_327714 := by exact prefixLift 327714
  have htrace : WordTrace (prefixWord ++ tailWord_327714) baseStart_327714 baseEnd_327714 := by
    simpa [prefixWord, tailWord_327714, baseEnd_327714] using wordTrace_append hprefix tailTrace_327714
  have hstable : (prefixWord ++ tailWord_327714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327714).length < 2 ^ (prefixWord ++ tailWord_327714).sum := by decide
  have hdescent : baseEnd_327714 < baseStart_327714 := by decide
  rcases family_descends (prefixWord ++ tailWord_327714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327836 : List Nat := [2, 2, 3, 2, 1, 1, 4, 7]
def baseStart_327836 : Nat := 118140960795 + 327836 * 2 ^ 59
def prefixEnd_327836 : Nat := 4983230072969 + 3 ^ 40 * 327836 * 2
def baseEnd_327836 : Nat := 12469440284998857321653

theorem tailTrace_327836 : CollatzResearch.WordTrace tailWord_327836 prefixEnd_327836 12469440284998857321653 := by
  unfold tailWord_327836
  simp only [CollatzResearch.WordTrace]
  refine ⟨5978580620156818388161681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7971440826875757850882241 5978580620156818388161681)
  ·
    refine ⟨4483935465117613791121261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5978580620156818388161681 4483935465117613791121261)
    ·
      refine ⟨1681475799419105171670473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4483935465117613791121261 1681475799419105171670473)
      ·
        refine ⟨1261106849564328878752855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1681475799419105171670473 1261106849564328878752855)
        ·
          refine ⟨1891660274346493318129283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261106849564328878752855 1891660274346493318129283)
          ·
            refine ⟨2837490411519739977193925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891660274346493318129283 2837490411519739977193925)
            ·
              refine ⟨532029452159951245723861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2837490411519739977193925 532029452159951245723861)
              ·
                refine ⟨12469440284998857321653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 532029452159951245723861 12469440284998857321653)
                ·
                  rfl

theorem cell22_327836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 7].length) (baseStart_327836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327836 prefixEnd_327836 := by exact prefixLift 327836
  have htrace : WordTrace (prefixWord ++ tailWord_327836) baseStart_327836 baseEnd_327836 := by
    simpa [prefixWord, tailWord_327836, baseEnd_327836] using wordTrace_append hprefix tailTrace_327836
  have hstable : (prefixWord ++ tailWord_327836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327836).length < 2 ^ (prefixWord ++ tailWord_327836).sum := by decide
  have hdescent : baseEnd_327836 < baseStart_327836 := by decide
  rcases family_descends (prefixWord ++ tailWord_327836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327840 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 2, 3]
def baseStart_327840 : Nat := 118140960795 + 327840 * 2 ^ 59
def prefixEnd_327840 : Nat := 4983230072969 + 3 ^ 40 * 327840 * 2
def baseEnd_327840 : Nat := 112226331846735038794865

theorem tailTrace_327840 : CollatzResearch.WordTrace tailWord_327840 prefixEnd_327840 112226331846735038794865 := by
  unfold tailWord_327840
  simp only [CollatzResearch.WordTrace]
  refine ⟨5978653566149572729734487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7971538088199430306312649 5978653566149572729734487)
  ·
    refine ⟨8967980349224359094601731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5978653566149572729734487 8967980349224359094601731)
    ·
      refine ⟨13451970523836538641902597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8967980349224359094601731 13451970523836538641902597)
      ·
        refine ⟨2522244473219350995356737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13451970523836538641902597 2522244473219350995356737)
        ·
          refine ⟨1891683354914513246517553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2522244473219350995356737 1891683354914513246517553)
          ·
            refine ⟨1418762516185884934888165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1891683354914513246517553 1418762516185884934888165)
            ·
              refine ⟨266017971784853425291531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1418762516185884934888165 266017971784853425291531)
              ·
                refine ⟨399026957677280137937297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266017971784853425291531 399026957677280137937297)
                ·
                  refine ⟨299270218257960103452973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399026957677280137937297 299270218257960103452973)
                  ·
                    refine ⟨112226331846735038794865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 299270218257960103452973 112226331846735038794865)
                    ·
                      rfl

theorem cell22_327840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 2, 3].length) (baseStart_327840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327840 prefixEnd_327840 := by exact prefixLift 327840
  have htrace : WordTrace (prefixWord ++ tailWord_327840) baseStart_327840 baseEnd_327840 := by
    simpa [prefixWord, tailWord_327840, baseEnd_327840] using wordTrace_append hprefix tailTrace_327840
  have hstable : (prefixWord ++ tailWord_327840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327840).length < 2 ^ (prefixWord ++ tailWord_327840).sum := by decide
  have hdescent : baseEnd_327840 < baseStart_327840 := by decide
  rcases family_descends (prefixWord ++ tailWord_327840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327874 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_327874 : Nat := 118140960795 + 327874 * 2 ^ 59
def prefixEnd_327874 : Nat := 4983230072969 + 3 ^ 40 * 327874 * 2
def baseEnd_327874 : Nat := 112237970741570283444761

theorem tailTrace_327874 : CollatzResearch.WordTrace tailWord_327874 prefixEnd_327874 112237970741570283444761 := by
  unfold tailWord_327874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2989636803543992316551669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7972364809450646177471117 2989636803543992316551669)
  ·
    refine ⟨280278450332249279676719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2989636803543992316551669 280278450332249279676719)
    ·
      refine ⟨420417675498373919515079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280278450332249279676719 420417675498373919515079)
      ·
        refine ⟨630626513247560879272619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420417675498373919515079 630626513247560879272619)
        ·
          refine ⟨945939769871341318908929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630626513247560879272619 945939769871341318908929)
          ·
            refine ⟨709454827403505989181697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 945939769871341318908929 709454827403505989181697)
            ·
              refine ⟨532091120552629491886273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709454827403505989181697 532091120552629491886273)
              ·
                refine ⟨399068340414472118914705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532091120552629491886273 399068340414472118914705)
                ·
                  refine ⟨299301255310854089186029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399068340414472118914705 299301255310854089186029)
                  ·
                    refine ⟨112237970741570283444761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 299301255310854089186029 112237970741570283444761)
                    ·
                      rfl

theorem cell22_327874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_327874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327874 prefixEnd_327874 := by exact prefixLift 327874
  have htrace : WordTrace (prefixWord ++ tailWord_327874) baseStart_327874 baseEnd_327874 := by
    simpa [prefixWord, tailWord_327874, baseEnd_327874] using wordTrace_append hprefix tailTrace_327874
  have hstable : (prefixWord ++ tailWord_327874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327874).length < 2 ^ (prefixWord ++ tailWord_327874).sum := by decide
  have hdescent : baseEnd_327874 < baseStart_327874 := by decide
  rcases family_descends (prefixWord ++ tailWord_327874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327896 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 1, 7]
def baseStart_327896 : Nat := 118140960795 + 327896 * 2 ^ 59
def prefixEnd_327896 : Nat := 4983230072969 + 3 ^ 40 * 327896 * 2
def baseEnd_327896 : Nat := 112245501791169559394693

theorem tailTrace_327896 : CollatzResearch.WordTrace tailWord_327896 prefixEnd_327896 112245501791169559394693 := by
  unfold tailWord_327896
  simp only [CollatzResearch.WordTrace]
  refine ⟨5979674810048133511753771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7972899746730844682338361 5979674810048133511753771)
  ·
    refine ⟨8969512215072200267630657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5979674810048133511753771 8969512215072200267630657)
    ·
      refine ⟨6727134161304150200722993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8969512215072200267630657 6727134161304150200722993)
      ·
        refine ⟨5045350620978112650542245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6727134161304150200722993 5045350620978112650542245)
        ·
          refine ⟨946003241433396121976671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5045350620978112650542245 946003241433396121976671)
          ·
            refine ⟨1419004862150094182965007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946003241433396121976671 1419004862150094182965007)
            ·
              refine ⟨2128507293225141274447511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419004862150094182965007 2128507293225141274447511)
              ·
                refine ⟨3192760939837711911671267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2128507293225141274447511 3192760939837711911671267)
                ·
                  refine ⟨4789141409756567867506901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192760939837711911671267 4789141409756567867506901)
                  ·
                    refine ⟨112245501791169559394693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4789141409756567867506901 112245501791169559394693)
                    ·
                      rfl

theorem cell22_327896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_327896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327896 prefixEnd_327896 := by exact prefixLift 327896
  have htrace : WordTrace (prefixWord ++ tailWord_327896) baseStart_327896 baseEnd_327896 := by
    simpa [prefixWord, tailWord_327896, baseEnd_327896] using wordTrace_append hprefix tailTrace_327896
  have hstable : (prefixWord ++ tailWord_327896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327896).length < 2 ^ (prefixWord ++ tailWord_327896).sum := by decide
  have hdescent : baseEnd_327896 < baseStart_327896 := by decide
  rcases family_descends (prefixWord ++ tailWord_327896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327906 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_327906 : Nat := 118140960795 + 327906 * 2 ^ 59
def prefixEnd_327906 : Nat := 4983230072969 + 3 ^ 40 * 327906 * 2
def baseEnd_327906 : Nat := 112248924995532866644663

theorem tailTrace_327906 : CollatzResearch.WordTrace tailWord_327906 prefixEnd_327906 112248924995532866644663 := by
  unfold tailWord_327906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2989928587515009682842893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7973142900040025820914381 2989928587515009682842893)
  ·
    refine ⟨1121223220318128631066085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2989928587515009682842893 1121223220318128631066085)
    ·
      refine ⟨210229353809649118324891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1121223220318128631066085 210229353809649118324891)
      ·
        refine ⟨315344030714473677487337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210229353809649118324891 315344030714473677487337)
        ·
          refine ⟨236508023035855258115503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315344030714473677487337 236508023035855258115503)
          ·
            refine ⟨354762034553782887173255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236508023035855258115503 354762034553782887173255)
            ·
              refine ⟨532143051830674330759883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354762034553782887173255 532143051830674330759883)
              ·
                refine ⟨798214577746011496139825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532143051830674330759883 798214577746011496139825)
                ·
                  refine ⟨598660933309508622104869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 798214577746011496139825 598660933309508622104869)
                  ·
                    refine ⟨112248924995532866644663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 598660933309508622104869 112248924995532866644663)
                    ·
                      rfl

theorem cell22_327906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_327906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327906 prefixEnd_327906 := by exact prefixLift 327906
  have htrace : WordTrace (prefixWord ++ tailWord_327906) baseStart_327906 baseEnd_327906 := by
    simpa [prefixWord, tailWord_327906, baseEnd_327906] using wordTrace_append hprefix tailTrace_327906
  have hstable : (prefixWord ++ tailWord_327906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327906).length < 2 ^ (prefixWord ++ tailWord_327906).sum := by decide
  have hdescent : baseEnd_327906 < baseStart_327906 := by decide
  rcases family_descends (prefixWord ++ tailWord_327906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327971 : List Nat := [1, 1, 1, 4, 2, 2, 3, 8]
def baseStart_327971 : Nat := 118140960795 + 327971 * 2 ^ 59
def prefixEnd_327971 : Nat := 4983230072969 + 3 ^ 40 * 327971 * 2
def baseEnd_327971 : Nat := 12474575091543818196607

theorem tailTrace_327971 : CollatzResearch.WordTrace tailWord_327971 prefixEnd_327971 12474575091543818196607 := by
  unfold tailWord_327971
  simp only [CollatzResearch.WordTrace]
  refine ⟨11962085094824554832487767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7974723396549703221658511 11962085094824554832487767)
  ·
    refine ⟨17943127642236832248731651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11962085094824554832487767 17943127642236832248731651)
    ·
      refine ⟨26914691463355248373097477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17943127642236832248731651 26914691463355248373097477)
      ·
        refine ⟨5046504649379109069955777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26914691463355248373097477 5046504649379109069955777)
        ·
          refine ⟨3784878487034331802466833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5046504649379109069955777 3784878487034331802466833)
          ·
            refine ⟨2838658865275748851850125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3784878487034331802466833 2838658865275748851850125)
            ·
              refine ⟨1064497074478405819443797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2838658865275748851850125 1064497074478405819443797)
              ·
                refine ⟨12474575091543818196607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1064497074478405819443797 12474575091543818196607)
                ·
                  rfl

theorem cell22_327971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 8].length) (baseStart_327971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327971 prefixEnd_327971 := by exact prefixLift 327971
  have htrace : WordTrace (prefixWord ++ tailWord_327971) baseStart_327971 baseEnd_327971 := by
    simpa [prefixWord, tailWord_327971, baseEnd_327971] using wordTrace_append hprefix tailTrace_327971
  have hstable : (prefixWord ++ tailWord_327971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327971).length < 2 ^ (prefixWord ++ tailWord_327971).sum := by decide
  have hdescent : baseEnd_327971 < baseStart_327971 := by decide
  rcases family_descends (prefixWord ++ tailWord_327971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327988 : List Nat := [2, 5, 1, 1, 1, 2, 10]
def baseStart_327988 : Nat := 118140960795 + 327988 * 2 ^ 59
def prefixEnd_327988 : Nat := 4983230072969 + 3 ^ 40 * 327988 * 2
def baseEnd_327988 : Nat := 4158407232270814299793

theorem tailTrace_327988 : CollatzResearch.WordTrace tailWord_327988 prefixEnd_327988 4158407232270814299793 := by
  unfold tailWord_327988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5981352567881483367928309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7975136757175311157237745 5981352567881483367928309)
  ·
    refine ⟨560751803238889065743279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5981352567881483367928309 560751803238889065743279)
    ·
      refine ⟨841127704858333598614919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 560751803238889065743279 841127704858333598614919)
      ·
        refine ⟨1261691557287500397922379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 841127704858333598614919 1261691557287500397922379)
        ·
          refine ⟨1892537335931250596883569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261691557287500397922379 1892537335931250596883569)
          ·
            refine ⟨1419403001948437947662677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1892537335931250596883569 1419403001948437947662677)
            ·
              refine ⟨4158407232270814299793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1419403001948437947662677 4158407232270814299793)
              ·
                rfl

theorem cell22_327988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 10].length) (baseStart_327988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_327988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_327988 prefixEnd_327988 := by exact prefixLift 327988
  have htrace : WordTrace (prefixWord ++ tailWord_327988) baseStart_327988 baseEnd_327988 := by
    simpa [prefixWord, tailWord_327988, baseEnd_327988] using wordTrace_append hprefix tailTrace_327988
  have hstable : (prefixWord ++ tailWord_327988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327988).length < 2 ^ (prefixWord ++ tailWord_327988).sum := by decide
  have hdescent : baseEnd_327988 < baseStart_327988 := by decide
  rcases family_descends (prefixWord ++ tailWord_327988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328050 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_328050 : Nat := 118140960795 + 328050 * 2 ^ 59
def prefixEnd_328050 : Nat := 4983230072969 + 3 ^ 40 * 328050 * 2
def baseEnd_328050 : Nat := 37432739712788163681407

theorem tailTrace_328050 : CollatzResearch.WordTrace tailWord_328050 prefixEnd_328050 37432739712788163681407 := by
  unfold tailWord_328050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991241615384587831153401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7976644307692234216409069 2991241615384587831153401)
  ·
    refine ⟨2243431211538440873365051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2991241615384587831153401 2243431211538440873365051)
    ·
      refine ⟨3365146817307661310047577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2243431211538440873365051 3365146817307661310047577)
      ·
        refine ⟨2523860112980745982535683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3365146817307661310047577 2523860112980745982535683)
        ·
          refine ⟨3785790169471118973803525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523860112980745982535683 3785790169471118973803525)
          ·
            refine ⟨709835656775834807588161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3785790169471118973803525 709835656775834807588161)
            ·
              refine ⟨532376742581876105691121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709835656775834807588161 532376742581876105691121)
              ·
                refine ⟨399282556936407079268341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532376742581876105691121 399282556936407079268341)
                ·
                  refine ⟨37432739712788163681407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 399282556936407079268341 37432739712788163681407)
                  ·
                    rfl

theorem cell22_328050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_328050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328050 prefixEnd_328050 := by exact prefixLift 328050
  have htrace : WordTrace (prefixWord ++ tailWord_328050) baseStart_328050 baseEnd_328050 := by
    simpa [prefixWord, tailWord_328050, baseEnd_328050] using wordTrace_append hprefix tailTrace_328050
  have hstable : (prefixWord ++ tailWord_328050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328050).length < 2 ^ (prefixWord ++ tailWord_328050).sum := by decide
  have hdescent : baseEnd_328050 < baseStart_328050 := by decide
  rcases family_descends (prefixWord ++ tailWord_328050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328065 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 2, 5]
def baseStart_328065 : Nat := 118140960795 + 328065 * 2 ^ 59
def prefixEnd_328065 : Nat := 4983230072969 + 3 ^ 40 * 328065 * 2
def baseEnd_328065 : Nat := 112303353944909451919175

theorem tailTrace_328065 : CollatzResearch.WordTrace tailWord_328065 prefixEnd_328065 112303353944909451919175 := by
  unfold tailWord_328065
  simp only [CollatzResearch.WordTrace]
  refine ⟨11965513556484008886409649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7977009037656005924273099 11965513556484008886409649)
  ·
    refine ⟨8974135167363006664807237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11965513556484008886409649 8974135167363006664807237)
    ·
      refine ⟨1682650343880563749651357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8974135167363006664807237 1682650343880563749651357)
      ·
        refine ⟨630993878955211406119259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1682650343880563749651357 630993878955211406119259)
        ·
          refine ⟨946490818432817109178889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630993878955211406119259 946490818432817109178889)
          ·
            refine ⟨709868113824612831884167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 946490818432817109178889 709868113824612831884167)
            ·
              refine ⟨1064802170736919247826251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709868113824612831884167 1064802170736919247826251)
              ·
                refine ⟨1597203256105378871739377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064802170736919247826251 1597203256105378871739377)
                ·
                  refine ⟨1197902442079034153804533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1597203256105378871739377 1197902442079034153804533)
                  ·
                    refine ⟨112303353944909451919175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1197902442079034153804533 112303353944909451919175)
                    ·
                      rfl

theorem cell22_328065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_328065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328065 prefixEnd_328065 := by exact prefixLift 328065
  have htrace : WordTrace (prefixWord ++ tailWord_328065) baseStart_328065 baseEnd_328065 := by
    simpa [prefixWord, tailWord_328065, baseEnd_328065] using wordTrace_append hprefix tailTrace_328065
  have hstable : (prefixWord ++ tailWord_328065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328065).length < 2 ^ (prefixWord ++ tailWord_328065).sum := by decide
  have hdescent : baseEnd_328065 < baseStart_328065 := by decide
  rcases family_descends (prefixWord ++ tailWord_328065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328108 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_328108 : Nat := 118140960795 + 328108 * 2 ^ 59
def prefixEnd_328108 : Nat := 4983230072969 + 3 ^ 40 * 328108 * 2
def baseEnd_328108 : Nat := 112318073723671673094043

theorem tailTrace_328108 : CollatzResearch.WordTrace tailWord_328108 prefixEnd_328108 112318073723671673094043 := by
  unfold tailWord_328108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5983540947664113615112489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7978054596885484820149985 5983540947664113615112489)
  ·
    refine ⟨4487655710748085211334367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5983540947664113615112489 4487655710748085211334367)
    ·
      refine ⟨6731483566122127817001551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4487655710748085211334367 6731483566122127817001551)
      ·
        refine ⟨10097225349183191725502327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6731483566122127817001551 10097225349183191725502327)
        ·
          refine ⟨15145838023774787588253491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10097225349183191725502327 15145838023774787588253491)
          ·
            refine ⟨22718757035662181382380237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15145838023774787588253491 22718757035662181382380237)
            ·
              refine ⟨8519533888373318018392589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22718757035662181382380237 8519533888373318018392589)
              ·
                refine ⟨3194825208139994256897221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8519533888373318018392589 3194825208139994256897221)
                ·
                  refine ⟨599029726526248923168229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3194825208139994256897221 599029726526248923168229)
                  ·
                    refine ⟨112318073723671673094043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 599029726526248923168229 112318073723671673094043)
                    ·
                      rfl

theorem cell22_328108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_328108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328108 prefixEnd_328108 := by exact prefixLift 328108
  have htrace : WordTrace (prefixWord ++ tailWord_328108) baseStart_328108 baseEnd_328108 := by
    simpa [prefixWord, tailWord_328108, baseEnd_328108] using wordTrace_append hprefix tailTrace_328108
  have hstable : (prefixWord ++ tailWord_328108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328108).length < 2 ^ (prefixWord ++ tailWord_328108).sum := by decide
  have hdescent : baseEnd_328108 < baseStart_328108 := by decide
  rcases family_descends (prefixWord ++ tailWord_328108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328138 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_328138 : Nat := 118140960795 + 328138 * 2 ^ 59
def prefixEnd_328138 : Nat := 4983230072969 + 3 ^ 40 * 328138 * 2
def baseEnd_328138 : Nat := 112328343336761594843951

theorem tailTrace_328138 : CollatzResearch.WordTrace tailWord_328138 prefixEnd_328138 112328343336761594843951 := by
  unfold tailWord_328138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992044021304885588454267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7978784056813028235878045 2992044021304885588454267)
  ·
    refine ⟨4488066031957328382681401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2992044021304885588454267 4488066031957328382681401)
    ·
      refine ⟨3366049523967996287011051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4488066031957328382681401 3366049523967996287011051)
      ·
        refine ⟨5049074285951994430516577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3366049523967996287011051 5049074285951994430516577)
        ·
          refine ⟨3786805714463995822887433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5049074285951994430516577 3786805714463995822887433)
          ·
            refine ⟨2840104285847996867165575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3786805714463995822887433 2840104285847996867165575)
            ·
              refine ⟨4260156428771995300748363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840104285847996867165575 4260156428771995300748363)
              ·
                refine ⟨6390234643157992951122545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4260156428771995300748363 6390234643157992951122545)
                ·
                  refine ⟨4792675982368494713341909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6390234643157992951122545 4792675982368494713341909)
                  ·
                    refine ⟨112328343336761594843951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4792675982368494713341909 112328343336761594843951)
                    ·
                      rfl

theorem cell22_328138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_328138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328138 prefixEnd_328138 := by exact prefixLift 328138
  have htrace : WordTrace (prefixWord ++ tailWord_328138) baseStart_328138 baseEnd_328138 := by
    simpa [prefixWord, tailWord_328138, baseEnd_328138] using wordTrace_append hprefix tailTrace_328138
  have hstable : (prefixWord ++ tailWord_328138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328138).length < 2 ^ (prefixWord ++ tailWord_328138).sum := by decide
  have hdescent : baseEnd_328138 < baseStart_328138 := by decide
  rcases family_descends (prefixWord ++ tailWord_328138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328140 : List Nat := [2, 2, 1, 4, 3, 1, 1, 8]
def baseStart_328140 : Nat := 118140960795 + 328140 * 2 ^ 59
def prefixEnd_328140 : Nat := 4983230072969 + 3 ^ 40 * 328140 * 2
def baseEnd_328140 : Nat := 12481003108626028477105

theorem tailTrace_328140 : CollatzResearch.WordTrace tailWord_328140 prefixEnd_328140 12481003108626028477105 := by
  unfold tailWord_328140
  simp only [CollatzResearch.WordTrace]
  refine ⟨5984124515606148347694937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7978832687474864463593249 5984124515606148347694937)
  ·
    refine ⟨4488093386704611260771203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5984124515606148347694937 4488093386704611260771203)
    ·
      refine ⟨6732140080056916891156805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4488093386704611260771203 6732140080056916891156805)
      ·
        refine ⟨1262276265010671917091901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6732140080056916891156805 1262276265010671917091901)
        ·
          refine ⟨473353599379001968909463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1262276265010671917091901 473353599379001968909463)
          ·
            refine ⟨710030399068502953364195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473353599379001968909463 710030399068502953364195)
            ·
              refine ⟨1065045598602754430046293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710030399068502953364195 1065045598602754430046293)
              ·
                refine ⟨12481003108626028477105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1065045598602754430046293 12481003108626028477105)
                ·
                  rfl

theorem cell22_328140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 8].length) (baseStart_328140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328140 prefixEnd_328140 := by exact prefixLift 328140
  have htrace : WordTrace (prefixWord ++ tailWord_328140) baseStart_328140 baseEnd_328140 := by
    simpa [prefixWord, tailWord_328140, baseEnd_328140] using wordTrace_append hprefix tailTrace_328140
  have hstable : (prefixWord ++ tailWord_328140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328140).length < 2 ^ (prefixWord ++ tailWord_328140).sum := by decide
  have hdescent : baseEnd_328140 < baseStart_328140 := by decide
  rcases family_descends (prefixWord ++ tailWord_328140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328146 : List Nat := [3, 2, 2, 4, 1, 2, 1, 3, 4]
def baseStart_328146 : Nat := 118140960795 + 328146 * 2 ^ 59
def prefixEnd_328146 : Nat := 4983230072969 + 3 ^ 40 * 328146 * 2
def baseEnd_328146 : Nat := 37443693966750746881309

theorem tailTrace_328146 : CollatzResearch.WordTrace tailWord_328146 prefixEnd_328146 37443693966750746881309 := by
  unfold tailWord_328146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992116967297639930027073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7978978579460373146738861 2992116967297639930027073)
  ·
    refine ⟨2244087725473229947520305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2992116967297639930027073 2244087725473229947520305)
    ·
      refine ⟨1683065794104922460640229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2244087725473229947520305 1683065794104922460640229)
      ·
        refine ⟨315574836394672961370043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1683065794104922460640229 315574836394672961370043)
        ·
          refine ⟨473362254592009442055065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315574836394672961370043 473362254592009442055065)
          ·
            refine ⟨355021690944007081541299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473362254592009442055065 355021690944007081541299)
            ·
              refine ⟨532532536416010622311949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355021690944007081541299 532532536416010622311949)
              ·
                refine ⟨199699701156003983366981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 532532536416010622311949 199699701156003983366981)
                ·
                  refine ⟨37443693966750746881309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199699701156003983366981 37443693966750746881309)
                  ·
                    rfl

theorem cell22_328146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_328146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328146 prefixEnd_328146 := by exact prefixLift 328146
  have htrace : WordTrace (prefixWord ++ tailWord_328146) baseStart_328146 baseEnd_328146 := by
    simpa [prefixWord, tailWord_328146, baseEnd_328146] using wordTrace_append hprefix tailTrace_328146
  have hstable : (prefixWord ++ tailWord_328146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328146).length < 2 ^ (prefixWord ++ tailWord_328146).sum := by decide
  have hdescent : baseEnd_328146 < baseStart_328146 := by decide
  rcases family_descends (prefixWord ++ tailWord_328146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328178 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_328178 : Nat := 118140960795 + 328178 * 2 ^ 59
def prefixEnd_328178 : Nat := 4983230072969 + 3 ^ 40 * 328178 * 2
def baseEnd_328178 : Nat := 112342036154214823843829

theorem tailTrace_328178 : CollatzResearch.WordTrace tailWord_328178 prefixEnd_328178 112342036154214823843829 := by
  unfold tailWord_328178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992408751268657296318297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7979756670049752790182125 2992408751268657296318297)
  ·
    refine ⟨2244306563451492972238723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2992408751268657296318297 2244306563451492972238723)
    ·
      refine ⟨3366459845177239458358085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2244306563451492972238723 3366459845177239458358085)
      ·
        refine ⟨631211220970732398442141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3366459845177239458358085 631211220970732398442141)
        ·
          refine ⟨236704207864024649415803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 631211220970732398442141 236704207864024649415803)
          ·
            refine ⟨355056311796036974123705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236704207864024649415803 355056311796036974123705)
            ·
              refine ⟨266292233847027730592779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355056311796036974123705 266292233847027730592779)
              ·
                refine ⟨399438350770541595889169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266292233847027730592779 399438350770541595889169)
                ·
                  refine ⟨299578763077906196916877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399438350770541595889169 299578763077906196916877)
                  ·
                    refine ⟨112342036154214823843829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 299578763077906196916877 112342036154214823843829)
                    ·
                      rfl

theorem cell22_328178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_328178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328178 prefixEnd_328178 := by exact prefixLift 328178
  have htrace : WordTrace (prefixWord ++ tailWord_328178) baseStart_328178 baseEnd_328178 := by
    simpa [prefixWord, tailWord_328178, baseEnd_328178] using wordTrace_append hprefix tailTrace_328178
  have hstable : (prefixWord ++ tailWord_328178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328178).length < 2 ^ (prefixWord ++ tailWord_328178).sum := by decide
  have hdescent : baseEnd_328178 < baseStart_328178 := by decide
  rcases family_descends (prefixWord ++ tailWord_328178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328183 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 6, 5]
def baseStart_328183 : Nat := 118140960795 + 328183 * 2 ^ 59
def prefixEnd_328183 : Nat := 4983230072969 + 3 ^ 40 * 328183 * 2
def baseEnd_328183 : Nat := 112343747756396477468813

theorem tailTrace_328183 : CollatzResearch.WordTrace tailWord_328183 prefixEnd_328183 112343747756396477468813 := by
  unfold tailWord_328183
  simp only [CollatzResearch.WordTrace]
  refine ⟨11969817370056515039205203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7979878246704343359470135 11969817370056515039205203)
  ·
    refine ⟨17954726055084772558807805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11969817370056515039205203 17954726055084772558807805)
    ·
      refine ⟨6733022270656789709552927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17954726055084772558807805 6733022270656789709552927)
      ·
        refine ⟨10099533405985184564329391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6733022270656789709552927 10099533405985184564329391)
        ·
          refine ⟨15149300108977776846494087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10099533405985184564329391 15149300108977776846494087)
          ·
            refine ⟨22723950163466665269741131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15149300108977776846494087 22723950163466665269741131)
            ·
              refine ⟨34085925245199997904611697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22723950163466665269741131 34085925245199997904611697)
              ·
                refine ⟨25564443933899998428458773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34085925245199997904611697 25564443933899998428458773)
                ·
                  refine ⟨1198333309401562426334005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25564443933899998428458773 1198333309401562426334005)
                  ·
                    refine ⟨112343747756396477468813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1198333309401562426334005 112343747756396477468813)
                    ·
                      rfl

theorem cell22_328183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_328183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328183 prefixEnd_328183 := by exact prefixLift 328183
  have htrace : WordTrace (prefixWord ++ tailWord_328183) baseStart_328183 baseEnd_328183 := by
    simpa [prefixWord, tailWord_328183, baseEnd_328183] using wordTrace_append hprefix tailTrace_328183
  have hstable : (prefixWord ++ tailWord_328183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328183).length < 2 ^ (prefixWord ++ tailWord_328183).sum := by decide
  have hdescent : baseEnd_328183 < baseStart_328183 := by decide
  rcases family_descends (prefixWord ++ tailWord_328183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328232 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 3, 4]
def baseStart_328232 : Nat := 118140960795 + 328232 * 2 ^ 59
def prefixEnd_328232 : Nat := 4983230072969 + 3 ^ 40 * 328232 * 2
def baseEnd_328232 : Nat := 112360521457776682993663

theorem tailTrace_328232 : CollatzResearch.WordTrace tailWord_328232 prefixEnd_328232 112360521457776682993663 := by
  unfold tailWord_328232
  simp only [CollatzResearch.WordTrace]
  refine ⟨5985802273439498203869475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7981069697919330938492633 5985802273439498203869475)
  ·
    refine ⟨8978703410159247305804213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5985802273439498203869475 8978703410159247305804213)
    ·
      refine ⟨841753444702429434919145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8978703410159247305804213 841753444702429434919145)
      ·
        refine ⟨631315083526822076189359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 841753444702429434919145 631315083526822076189359)
        ·
          refine ⟨946972625290233114284039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631315083526822076189359 946972625290233114284039)
          ·
            refine ⟨1420458937935349671426059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946972625290233114284039 1420458937935349671426059)
            ·
              refine ⟨2130688406903024507139089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420458937935349671426059 2130688406903024507139089)
              ·
                refine ⟨1598016305177268380354317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2130688406903024507139089 1598016305177268380354317)
                ·
                  refine ⟨599256114441475642632869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1598016305177268380354317 599256114441475642632869)
                  ·
                    refine ⟨112360521457776682993663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 599256114441475642632869 112360521457776682993663)
                    ·
                      rfl

theorem cell22_328232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_328232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328232 prefixEnd_328232 := by exact prefixLift 328232
  have htrace : WordTrace (prefixWord ++ tailWord_328232) baseStart_328232 baseEnd_328232 := by
    simpa [prefixWord, tailWord_328232, baseEnd_328232] using wordTrace_append hprefix tailTrace_328232
  have hstable : (prefixWord ++ tailWord_328232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328232).length < 2 ^ (prefixWord ++ tailWord_328232).sum := by decide
  have hdescent : baseEnd_328232 < baseStart_328232 := by decide
  rcases family_descends (prefixWord ++ tailWord_328232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328296 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 1, 5]
def baseStart_328296 : Nat := 118140960795 + 328296 * 2 ^ 59
def prefixEnd_328296 : Nat := 4983230072969 + 3 ^ 40 * 328296 * 2
def baseEnd_328296 : Nat := 112382429965701849393467

theorem tailTrace_328296 : CollatzResearch.WordTrace tailWord_328296 prefixEnd_328296 112382429965701849393467 := by
  unfold tailWord_328296
  simp only [CollatzResearch.WordTrace]
  refine ⟨5986969409323567669034371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7982625879098090225379161 5986969409323567669034371)
  ·
    refine ⟨8980454113985351503551557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5986969409323567669034371 8980454113985351503551557)
    ·
      refine ⟨1683835146372253406915917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8980454113985351503551557 1683835146372253406915917)
      ·
        refine ⟨631438179889595027593469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1683835146372253406915917 631438179889595027593469)
        ·
          refine ⟨236789317458598135347551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 631438179889595027593469 236789317458598135347551)
          ·
            refine ⟨355183976187897203021327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236789317458598135347551 355183976187897203021327)
            ·
              refine ⟨532775964281845804531991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355183976187897203021327 532775964281845804531991)
              ·
                refine ⟨799163946422768706797987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532775964281845804531991 799163946422768706797987)
                ·
                  refine ⟨1198745919634153060196981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799163946422768706797987 1198745919634153060196981)
                  ·
                    refine ⟨112382429965701849393467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1198745919634153060196981 112382429965701849393467)
                    ·
                      rfl

theorem cell22_328296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_328296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328296 prefixEnd_328296 := by exact prefixLift 328296
  have htrace : WordTrace (prefixWord ++ tailWord_328296) baseStart_328296 baseEnd_328296 := by
    simpa [prefixWord, tailWord_328296, baseEnd_328296] using wordTrace_append hprefix tailTrace_328296
  have hstable : (prefixWord ++ tailWord_328296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328296).length < 2 ^ (prefixWord ++ tailWord_328296).sum := by decide
  have hdescent : baseEnd_328296 < baseStart_328296 := by decide
  rcases family_descends (prefixWord ++ tailWord_328296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328320 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 7]
def baseStart_328320 : Nat := 118140960795 + 328320 * 2 ^ 59
def prefixEnd_328320 : Nat := 4983230072969 + 3 ^ 40 * 328320 * 2
def baseEnd_328320 : Nat := 37463548552057928931131

theorem tailTrace_328320 : CollatzResearch.WordTrace tailWord_328320 prefixEnd_328320 37463548552057928931131 := by
  unfold tailWord_328320
  simp only [CollatzResearch.WordTrace]
  refine ⟨5987407085280093718471207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7983209447040124957961609 5987407085280093718471207)
  ·
    refine ⟨8981110627920140577706811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5987407085280093718471207 8981110627920140577706811)
    ·
      refine ⟨13471665941880210866560217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8981110627920140577706811 13471665941880210866560217)
      ·
        refine ⟨10103749456410158149920163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13471665941880210866560217 10103749456410158149920163)
        ·
          refine ⟨15155624184615237224880245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10103749456410158149920163 15155624184615237224880245)
          ·
            refine ⟨1420839767307678489832523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15155624184615237224880245 1420839767307678489832523)
            ·
              refine ⟨2131259650961517734748785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420839767307678489832523 2131259650961517734748785)
              ·
                refine ⟨1598444738221138301061589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2131259650961517734748785 1598444738221138301061589)
                ·
                  refine ⟨37463548552057928931131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1598444738221138301061589 37463548552057928931131)
                  ·
                    rfl

theorem cell22_328320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_328320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328320 prefixEnd_328320 := by exact prefixLift 328320
  have htrace : WordTrace (prefixWord ++ tailWord_328320) baseStart_328320 baseEnd_328320 := by
    simpa [prefixWord, tailWord_328320, baseEnd_328320] using wordTrace_append hprefix tailTrace_328320
  have hstable : (prefixWord ++ tailWord_328320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328320).length < 2 ^ (prefixWord ++ tailWord_328320).sum := by decide
  have hdescent : baseEnd_328320 < baseStart_328320 := by decide
  rcases family_descends (prefixWord ++ tailWord_328320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328367 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 3, 4]
def baseStart_328367 : Nat := 118140960795 + 328367 * 2 ^ 59
def prefixEnd_328367 : Nat := 4983230072969 + 3 ^ 40 * 328367 * 2
def baseEnd_328367 : Nat := 112406734716681330868249

theorem tailTrace_328367 : CollatzResearch.WordTrace tailWord_328367 prefixEnd_328367 112406734716681330868249 := by
  unfold tailWord_328367
  simp only [CollatzResearch.WordTrace]
  refine ⟨11976528401389914463903355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7984352267593276309268903 11976528401389914463903355)
  ·
    refine ⟨17964792602084871695855033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11976528401389914463903355 17964792602084871695855033)
    ·
      refine ⟨13473594451563653771891275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17964792602084871695855033 13473594451563653771891275)
      ·
        refine ⟨20210391677345480657836913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13473594451563653771891275 20210391677345480657836913)
        ·
          refine ⟨15157793758009110493377685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20210391677345480657836913 15157793758009110493377685)
          ·
            refine ⟨710521582406677054377079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15157793758009110493377685 710521582406677054377079)
            ·
              refine ⟨1065782373610015581565619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710521582406677054377079 1065782373610015581565619)
              ·
                refine ⟨1598673560415023372348429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065782373610015581565619 1598673560415023372348429)
                ·
                  refine ⟨599502585155633764630661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1598673560415023372348429 599502585155633764630661)
                  ·
                    refine ⟨112406734716681330868249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 599502585155633764630661 112406734716681330868249)
                    ·
                      rfl

theorem cell22_328367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_328367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328367 prefixEnd_328367 := by exact prefixLift 328367
  have htrace : WordTrace (prefixWord ++ tailWord_328367) baseStart_328367 baseEnd_328367 := by
    simpa [prefixWord, tailWord_328367, baseEnd_328367] using wordTrace_append hprefix tailTrace_328367
  have hstable : (prefixWord ++ tailWord_328367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328367).length < 2 ^ (prefixWord ++ tailWord_328367).sum := by decide
  have hdescent : baseEnd_328367 < baseStart_328367 := by decide
  rcases family_descends (prefixWord ++ tailWord_328367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328395 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 5, 6]
def baseStart_328395 : Nat := 118140960795 + 328395 * 2 ^ 59
def prefixEnd_328395 : Nat := 4983230072969 + 3 ^ 40 * 328395 * 2
def baseEnd_328395 : Nat := 112416319688898591168163

theorem tailTrace_328395 : CollatzResearch.WordTrace tailWord_328395 prefixEnd_328395 112416319688898591168163 := by
  unfold tailWord_328395
  simp only [CollatzResearch.WordTrace]
  refine ⟨11977549645288475245922639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7985033096858983497281759 11977549645288475245922639)
  ·
    refine ⟨17966324467932712868883959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11977549645288475245922639 17966324467932712868883959)
    ·
      refine ⟨26949486701899069303325939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17966324467932712868883959 26949486701899069303325939)
      ·
        refine ⟨40424230052848603954988909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26949486701899069303325939 40424230052848603954988909)
        ·
          refine ⟨15159086269818226483120841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40424230052848603954988909 15159086269818226483120841)
          ·
            refine ⟨11369314702363669862340631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15159086269818226483120841 11369314702363669862340631)
            ·
              refine ⟨17053972053545504793510947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11369314702363669862340631 17053972053545504793510947)
              ·
                refine ⟨25580958080318257190266421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17053972053545504793510947 25580958080318257190266421)
                ·
                  refine ⟨2398214820029836611587477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25580958080318257190266421 2398214820029836611587477)
                  ·
                    refine ⟨112416319688898591168163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2398214820029836611587477 112416319688898591168163)
                    ·
                      rfl

theorem cell22_328395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_328395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328395 prefixEnd_328395 := by exact prefixLift 328395
  have htrace : WordTrace (prefixWord ++ tailWord_328395) baseStart_328395 baseEnd_328395 := by
    simpa [prefixWord, tailWord_328395, baseEnd_328395] using wordTrace_append hprefix tailTrace_328395
  have hstable : (prefixWord ++ tailWord_328395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328395).length < 2 ^ (prefixWord ++ tailWord_328395).sum := by decide
  have hdescent : baseEnd_328395 < baseStart_328395 := by decide
  rcases family_descends (prefixWord ++ tailWord_328395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328510 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_328510 : Nat := 118140960795 + 328510 * 2 ^ 59
def prefixEnd_328510 : Nat := 4983230072969 + 3 ^ 40 * 328510 * 2
def baseEnd_328510 : Nat := 112455686539076624542811

theorem tailTrace_328510 : CollatzResearch.WordTrace tailWord_328510 prefixEnd_328510 112455686539076624542811 := by
  unfold tailWord_328510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497718004983981235794873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7987829359914566590905989 1497718004983981235794873)
  ·
    refine ⟨1123288503737985926846155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1497718004983981235794873 1123288503737985926846155)
    ·
      refine ⟨1684932755606978890269233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123288503737985926846155 1684932755606978890269233)
      ·
        refine ⟨1263699566705234167701925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1684932755606978890269233 1263699566705234167701925)
        ·
          refine ⟨236943668757231406444111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1263699566705234167701925 236943668757231406444111)
          ·
            refine ⟨355415503135847109666167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236943668757231406444111 355415503135847109666167)
            ·
              refine ⟨533123254703770664499251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355415503135847109666167 533123254703770664499251)
              ·
                refine ⟨799684882055655996748877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533123254703770664499251 799684882055655996748877)
                ·
                  refine ⟨299881830770870998780829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799684882055655996748877 299881830770870998780829)
                  ·
                    refine ⟨112455686539076624542811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 299881830770870998780829 112455686539076624542811)
                    ·
                      rfl

theorem cell22_328510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_328510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328510 prefixEnd_328510 := by exact prefixLift 328510
  have htrace : WordTrace (prefixWord ++ tailWord_328510) baseStart_328510 baseEnd_328510 := by
    simpa [prefixWord, tailWord_328510, baseEnd_328510] using wordTrace_append hprefix tailTrace_328510
  have hstable : (prefixWord ++ tailWord_328510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328510).length < 2 ^ (prefixWord ++ tailWord_328510).sum := by decide
  have hdescent : baseEnd_328510 < baseStart_328510 := by decide
  rcases family_descends (prefixWord ++ tailWord_328510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328517 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 6]
def baseStart_328517 : Nat := 118140960795 + 328517 * 2 ^ 59
def prefixEnd_328517 : Nat := 4983230072969 + 3 ^ 40 * 328517 * 2
def baseEnd_328517 : Nat := 37486027594043646539263

theorem tailTrace_328517 : CollatzResearch.WordTrace tailWord_328517 prefixEnd_328517 37486027594043646539263 := by
  unfold tailWord_328517
  simp only [CollatzResearch.WordTrace]
  refine ⟨11981999350846490081863805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7987999567230993387909203 11981999350846490081863805)
  ·
    refine ⟨4493249756567433780698927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11981999350846490081863805 4493249756567433780698927)
    ·
      refine ⟨6739874634851150671048391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4493249756567433780698927 6739874634851150671048391)
      ·
        refine ⟨10109811952276726006572587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6739874634851150671048391 10109811952276726006572587)
        ·
          refine ⟨15164717928415089009858881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10109811952276726006572587 15164717928415089009858881)
          ·
            refine ⟨11373538446311316757394161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15164717928415089009858881 11373538446311316757394161)
            ·
              refine ⟨8530153834733487568045621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11373538446311316757394161 8530153834733487568045621)
              ·
                refine ⟨799701922006264459504277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8530153834733487568045621 799701922006264459504277)
                ·
                  refine ⟨37486027594043646539263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 799701922006264459504277 37486027594043646539263)
                  ·
                    rfl

theorem cell22_328517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_328517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328517 prefixEnd_328517 := by exact prefixLift 328517
  have htrace : WordTrace (prefixWord ++ tailWord_328517) baseStart_328517 baseEnd_328517 := by
    simpa [prefixWord, tailWord_328517, baseEnd_328517] using wordTrace_append hprefix tailTrace_328517
  have hstable : (prefixWord ++ tailWord_328517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328517).length < 2 ^ (prefixWord ++ tailWord_328517).sum := by decide
  have hdescent : baseEnd_328517 < baseStart_328517 := by decide
  rcases family_descends (prefixWord ++ tailWord_328517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328549 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 6, 3]
def baseStart_328549 : Nat := 118140960795 + 328549 * 2 ^ 59
def prefixEnd_328549 : Nat := 4983230072969 + 3 ^ 40 * 328549 * 2
def baseEnd_328549 : Nat := 112469037036093522817691

theorem tailTrace_328549 : CollatzResearch.WordTrace tailWord_328549 prefixEnd_328549 112469037036093522817691 := by
  unfold tailWord_328549
  simp only [CollatzResearch.WordTrace]
  refine ⟨11983166486730559547028701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7988777657820373031352467 11983166486730559547028701)
  ·
    refine ⟨4493687432523959830135763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11983166486730559547028701 4493687432523959830135763)
    ·
      refine ⟨6740531148785939745203645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4493687432523959830135763 6740531148785939745203645)
      ·
        refine ⟨2527699180794727404451367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6740531148785939745203645 2527699180794727404451367)
        ·
          refine ⟨3791548771192091106677051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527699180794727404451367 3791548771192091106677051)
          ·
            refine ⟨5687323156788136660015577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3791548771192091106677051 5687323156788136660015577)
            ·
              refine ⟨4265492367591102495011683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5687323156788136660015577 4265492367591102495011683)
              ·
                refine ⟨6398238551386653742517525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4265492367591102495011683 6398238551386653742517525)
                ·
                  refine ⟨299917432096249394180509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6398238551386653742517525 299917432096249394180509)
                  ·
                    refine ⟨112469037036093522817691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 299917432096249394180509 112469037036093522817691)
                    ·
                      rfl

theorem cell22_328549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_328549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328549 prefixEnd_328549 := by exact prefixLift 328549
  have htrace : WordTrace (prefixWord ++ tailWord_328549) baseStart_328549 baseEnd_328549 := by
    simpa [prefixWord, tailWord_328549, baseEnd_328549] using wordTrace_append hprefix tailTrace_328549
  have hstable : (prefixWord ++ tailWord_328549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328549).length < 2 ^ (prefixWord ++ tailWord_328549).sum := by decide
  have hdescent : baseEnd_328549 < baseStart_328549 := by decide
  rcases family_descends (prefixWord ++ tailWord_328549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328592 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_328592 : Nat := 118140960795 + 328592 * 2 ^ 59
def prefixEnd_328592 : Nat := 4983230072969 + 3 ^ 40 * 328592 * 2
def baseEnd_328592 : Nat := 112483756814855743992559

theorem tailTrace_328592 : CollatzResearch.WordTrace tailWord_328592 prefixEnd_328592 112483756814855743992559 := by
  unfold tailWord_328592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5992367412787388945422015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7989823217049851927229353 5992367412787388945422015)
  ·
    refine ⟨8988551119181083418133023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5992367412787388945422015 8988551119181083418133023)
    ·
      refine ⟨13482826678771625127199535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8988551119181083418133023 13482826678771625127199535)
      ·
        refine ⟨20224240018157437690799303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13482826678771625127199535 20224240018157437690799303)
        ·
          refine ⟨30336360027236156536198955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20224240018157437690799303 30336360027236156536198955)
          ·
            refine ⟨45504540040854234804298433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30336360027236156536198955 45504540040854234804298433)
            ·
              refine ⟨34128405030640676103223825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45504540040854234804298433 34128405030640676103223825)
              ·
                refine ⟨25596303772980507077417869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34128405030640676103223825 25596303772980507077417869)
                ·
                  refine ⟨9598613914867690154031701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25596303772980507077417869 9598613914867690154031701)
                  ·
                    refine ⟨112483756814855743992559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9598613914867690154031701 112483756814855743992559)
                    ·
                      rfl

theorem cell22_328592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_328592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328592 prefixEnd_328592 := by exact prefixLift 328592
  have htrace : WordTrace (prefixWord ++ tailWord_328592) baseStart_328592 baseEnd_328592 := by
    simpa [prefixWord, tailWord_328592, baseEnd_328592] using wordTrace_append hprefix tailTrace_328592
  have hstable : (prefixWord ++ tailWord_328592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328592).length < 2 ^ (prefixWord ++ tailWord_328592).sum := by decide
  have hdescent : baseEnd_328592 < baseStart_328592 := by decide
  rcases family_descends (prefixWord ++ tailWord_328592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328596 : List Nat := [2, 4, 2, 1, 1, 1, 5, 6]
def baseStart_328596 : Nat := 118140960795 + 328596 * 2 ^ 59
def prefixEnd_328596 : Nat := 4983230072969 + 3 ^ 40 * 328596 * 2
def baseEnd_328596 : Nat := 12498347344066785210283

theorem tailTrace_328596 : CollatzResearch.WordTrace tailWord_328596 prefixEnd_328596 12498347344066785210283 := by
  unfold tailWord_328596
  simp only [CollatzResearch.WordTrace]
  refine ⟨5992440358780143286994821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7989920478373524382659761 5992440358780143286994821)
  ·
    refine ⟨1123582567271276866311529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5992440358780143286994821 1123582567271276866311529)
    ·
      refine ⟨842686925453457649733647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1123582567271276866311529 842686925453457649733647)
      ·
        refine ⟨1264030388180186474600471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842686925453457649733647 1264030388180186474600471)
        ·
          refine ⟨1896045582270279711900707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1264030388180186474600471 1896045582270279711900707)
          ·
            refine ⟨2844068373405419567851061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896045582270279711900707 2844068373405419567851061)
            ·
              refine ⟨266631410006758084486037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2844068373405419567851061 266631410006758084486037)
              ·
                refine ⟨12498347344066785210283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 266631410006758084486037 12498347344066785210283)
                ·
                  rfl

theorem cell22_328596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 6].length) (baseStart_328596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328596 prefixEnd_328596 := by exact prefixLift 328596
  have htrace : WordTrace (prefixWord ++ tailWord_328596) baseStart_328596 baseEnd_328596 := by
    simpa [prefixWord, tailWord_328596, baseEnd_328596] using wordTrace_append hprefix tailTrace_328596
  have hstable : (prefixWord ++ tailWord_328596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328596).length < 2 ^ (prefixWord ++ tailWord_328596).sum := by decide
  have hdescent : baseEnd_328596 < baseStart_328596 := by decide
  rcases family_descends (prefixWord ++ tailWord_328596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328662 : List Nat := [5, 2, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_328662 : Nat := 118140960795 + 328662 * 2 ^ 59
def prefixEnd_328662 : Nat := 4983230072969 + 3 ^ 40 * 328662 * 2
def baseEnd_328662 : Nat := 112507719245398894742345

theorem tailTrace_328662 : CollatzResearch.WordTrace tailWord_328662 prefixEnd_328662 112507719245398894742345 := by
  unfold tailWord_328662
  simp only [CollatzResearch.WordTrace]
  refine ⟨749205495957573740368265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7991525290214119897261493 749205495957573740368265)
  ·
    refine ⟨561904121968180305276199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 749205495957573740368265 561904121968180305276199)
    ·
      refine ⟨842856182952270457914299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 561904121968180305276199 842856182952270457914299)
      ·
        refine ⟨1264284274428405686871449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842856182952270457914299 1264284274428405686871449)
        ·
          refine ⟨948213205821304265153587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1264284274428405686871449 948213205821304265153587)
          ·
            refine ⟨1422319808731956397730381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948213205821304265153587 1422319808731956397730381)
            ·
              refine ⟨533369928274483649148893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1422319808731956397730381 533369928274483649148893)
              ·
                refine ⟨200013723102931368430835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 533369928274483649148893 200013723102931368430835)
                ·
                  refine ⟨300020584654397052646253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200013723102931368430835 300020584654397052646253)
                  ·
                    refine ⟨112507719245398894742345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 300020584654397052646253 112507719245398894742345)
                    ·
                      rfl

theorem cell22_328662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_328662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328662 prefixEnd_328662 := by exact prefixLift 328662
  have htrace : WordTrace (prefixWord ++ tailWord_328662) baseStart_328662 baseEnd_328662 := by
    simpa [prefixWord, tailWord_328662, baseEnd_328662] using wordTrace_append hprefix tailTrace_328662
  have hstable : (prefixWord ++ tailWord_328662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328662).length < 2 ^ (prefixWord ++ tailWord_328662).sum := by decide
  have hdescent : baseEnd_328662 < baseStart_328662 := by decide
  rcases family_descends (prefixWord ++ tailWord_328662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328699 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 6, 4]
def baseStart_328699 : Nat := 118140960795 + 328699 * 2 ^ 59
def prefixEnd_328699 : Nat := 4983230072969 + 3 ^ 40 * 328699 * 2
def baseEnd_328699 : Nat := 112520385101543131567231

theorem tailTrace_328699 : CollatzResearch.WordTrace tailWord_328699 prefixEnd_328699 112520385101543131567231 := by
  unfold tailWord_328699
  simp only [CollatzResearch.WordTrace]
  refine ⟨11988637436187135164989151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7992424957458090109992767 11988637436187135164989151)
  ·
    refine ⟨17982956154280702747483727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11988637436187135164989151 17982956154280702747483727)
    ·
      refine ⟨26974434231421054121225591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17982956154280702747483727 26974434231421054121225591)
      ·
        refine ⟨40461651347131581181838387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26974434231421054121225591 40461651347131581181838387)
        ·
          refine ⟨60692477020697371772757581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40461651347131581181838387 60692477020697371772757581)
          ·
            refine ⟨22759678882761514414784093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60692477020697371772757581 22759678882761514414784093)
            ·
              refine ⟨8534879581035567905544035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22759678882761514414784093 8534879581035567905544035)
              ·
                refine ⟨12802319371553351858316053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8534879581035567905544035 12802319371553351858316053)
                ·
                  refine ⟨600108720541563368358565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12802319371553351858316053 600108720541563368358565)
                  ·
                    refine ⟨112520385101543131567231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 600108720541563368358565 112520385101543131567231)
                    ·
                      rfl

theorem cell22_328699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 4].length) (baseStart_328699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328699 prefixEnd_328699 := by exact prefixLift 328699
  have htrace : WordTrace (prefixWord ++ tailWord_328699) baseStart_328699 baseEnd_328699 := by
    simpa [prefixWord, tailWord_328699, baseEnd_328699] using wordTrace_append hprefix tailTrace_328699
  have hstable : (prefixWord ++ tailWord_328699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328699).length < 2 ^ (prefixWord ++ tailWord_328699).sum := by decide
  have hdescent : baseEnd_328699 < baseStart_328699 := by decide
  rcases family_descends (prefixWord ++ tailWord_328699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328716 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_328716 : Nat := 118140960795 + 328716 * 2 ^ 59
def prefixEnd_328716 : Nat := 4983230072969 + 3 ^ 40 * 328716 * 2
def baseEnd_328716 : Nat := 112526204548960753892179

theorem tailTrace_328716 : CollatzResearch.WordTrace tailWord_328716 prefixEnd_328716 112526204548960753892179 := by
  unfold tailWord_328716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5994628738562773534179001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7992838318083698045572001 5994628738562773534179001)
  ·
    refine ⟨4495971553922080150634251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5994628738562773534179001 4495971553922080150634251)
    ·
      refine ⟨6743957330883120225951377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4495971553922080150634251 6743957330883120225951377)
      ·
        refine ⟨5057967998162340169463533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6743957330883120225951377 5057967998162340169463533)
        ·
          refine ⟨1896737999310877563548825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5057967998162340169463533 1896737999310877563548825)
          ·
            refine ⟨1422553499483158172661619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1896737999310877563548825 1422553499483158172661619)
            ·
              refine ⟨2133830249224737258992429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422553499483158172661619 2133830249224737258992429)
              ·
                refine ⟨800186343459276472122161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2133830249224737258992429 800186343459276472122161)
                ·
                  refine ⟨600139757594457354091621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 800186343459276472122161 600139757594457354091621)
                  ·
                    refine ⟨112526204548960753892179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 600139757594457354091621 112526204548960753892179)
                    ·
                      rfl

theorem cell22_328716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_328716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328716 prefixEnd_328716 := by exact prefixLift 328716
  have htrace : WordTrace (prefixWord ++ tailWord_328716) baseStart_328716 baseEnd_328716 := by
    simpa [prefixWord, tailWord_328716, baseEnd_328716] using wordTrace_append hprefix tailTrace_328716
  have hstable : (prefixWord ++ tailWord_328716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328716).length < 2 ^ (prefixWord ++ tailWord_328716).sum := by decide
  have hdescent : baseEnd_328716 < baseStart_328716 := by decide
  rcases family_descends (prefixWord ++ tailWord_328716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328759 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 9]
def baseStart_328759 : Nat := 118140960795 + 328759 * 2 ^ 59
def prefixEnd_328759 : Nat := 4983230072969 + 3 ^ 40 * 328759 * 2
def baseEnd_328759 : Nat := 37513641442574325022349

theorem tailTrace_328759 : CollatzResearch.WordTrace tailWord_328759 prefixEnd_328759 37513641442574325022349 := by
  unfold tailWord_328759
  simp only [CollatzResearch.WordTrace]
  refine ⟨11990825815969765412173331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7993883877313176941448887 11990825815969765412173331)
  ·
    refine ⟨17986238723954648118259997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11990825815969765412173331 17986238723954648118259997)
    ·
      refine ⟨6744839521482993044347499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17986238723954648118259997 6744839521482993044347499)
      ·
        refine ⟨10117259282224489566521249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6744839521482993044347499 10117259282224489566521249)
        ·
          refine ⟨7587944461668367174890937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10117259282224489566521249 7587944461668367174890937)
          ·
            refine ⟨5690958346251275381168203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7587944461668367174890937 5690958346251275381168203)
            ·
              refine ⟨8536437519376913071752305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5690958346251275381168203 8536437519376913071752305)
              ·
                refine ⟨6402328139532684803814229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8536437519376913071752305 6402328139532684803814229)
                ·
                  refine ⟨37513641442574325022349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6402328139532684803814229 37513641442574325022349)
                  ·
                    rfl

theorem cell22_328759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 9].length) (baseStart_328759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328759 prefixEnd_328759 := by exact prefixLift 328759
  have htrace : WordTrace (prefixWord ++ tailWord_328759) baseStart_328759 baseEnd_328759 := by
    simpa [prefixWord, tailWord_328759, baseEnd_328759] using wordTrace_append hprefix tailTrace_328759
  have hstable : (prefixWord ++ tailWord_328759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328759).length < 2 ^ (prefixWord ++ tailWord_328759).sum := by decide
  have hdescent : baseEnd_328759 < baseStart_328759 := by decide
  rcases family_descends (prefixWord ++ tailWord_328759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328797 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_328797 : Nat := 118140960795 + 328797 * 2 ^ 59
def prefixEnd_328797 : Nat := 4983230072969 + 3 ^ 40 * 328797 * 2
def baseEnd_328797 : Nat := 112553932504303542616931

theorem tailTrace_328797 : CollatzResearch.WordTrace tailWord_328797 prefixEnd_328797 112553932504303542616931 := by
  unfold tailWord_328797
  simp only [CollatzResearch.WordTrace]
  refine ⟨11992211789832097902056645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7994807859888065268037763 11992211789832097902056645)
  ·
    refine ⟨2248539710593518356635621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11992211789832097902056645 2248539710593518356635621)
    ·
      refine ⟨421601195736284691869179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2248539710593518356635621 421601195736284691869179)
      ·
        refine ⟨632401793604427037803769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421601195736284691869179 632401793604427037803769)
        ·
          refine ⟨474301345203320278352827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632401793604427037803769 474301345203320278352827)
          ·
            refine ⟨711452017804980417529241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474301345203320278352827 711452017804980417529241)
            ·
              refine ⟨533589013353735313146931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 711452017804980417529241 533589013353735313146931)
              ·
                refine ⟨800383520030602969720397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533589013353735313146931 800383520030602969720397)
                ·
                  refine ⟨300143820011476113645149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800383520030602969720397 300143820011476113645149)
                  ·
                    refine ⟨112553932504303542616931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 300143820011476113645149 112553932504303542616931)
                    ·
                      rfl

theorem cell22_328797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_328797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328797 prefixEnd_328797 := by exact prefixLift 328797
  have htrace : WordTrace (prefixWord ++ tailWord_328797) baseStart_328797 baseEnd_328797 := by
    simpa [prefixWord, tailWord_328797, baseEnd_328797] using wordTrace_append hprefix tailTrace_328797
  have hstable : (prefixWord ++ tailWord_328797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328797).length < 2 ^ (prefixWord ++ tailWord_328797).sum := by decide
  have hdescent : baseEnd_328797 < baseStart_328797 := by decide
  rcases family_descends (prefixWord ++ tailWord_328797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328810 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 5]
def baseStart_328810 : Nat := 118140960795 + 328810 * 2 ^ 59
def prefixEnd_328810 : Nat := 4983230072969 + 3 ^ 40 * 328810 * 2
def baseEnd_328810 : Nat := 37519460889991947347297

theorem tailTrace_328810 : CollatzResearch.WordTrace tailWord_328810 prefixEnd_328810 37519460889991947347297 := by
  unfold tailWord_328810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998171484696250280569971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7995123959190000748186589 2998171484696250280569971)
  ·
    refine ⟨4497257227044375420854957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2998171484696250280569971 4497257227044375420854957)
    ·
      refine ⟨1686471460141640782820609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4497257227044375420854957 1686471460141640782820609)
      ·
        refine ⟨1264853595106230587115457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1686471460141640782820609 1264853595106230587115457)
        ·
          refine ⟨948640196329672940336593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1264853595106230587115457 948640196329672940336593)
          ·
            refine ⟨711480147247254705252445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 948640196329672940336593 711480147247254705252445)
            ·
              refine ⟨266805055217720514469667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 711480147247254705252445 266805055217720514469667)
              ·
                refine ⟨400207582826580771704501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266805055217720514469667 400207582826580771704501)
                ·
                  refine ⟨37519460889991947347297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 400207582826580771704501 37519460889991947347297)
                  ·
                    rfl

theorem cell22_328810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_328810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328810 prefixEnd_328810 := by exact prefixLift 328810
  have htrace : WordTrace (prefixWord ++ tailWord_328810) baseStart_328810 baseEnd_328810 := by
    simpa [prefixWord, tailWord_328810, baseEnd_328810] using wordTrace_append hprefix tailTrace_328810
  have hstable : (prefixWord ++ tailWord_328810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328810).length < 2 ^ (prefixWord ++ tailWord_328810).sum := by decide
  have hdescent : baseEnd_328810 < baseStart_328810 := by decide
  rcases family_descends (prefixWord ++ tailWord_328810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328823 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 1, 4]
def baseStart_328823 : Nat := 118140960795 + 328823 * 2 ^ 59
def prefixEnd_328823 : Nat := 4983230072969 + 3 ^ 40 * 328823 * 2
def baseEnd_328823 : Nat := 112562832835648141466851

theorem tailTrace_328823 : CollatzResearch.WordTrace tailWord_328823 prefixEnd_328823 112562832835648141466851 := by
  unfold tailWord_328823
  simp only [CollatzResearch.WordTrace]
  refine ⟨11993160087737904342503123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7995440058491936228335415 11993160087737904342503123)
  ·
    refine ⟨17989740131606856513754685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11993160087737904342503123 17989740131606856513754685)
    ·
      refine ⟨6746152549352571192658007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17989740131606856513754685 6746152549352571192658007)
      ·
        refine ⟨10119228824028856788987011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6746152549352571192658007 10119228824028856788987011)
        ·
          refine ⟨15178843236043285183480517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10119228824028856788987011 15178843236043285183480517)
          ·
            refine ⟨2846033106758115971902597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15178843236043285183480517 2846033106758115971902597)
            ·
              refine ⟨533631207517146744731737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2846033106758115971902597 533631207517146744731737)
              ·
                refine ⟨400223405637860058548803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533631207517146744731737 400223405637860058548803)
                ·
                  refine ⟨600335108456790087823205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400223405637860058548803 600335108456790087823205)
                  ·
                    refine ⟨112562832835648141466851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 600335108456790087823205 112562832835648141466851)
                    ·
                      rfl

theorem cell22_328823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_328823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328823 prefixEnd_328823 := by exact prefixLift 328823
  have htrace : WordTrace (prefixWord ++ tailWord_328823) baseStart_328823 baseEnd_328823 := by
    simpa [prefixWord, tailWord_328823, baseEnd_328823] using wordTrace_append hprefix tailTrace_328823
  have hstable : (prefixWord ++ tailWord_328823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328823).length < 2 ^ (prefixWord ++ tailWord_328823).sum := by decide
  have hdescent : baseEnd_328823 < baseStart_328823 := by decide
  rcases family_descends (prefixWord ++ tailWord_328823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328851 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 4, 4]
def baseStart_328851 : Nat := 118140960795 + 328851 * 2 ^ 59
def prefixEnd_328851 : Nat := 4983230072969 + 3 ^ 40 * 328851 * 2
def baseEnd_328851 : Nat := 112572417807865401766765

theorem tailTrace_328851 : CollatzResearch.WordTrace tailWord_328851 prefixEnd_328851 112572417807865401766765 := by
  unfold tailWord_328851
  simp only [CollatzResearch.WordTrace]
  refine ⟨11994181331636465124522407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7996120887757643416348271 11994181331636465124522407)
  ·
    refine ⟨17991271997454697686783611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11994181331636465124522407 17991271997454697686783611)
    ·
      refine ⟨26986907996182046530175417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17991271997454697686783611 26986907996182046530175417)
      ·
        refine ⟨20240180997136534897631563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26986907996182046530175417 20240180997136534897631563)
        ·
          refine ⟨30360271495704802346447345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20240180997136534897631563 30360271495704802346447345)
          ·
            refine ⟨22770203621778601759835509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30360271495704802346447345 22770203621778601759835509)
            ·
              refine ⟨2134706589541743914984579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22770203621778601759835509 2134706589541743914984579)
              ·
                refine ⟨3202059884312615872476869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134706589541743914984579 3202059884312615872476869)
                ·
                  refine ⟨600386228308615476089413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3202059884312615872476869 600386228308615476089413)
                  ·
                    refine ⟨112572417807865401766765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 600386228308615476089413 112572417807865401766765)
                    ·
                      rfl

theorem cell22_328851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 4].length) (baseStart_328851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328851 prefixEnd_328851 := by exact prefixLift 328851
  have htrace : WordTrace (prefixWord ++ tailWord_328851) baseStart_328851 baseEnd_328851 := by
    simpa [prefixWord, tailWord_328851, baseEnd_328851] using wordTrace_append hprefix tailTrace_328851
  have hstable : (prefixWord ++ tailWord_328851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328851).length < 2 ^ (prefixWord ++ tailWord_328851).sum := by decide
  have hdescent : baseEnd_328851 < baseStart_328851 := by decide
  rcases family_descends (prefixWord ++ tailWord_328851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328915 : List Nat := [1, 1, 1, 2, 1, 1, 1, 10, 1, 3]
def baseStart_328915 : Nat := 118140960795 + 328915 * 2 ^ 59
def prefixEnd_328915 : Nat := 4983230072969 + 3 ^ 40 * 328915 * 2
def baseEnd_328915 : Nat := 112594326315790568166569

theorem tailTrace_328915 : CollatzResearch.WordTrace tailWord_328915 prefixEnd_328915 112594326315790568166569 := by
  unfold tailWord_328915
  simp only [CollatzResearch.WordTrace]
  refine ⟨11996515603404604054852199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7997677068936402703234799 11996515603404604054852199)
  ·
    refine ⟨17994773405106906082278299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11996515603404604054852199 17994773405106906082278299)
    ·
      refine ⟨26992160107660359123417449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17994773405106906082278299 26992160107660359123417449)
      ·
        refine ⟨20244120080745269342563087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26992160107660359123417449 20244120080745269342563087)
        ·
          refine ⟨30366180121117904013844631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20244120080745269342563087 30366180121117904013844631)
          ·
            refine ⟨45549270181676856020766947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30366180121117904013844631 45549270181676856020766947)
            ·
              refine ⟨68323905272515284031150421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45549270181676856020766947 68323905272515284031150421)
              ·
                refine ⟨200167691228072121185011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 68323905272515284031150421 200167691228072121185011)
                ·
                  refine ⟨300251536842108181777517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200167691228072121185011 300251536842108181777517)
                  ·
                    refine ⟨112594326315790568166569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 300251536842108181777517 112594326315790568166569)
                    ·
                      rfl

theorem cell22_328915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 1, 3].length) (baseStart_328915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328915 prefixEnd_328915 := by exact prefixLift 328915
  have htrace : WordTrace (prefixWord ++ tailWord_328915) baseStart_328915 baseEnd_328915 := by
    simpa [prefixWord, tailWord_328915, baseEnd_328915] using wordTrace_append hprefix tailTrace_328915
  have hstable : (prefixWord ++ tailWord_328915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328915).length < 2 ^ (prefixWord ++ tailWord_328915).sum := by decide
  have hdescent : baseEnd_328915 < baseStart_328915 := by decide
  rcases family_descends (prefixWord ++ tailWord_328915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328928 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 5]
def baseStart_328928 : Nat := 118140960795 + 328928 * 2 ^ 59
def prefixEnd_328928 : Nat := 4983230072969 + 3 ^ 40 * 328928 * 2
def baseEnd_328928 : Nat := 37532925493820955863843

theorem tailTrace_328928 : CollatzResearch.WordTrace tailWord_328928 prefixEnd_328928 37532925493820955863843 := by
  unfold tailWord_328928
  simp only [CollatzResearch.WordTrace]
  refine ⟨5998494876178753637537719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7997993168238338183383625 5998494876178753637537719)
  ·
    refine ⟨8997742314268130456306579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5998494876178753637537719 8997742314268130456306579)
    ·
      refine ⟨13496613471402195684459869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8997742314268130456306579 13496613471402195684459869)
      ·
        refine ⟨5061230051775823381672451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13496613471402195684459869 5061230051775823381672451)
        ·
          refine ⟨7591845077663735072508677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061230051775823381672451 7591845077663735072508677)
          ·
            refine ⟨1423470952061950326095377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7591845077663735072508677 1423470952061950326095377)
            ·
              refine ⟨1067603214046462744571533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1423470952061950326095377 1067603214046462744571533)
              ·
                refine ⟨400351205267423529214325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1067603214046462744571533 400351205267423529214325)
                ·
                  refine ⟨37532925493820955863843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 400351205267423529214325 37532925493820955863843)
                  ·
                    rfl

theorem cell22_328928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_328928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328928 prefixEnd_328928 := by exact prefixLift 328928
  have htrace : WordTrace (prefixWord ++ tailWord_328928) baseStart_328928 baseEnd_328928 := by
    simpa [prefixWord, tailWord_328928, baseEnd_328928] using wordTrace_append hprefix tailTrace_328928
  have hstable : (prefixWord ++ tailWord_328928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328928).length < 2 ^ (prefixWord ++ tailWord_328928).sum := by decide
  have hdescent : baseEnd_328928 < baseStart_328928 := by decide
  rcases family_descends (prefixWord ++ tailWord_328928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328992 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 1, 4]
def baseStart_328992 : Nat := 118140960795 + 328992 * 2 ^ 59
def prefixEnd_328992 : Nat := 4983230072969 + 3 ^ 40 * 328992 * 2
def baseEnd_328992 : Nat := 112620684989388033991333

theorem tailTrace_328992 : CollatzResearch.WordTrace tailWord_328992 prefixEnd_328992 112620684989388033991333 := by
  unfold tailWord_328992
  simp only [CollatzResearch.WordTrace]
  refine ⟨5999662012062823102702615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7999549349417097470270153 5999662012062823102702615)
  ·
    refine ⟨8999493018094234654053923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5999662012062823102702615 8999493018094234654053923)
    ·
      refine ⟨13499239527141351981080885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8999493018094234654053923 13499239527141351981080885)
      ·
        refine ⟨1265553705669501748226333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13499239527141351981080885 1265553705669501748226333)
        ·
          refine ⟨474582639626063155584875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1265553705669501748226333 474582639626063155584875)
          ·
            refine ⟨711873959439094733377313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474582639626063155584875 711873959439094733377313)
            ·
              refine ⟨533905469579321050032985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 711873959439094733377313 533905469579321050032985)
              ·
                refine ⟨400429102184490787524739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533905469579321050032985 400429102184490787524739)
                ·
                  refine ⟨600643653276736181287109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400429102184490787524739 600643653276736181287109)
                  ·
                    refine ⟨112620684989388033991333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 600643653276736181287109 112620684989388033991333)
                    ·
                      rfl

theorem cell22_328992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_328992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_328992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_328992 prefixEnd_328992 := by exact prefixLift 328992
  have htrace : WordTrace (prefixWord ++ tailWord_328992) baseStart_328992 baseEnd_328992 := by
    simpa [prefixWord, tailWord_328992, baseEnd_328992] using wordTrace_append hprefix tailTrace_328992
  have hstable : (prefixWord ++ tailWord_328992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328992).length < 2 ^ (prefixWord ++ tailWord_328992).sum := by decide
  have hdescent : baseEnd_328992 < baseStart_328992 := by decide
  rcases family_descends (prefixWord ++ tailWord_328992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329020 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_329020 : Nat := 118140960795 + 329020 * 2 ^ 59
def prefixEnd_329020 : Nat := 4983230072969 + 3 ^ 40 * 329020 * 2
def baseEnd_329020 : Nat := 112630269961605294291247

theorem tailTrace_329020 : CollatzResearch.WordTrace tailWord_329020 prefixEnd_329020 112630269961605294291247 := by
  unfold tailWord_329020
  simp only [CollatzResearch.WordTrace]
  refine ⟨6000172634012103493712257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8000230178682804658283009 6000172634012103493712257)
  ·
    refine ⟨4500129475509077620284193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6000172634012103493712257 4500129475509077620284193)
    ·
      refine ⟨3375097106631808215213145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4500129475509077620284193 3375097106631808215213145)
      ·
        refine ⟨2531322829973856161409859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3375097106631808215213145 2531322829973856161409859)
        ·
          refine ⟨3796984244960784242114789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2531322829973856161409859 3796984244960784242114789)
          ·
            refine ⟨711934545930147045396523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3796984244960784242114789 711934545930147045396523)
            ·
              refine ⟨1067901818895220568094785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711934545930147045396523 1067901818895220568094785)
              ·
                refine ⟨800926364171415426071089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067901818895220568094785 800926364171415426071089)
                ·
                  refine ⟨600694773128561569553317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 800926364171415426071089 600694773128561569553317)
                  ·
                    refine ⟨112630269961605294291247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 600694773128561569553317 112630269961605294291247)
                    ·
                      rfl

theorem cell22_329020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_329020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329020 prefixEnd_329020 := by exact prefixLift 329020
  have htrace : WordTrace (prefixWord ++ tailWord_329020) baseStart_329020 baseEnd_329020 := by
    simpa [prefixWord, tailWord_329020, baseEnd_329020] using wordTrace_append hprefix tailTrace_329020
  have hstable : (prefixWord ++ tailWord_329020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329020).length < 2 ^ (prefixWord ++ tailWord_329020).sum := by decide
  have hdescent : baseEnd_329020 < baseStart_329020 := by decide
  rcases family_descends (prefixWord ++ tailWord_329020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329022 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_329022 : Nat := 118140960795 + 329022 * 2 ^ 59
def prefixEnd_329022 : Nat := 4983230072969 + 3 ^ 40 * 329022 * 2
def baseEnd_329022 : Nat := 112630954602477955741241

theorem tailTrace_329022 : CollatzResearch.WordTrace tailWord_329022 prefixEnd_329022 112630954602477955741241 := by
  unfold tailWord_329022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500052276752120166124665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8000278809344640885998213 1500052276752120166124665)
  ·
    refine ⟨1125039207564090124593499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1500052276752120166124665 1125039207564090124593499)
    ·
      refine ⟨1687558811346135186890249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125039207564090124593499 1687558811346135186890249)
      ·
        refine ⟨1265669108509601390167687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1687558811346135186890249 1265669108509601390167687)
        ·
          refine ⟨1898503662764402085251531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265669108509601390167687 1898503662764402085251531)
          ·
            refine ⟨2847755494146603127877297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898503662764402085251531 2847755494146603127877297)
            ·
              refine ⟨2135816620609952345907973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2847755494146603127877297 2135816620609952345907973)
              ·
                refine ⟨400465616364366064857745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2135816620609952345907973 400465616364366064857745)
                ·
                  refine ⟨300349212273274548643309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400465616364366064857745 300349212273274548643309)
                  ·
                    refine ⟨112630954602477955741241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 300349212273274548643309 112630954602477955741241)
                    ·
                      rfl

theorem cell22_329022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_329022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329022 prefixEnd_329022 := by exact prefixLift 329022
  have htrace : WordTrace (prefixWord ++ tailWord_329022) baseStart_329022 baseEnd_329022 := by
    simpa [prefixWord, tailWord_329022, baseEnd_329022] using wordTrace_append hprefix tailTrace_329022
  have hstable : (prefixWord ++ tailWord_329022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329022).length < 2 ^ (prefixWord ++ tailWord_329022).sum := by decide
  have hdescent : baseEnd_329022 < baseStart_329022 := by decide
  rcases family_descends (prefixWord ++ tailWord_329022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329050 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 3, 3]
def baseStart_329050 : Nat := 118140960795 + 329050 * 2 ^ 59
def prefixEnd_329050 : Nat := 4983230072969 + 3 ^ 40 * 329050 * 2
def baseEnd_329050 : Nat := 112640539574695216041155

theorem tailTrace_329050 : CollatzResearch.WordTrace tailWord_329050 prefixEnd_329050 112640539574695216041155 := by
  unfold tailWord_329050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3000359864478880527754151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8000959638610348074011069 3000359864478880527754151)
  ·
    refine ⟨4500539796718320791631227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3000359864478880527754151 4500539796718320791631227)
    ·
      refine ⟨6750809695077481187446841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4500539796718320791631227 6750809695077481187446841)
      ·
        refine ⟨5063107271308110890585131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6750809695077481187446841 5063107271308110890585131)
        ·
          refine ⟨7594660906962166335877697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5063107271308110890585131 7594660906962166335877697)
          ·
            refine ⟨5695995680221624751908273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7594660906962166335877697 5695995680221624751908273)
            ·
              refine ⟨4271996760166218563931205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5695995680221624751908273 4271996760166218563931205)
              ·
                refine ⟨800999392531165980737101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4271996760166218563931205 800999392531165980737101)
                ·
                  refine ⟨300374772199187242776413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800999392531165980737101 300374772199187242776413)
                  ·
                    refine ⟨112640539574695216041155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 300374772199187242776413 112640539574695216041155)
                    ·
                      rfl

theorem cell22_329050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_329050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329050 prefixEnd_329050 := by exact prefixLift 329050
  have htrace : WordTrace (prefixWord ++ tailWord_329050) baseStart_329050 baseEnd_329050 := by
    simpa [prefixWord, tailWord_329050, baseEnd_329050] using wordTrace_append hprefix tailTrace_329050
  have hstable : (prefixWord ++ tailWord_329050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329050).length < 2 ^ (prefixWord ++ tailWord_329050).sum := by decide
  have hdescent : baseEnd_329050 < baseStart_329050 := by decide
  rcases family_descends (prefixWord ++ tailWord_329050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329086 : List Nat := [4, 2, 3, 2, 2, 1, 1, 7]
def baseStart_329086 : Nat := 118140960795 + 329086 * 2 ^ 59
def prefixEnd_329086 : Nat := 4983230072969 + 3 ^ 40 * 329086 * 2
def baseEnd_329086 : Nat := 12516984790044791349005

theorem tailTrace_329086 : CollatzResearch.WordTrace tailWord_329086 prefixEnd_329086 12516984790044791349005 := by
  unfold tailWord_329086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500344060723137532415889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8001834990523400172884741 1500344060723137532415889)
  ·
    refine ⟨1125258045542353149311917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1500344060723137532415889 1125258045542353149311917)
    ·
      refine ⟨421971767078382430991969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1125258045542353149311917 421971767078382430991969)
      ·
        refine ⟨316478825308786823243977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421971767078382430991969 316478825308786823243977)
        ·
          refine ⟨237359118981590117432983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316478825308786823243977 237359118981590117432983)
          ·
            refine ⟨356038678472385176149475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237359118981590117432983 356038678472385176149475)
            ·
              refine ⟨534058017708577764224213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356038678472385176149475 534058017708577764224213)
              ·
                refine ⟨12516984790044791349005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 534058017708577764224213 12516984790044791349005)
                ·
                  rfl

theorem cell22_329086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_329086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329086 prefixEnd_329086 := by exact prefixLift 329086
  have htrace : WordTrace (prefixWord ++ tailWord_329086) baseStart_329086 baseEnd_329086 := by
    simpa [prefixWord, tailWord_329086, baseEnd_329086] using wordTrace_append hprefix tailTrace_329086
  have hstable : (prefixWord ++ tailWord_329086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329086).length < 2 ^ (prefixWord ++ tailWord_329086).sum := by decide
  have hdescent : baseEnd_329086 < baseStart_329086 := by decide
  rcases family_descends (prefixWord ++ tailWord_329086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329095 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 2, 5]
def baseStart_329095 : Nat := 118140960795 + 329095 * 2 ^ 59
def prefixEnd_329095 : Nat := 4983230072969 + 3 ^ 40 * 329095 * 2
def baseEnd_329095 : Nat := 112655943994330098666017

theorem tailTrace_329095 : CollatzResearch.WordTrace tailWord_329095 prefixEnd_329095 112655943994330098666017 := by
  unfold tailWord_329095
  simp only [CollatzResearch.WordTrace]
  refine ⟨12003080742752494796404739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8002053828501663197603159 12003080742752494796404739)
  ·
    refine ⟨18004621114128742194607109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12003080742752494796404739 18004621114128742194607109)
    ·
      refine ⟨3375866458899139161488833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18004621114128742194607109 3375866458899139161488833)
      ·
        refine ⟨2531899844174354371116625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3375866458899139161488833 2531899844174354371116625)
        ·
          refine ⟨1898924883130765778337469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2531899844174354371116625 1898924883130765778337469)
          ·
            refine ⟨712096831174037166876551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1898924883130765778337469 712096831174037166876551)
            ·
              refine ⟨1068145246761055750314827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712096831174037166876551 1068145246761055750314827)
              ·
                refine ⟨1602217870141583625472241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1068145246761055750314827 1602217870141583625472241)
                ·
                  refine ⟨1201663402606187719104181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1602217870141583625472241 1201663402606187719104181)
                  ·
                    refine ⟨112655943994330098666017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1201663402606187719104181 112655943994330098666017)
                    ·
                      rfl

theorem cell22_329095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_329095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329095 prefixEnd_329095 := by exact prefixLift 329095
  have htrace : WordTrace (prefixWord ++ tailWord_329095) baseStart_329095 baseEnd_329095 := by
    simpa [prefixWord, tailWord_329095, baseEnd_329095] using wordTrace_append hprefix tailTrace_329095
  have hstable : (prefixWord ++ tailWord_329095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329095).length < 2 ^ (prefixWord ++ tailWord_329095).sum := by decide
  have hdescent : baseEnd_329095 < baseStart_329095 := by decide
  rcases family_descends (prefixWord ++ tailWord_329095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329118 : List Nat := [4, 3, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_329118 : Nat := 118140960795 + 329118 * 2 ^ 59
def prefixEnd_329118 : Nat := 4983230072969 + 3 ^ 40 * 329118 * 2
def baseEnd_329118 : Nat := 112663817364365705340947

theorem tailTrace_329118 : CollatzResearch.WordTrace tailWord_329118 prefixEnd_329118 112663817364365705340947 := by
  unfold tailWord_329118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500489952708646215561501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8002613081112779816328005 1500489952708646215561501)
  ·
    refine ⟨562683732265742330835563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1500489952708646215561501 562683732265742330835563)
    ·
      refine ⟨844025598398613496253345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 562683732265742330835563 844025598398613496253345)
      ·
        refine ⟨633019198798960122190009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 844025598398613496253345 633019198798960122190009)
        ·
          refine ⟨474764399099220091642507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633019198798960122190009 474764399099220091642507)
          ·
            refine ⟨712146598648830137463761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474764399099220091642507 712146598648830137463761)
            ·
              refine ⟨534109948986622603097821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712146598648830137463761 534109948986622603097821)
              ·
                refine ⟨200291230869983476161683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 534109948986622603097821 200291230869983476161683)
                ·
                  refine ⟨300436846304975214242525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200291230869983476161683 300436846304975214242525)
                  ·
                    refine ⟨112663817364365705340947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 300436846304975214242525 112663817364365705340947)
                    ·
                      rfl

theorem cell22_329118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_329118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329118 prefixEnd_329118 := by exact prefixLift 329118
  have htrace : WordTrace (prefixWord ++ tailWord_329118) baseStart_329118 baseEnd_329118 := by
    simpa [prefixWord, tailWord_329118, baseEnd_329118] using wordTrace_append hprefix tailTrace_329118
  have hstable : (prefixWord ++ tailWord_329118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329118).length < 2 ^ (prefixWord ++ tailWord_329118).sum := by decide
  have hdescent : baseEnd_329118 < baseStart_329118 := by decide
  rcases family_descends (prefixWord ++ tailWord_329118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329127 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 1, 4]
def baseStart_329127 : Nat := 118140960795 + 329127 * 2 ^ 59
def prefixEnd_329127 : Nat := 4983230072969 + 3 ^ 40 * 329127 * 2
def baseEnd_329127 : Nat := 112666898248292681865919

theorem tailTrace_329127 : CollatzResearch.WordTrace tailWord_329127 prefixEnd_329127 112666898248292681865919 := by
  unfold tailWord_329127
  simp only [CollatzResearch.WordTrace]
  refine ⟨12004247878636564261569635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8002831919091042841046423 12004247878636564261569635)
  ·
    refine ⟨18006371817954846392354453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12004247878636564261569635 18006371817954846392354453)
    ·
      refine ⟨844048678966633424641615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18006371817954846392354453 844048678966633424641615)
      ·
        refine ⟨1266073018449950136962423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844048678966633424641615 1266073018449950136962423)
        ·
          refine ⟨1899109527674925205443635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266073018449950136962423 1899109527674925205443635)
          ·
            refine ⟨2848664291512387808165453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899109527674925205443635 2848664291512387808165453)
            ·
              refine ⟨1068249109317145428062045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2848664291512387808165453 1068249109317145428062045)
              ·
                refine ⟨400593415993929535523267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1068249109317145428062045 400593415993929535523267)
                ·
                  refine ⟨600890123990894303284901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400593415993929535523267 600890123990894303284901)
                  ·
                    refine ⟨112666898248292681865919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 600890123990894303284901 112666898248292681865919)
                    ·
                      rfl

theorem cell22_329127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_329127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329127 prefixEnd_329127 := by exact prefixLift 329127
  have htrace : WordTrace (prefixWord ++ tailWord_329127) baseStart_329127 baseEnd_329127 := by
    simpa [prefixWord, tailWord_329127, baseEnd_329127] using wordTrace_append hprefix tailTrace_329127
  have hstable : (prefixWord ++ tailWord_329127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329127).length < 2 ^ (prefixWord ++ tailWord_329127).sum := by decide
  have hdescent : baseEnd_329127 < baseStart_329127 := by decide
  rcases family_descends (prefixWord ++ tailWord_329127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329174 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_329174 : Nat := 118140960795 + 329174 * 2 ^ 59
def prefixEnd_329174 : Nat := 4983230072969 + 3 ^ 40 * 329174 * 2
def baseEnd_329174 : Nat := 112682987308800225940775

theorem tailTrace_329174 : CollatzResearch.WordTrace tailWord_329174 prefixEnd_329174 112682987308800225940775 := by
  unfold tailWord_329174
  simp only [CollatzResearch.WordTrace]
  refine ⟨750372631841643205533161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8003974739644194192353717 750372631841643205533161)
  ·
    refine ⟨562779473881232404149871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 750372631841643205533161 562779473881232404149871)
    ·
      refine ⟨844169210821848606224807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 562779473881232404149871 844169210821848606224807)
      ·
        refine ⟨1266253816232772909337211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844169210821848606224807 1266253816232772909337211)
        ·
          refine ⟨1899380724349159364005817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266253816232772909337211 1899380724349159364005817)
          ·
            refine ⟨1424535543261869523004363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1899380724349159364005817 1424535543261869523004363)
            ·
              refine ⟨2136803314892804284506545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424535543261869523004363 2136803314892804284506545)
              ·
                refine ⟨1602602486169603213379909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2136803314892804284506545 1602602486169603213379909)
                ·
                  refine ⟨300487966156800602508733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1602602486169603213379909 300487966156800602508733)
                  ·
                    refine ⟨112682987308800225940775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 300487966156800602508733 112682987308800225940775)
                    ·
                      rfl

theorem cell22_329174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_329174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329174 prefixEnd_329174 := by exact prefixLift 329174
  have htrace : WordTrace (prefixWord ++ tailWord_329174) baseStart_329174 baseEnd_329174 := by
    simpa [prefixWord, tailWord_329174, baseEnd_329174] using wordTrace_append hprefix tailTrace_329174
  have hstable : (prefixWord ++ tailWord_329174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329174).length < 2 ^ (prefixWord ++ tailWord_329174).sum := by decide
  have hdescent : baseEnd_329174 < baseStart_329174 := by decide
  rcases family_descends (prefixWord ++ tailWord_329174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329292 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_329292 : Nat := 118140960795 + 329292 * 2 ^ 59
def prefixEnd_329292 : Nat := 4983230072969 + 3 ^ 40 * 329292 * 2
def baseEnd_329292 : Nat := 112723381120287251490413

theorem tailTrace_329292 : CollatzResearch.WordTrace tailWord_329292 prefixEnd_329292 112723381120287251490413 := by
  unfold tailWord_329292
  simp only [CollatzResearch.WordTrace]
  refine ⟨6005132961519398720663065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8006843948692531627550753 6005132961519398720663065)
  ·
    refine ⟨4503849721139549040497299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6005132961519398720663065 4503849721139549040497299)
    ·
      refine ⟨6755774581709323560745949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4503849721139549040497299 6755774581709323560745949)
      ·
        refine ⟨2533415468140996335279731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6755774581709323560745949 2533415468140996335279731)
        ·
          refine ⟨3800123202211494502919597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533415468140996335279731 3800123202211494502919597)
          ·
            refine ⟨1425046200829310438594849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3800123202211494502919597 1425046200829310438594849)
            ·
              refine ⟨1068784650621982828946137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1425046200829310438594849 1068784650621982828946137)
              ·
                refine ⟨801588487966487121709603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068784650621982828946137 801588487966487121709603)
                ·
                  refine ⟨1202382731949730682564405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801588487966487121709603 1202382731949730682564405)
                  ·
                    refine ⟨112723381120287251490413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1202382731949730682564405 112723381120287251490413)
                    ·
                      rfl

theorem cell22_329292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_329292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329292 prefixEnd_329292 := by exact prefixLift 329292
  have htrace : WordTrace (prefixWord ++ tailWord_329292) baseStart_329292 baseEnd_329292 := by
    simpa [prefixWord, tailWord_329292, baseEnd_329292] using wordTrace_append hprefix tailTrace_329292
  have hstable : (prefixWord ++ tailWord_329292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329292).length < 2 ^ (prefixWord ++ tailWord_329292).sum := by decide
  have hdescent : baseEnd_329292 < baseStart_329292 := by decide
  rcases family_descends (prefixWord ++ tailWord_329292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329326 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_329326 : Nat := 118140960795 + 329326 * 2 ^ 59
def prefixEnd_329326 : Nat := 4983230072969 + 3 ^ 40 * 329326 * 2
def baseEnd_329326 : Nat := 112735020015122496140309

theorem tailTrace_329326 : CollatzResearch.WordTrace tailWord_329326 prefixEnd_329326 112735020015122496140309 := by
  unfold tailWord_329326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501438250614452656007979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8007670669943747498709221 1501438250614452656007979)
  ·
    refine ⟨2252157375921678984011969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1501438250614452656007979 2252157375921678984011969)
    ·
      refine ⟨1689118031941259238008977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2252157375921678984011969 1689118031941259238008977)
      ·
        refine ⟨1266838523955944428506733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1689118031941259238008977 1266838523955944428506733)
        ·
          refine ⟨475064446483479160690025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1266838523955944428506733 475064446483479160690025)
          ·
            refine ⟨356298334862609370517519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475064446483479160690025 356298334862609370517519)
            ·
              refine ⟨534447502293914055776279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356298334862609370517519 534447502293914055776279)
              ·
                refine ⟨801671253440871083664419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534447502293914055776279 801671253440871083664419)
                ·
                  refine ⟨1202506880161306625496629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801671253440871083664419 1202506880161306625496629)
                  ·
                    refine ⟨112735020015122496140309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1202506880161306625496629 112735020015122496140309)
                    ·
                      rfl

theorem cell22_329326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_329326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329326 prefixEnd_329326 := by exact prefixLift 329326
  have htrace : WordTrace (prefixWord ++ tailWord_329326) baseStart_329326 baseEnd_329326 := by
    simpa [prefixWord, tailWord_329326, baseEnd_329326] using wordTrace_append hprefix tailTrace_329326
  have hstable : (prefixWord ++ tailWord_329326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329326).length < 2 ^ (prefixWord ++ tailWord_329326).sum := by decide
  have hdescent : baseEnd_329326 < baseStart_329326 := by decide
  rcases family_descends (prefixWord ++ tailWord_329326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329367 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 7]
def baseStart_329367 : Nat := 118140960795 + 329367 * 2 ^ 59
def prefixEnd_329367 : Nat := 4983230072969 + 3 ^ 40 * 329367 * 2
def baseEnd_329367 : Nat := 37583018384337351955061

theorem tailTrace_329367 : CollatzResearch.WordTrace tailWord_329367 prefixEnd_329367 37583018384337351955061 := by
  unfold tailWord_329367
  simp only [CollatzResearch.WordTrace]
  refine ⟨12013001397767085250306355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8008667598511390166870903 12013001397767085250306355)
  ·
    refine ⟨18019502096650627875459533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12013001397767085250306355 18019502096650627875459533)
    ·
      refine ⟨6757313286243985453297325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18019502096650627875459533 6757313286243985453297325)
      ·
        refine ⟨2533992482341494544986497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6757313286243985453297325 2533992482341494544986497)
        ·
          refine ⟨1900494361756120908739873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2533992482341494544986497 1900494361756120908739873)
          ·
            refine ⟨1425370771317090681554905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1900494361756120908739873 1425370771317090681554905)
            ·
              refine ⟨1069028078487818011166179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1425370771317090681554905 1069028078487818011166179)
              ·
                refine ⟨1603542117731727016749269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069028078487818011166179 1603542117731727016749269)
                ·
                  refine ⟨37583018384337351955061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1603542117731727016749269 37583018384337351955061)
                  ·
                    rfl

theorem cell22_329367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 7].length) (baseStart_329367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329367 prefixEnd_329367 := by exact prefixLift 329367
  have htrace : WordTrace (prefixWord ++ tailWord_329367) baseStart_329367 baseEnd_329367 := by
    simpa [prefixWord, tailWord_329367, baseEnd_329367] using wordTrace_append hprefix tailTrace_329367
  have hstable : (prefixWord ++ tailWord_329367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329367).length < 2 ^ (prefixWord ++ tailWord_329367).sum := by decide
  have hdescent : baseEnd_329367 < baseStart_329367 := by decide
  rcases family_descends (prefixWord ++ tailWord_329367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329444 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_329444 : Nat := 118140960795 + 329444 * 2 ^ 59
def prefixEnd_329444 : Nat := 4983230072969 + 3 ^ 40 * 329444 * 2
def baseEnd_329444 : Nat := 112775413826609521689947

theorem tailTrace_329444 : CollatzResearch.WordTrace tailWord_329444 prefixEnd_329444 112775413826609521689947 := by
  unfold tailWord_329444
  simp only [CollatzResearch.WordTrace]
  refine ⟨6007904909244063700429693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8010539878992084933906257 6007904909244063700429693)
  ·
    refine ⟨2252964340966523887661135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6007904909244063700429693 2252964340966523887661135)
    ·
      refine ⟨3379446511449785831491703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2252964340966523887661135 3379446511449785831491703)
      ·
        refine ⟨5069169767174678747237555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3379446511449785831491703 5069169767174678747237555)
        ·
          refine ⟨7603754650762018120856333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5069169767174678747237555 7603754650762018120856333)
          ·
            refine ⟨2851407994035756795321125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7603754650762018120856333 2851407994035756795321125)
            ·
              refine ⟨534638998881704399122711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2851407994035756795321125 534638998881704399122711)
              ·
                refine ⟨801958498322556598684067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534638998881704399122711 801958498322556598684067)
                ·
                  refine ⟨1202937747483834898026101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801958498322556598684067 1202937747483834898026101)
                  ·
                    refine ⟨112775413826609521689947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1202937747483834898026101 112775413826609521689947)
                    ·
                      rfl

theorem cell22_329444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_329444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329444 prefixEnd_329444 := by exact prefixLift 329444
  have htrace : WordTrace (prefixWord ++ tailWord_329444) baseStart_329444 baseEnd_329444 := by
    simpa [prefixWord, tailWord_329444, baseEnd_329444] using wordTrace_append hprefix tailTrace_329444
  have hstable : (prefixWord ++ tailWord_329444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329444).length < 2 ^ (prefixWord ++ tailWord_329444).sum := by decide
  have hdescent : baseEnd_329444 < baseStart_329444 := by decide
  rcases family_descends (prefixWord ++ tailWord_329444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329459 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 2, 4]
def baseStart_329459 : Nat := 118140960795 + 329459 * 2 ^ 59
def prefixEnd_329459 : Nat := 4983230072969 + 3 ^ 40 * 329459 * 2
def baseEnd_329459 : Nat := 112780548633154482564901

theorem tailTrace_329459 : CollatzResearch.WordTrace tailWord_329459 prefixEnd_329459 112780548633154482564901 := by
  unfold tailWord_329459
  simp only [CollatzResearch.WordTrace]
  refine ⟨12016356913433784962655431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8010904608955856641770287 12016356913433784962655431)
  ·
    refine ⟨18024535370150677443983147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12016356913433784962655431 18024535370150677443983147)
    ·
      refine ⟨27036803055226016165974721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18024535370150677443983147 27036803055226016165974721)
      ·
        refine ⟨20277602291419512124481041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27036803055226016165974721 20277602291419512124481041)
        ·
          refine ⟨15208201718564634093360781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20277602291419512124481041 15208201718564634093360781)
          ·
            refine ⟨5703075644461737785010293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15208201718564634093360781 5703075644461737785010293)
            ·
              refine ⟨534663341668287917344715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5703075644461737785010293 534663341668287917344715)
              ·
                refine ⟨801995012502431876017073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534663341668287917344715 801995012502431876017073)
                ·
                  refine ⟨601496259376823907012805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 801995012502431876017073 601496259376823907012805)
                  ·
                    refine ⟨112780548633154482564901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 601496259376823907012805 112780548633154482564901)
                    ·
                      rfl

theorem cell22_329459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 4].length) (baseStart_329459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329459 prefixEnd_329459 := by exact prefixLift 329459
  have htrace : WordTrace (prefixWord ++ tailWord_329459) baseStart_329459 baseEnd_329459 := by
    simpa [prefixWord, tailWord_329459, baseEnd_329459] using wordTrace_append hprefix tailTrace_329459
  have hstable : (prefixWord ++ tailWord_329459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329459).length < 2 ^ (prefixWord ++ tailWord_329459).sum := by decide
  have hdescent : baseEnd_329459 < baseStart_329459 := by decide
  rcases family_descends (prefixWord ++ tailWord_329459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329474 : List Nat := [3, 4, 1, 1, 1, 1, 11]
def baseStart_329474 : Nat := 118140960795 + 329474 * 2 ^ 59
def prefixEnd_329474 : Nat := 4983230072969 + 3 ^ 40 * 329474 * 2
def baseEnd_329474 : Nat := 4177247534803683090365

theorem tailTrace_329474 : CollatzResearch.WordTrace tailWord_329474 prefixEnd_329474 4177247534803683090365 := by
  unfold tailWord_329474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3004226002094860631112869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8011269338919628349634317 3004226002094860631112869)
  ·
    refine ⟨563292375392786368333663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3004226002094860631112869 563292375392786368333663)
    ·
      refine ⟨844938563089179552500495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563292375392786368333663 844938563089179552500495)
      ·
        refine ⟨1267407844633769328750743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844938563089179552500495 1267407844633769328750743)
        ·
          refine ⟨1901111766950653993126115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1267407844633769328750743 1901111766950653993126115)
          ·
            refine ⟨2851667650425980989689173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901111766950653993126115 2851667650425980989689173)
            ·
              refine ⟨4177247534803683090365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2851667650425980989689173 4177247534803683090365)
              ·
                rfl

theorem cell22_329474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 11].length) (baseStart_329474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329474 prefixEnd_329474 := by exact prefixLift 329474
  have htrace : WordTrace (prefixWord ++ tailWord_329474) baseStart_329474 baseEnd_329474 := by
    simpa [prefixWord, tailWord_329474, baseEnd_329474] using wordTrace_append hprefix tailTrace_329474
  have hstable : (prefixWord ++ tailWord_329474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329474).length < 2 ^ (prefixWord ++ tailWord_329474).sum := by decide
  have hdescent : baseEnd_329474 < baseStart_329474 := by decide
  rcases family_descends (prefixWord ++ tailWord_329474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329487 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 2, 6]
def baseStart_329487 : Nat := 118140960795 + 329487 * 2 ^ 59
def prefixEnd_329487 : Nat := 4983230072969 + 3 ^ 40 * 329487 * 2
def baseEnd_329487 : Nat := 112790133605371742864815

theorem tailTrace_329487 : CollatzResearch.WordTrace tailWord_329487 prefixEnd_329487 112790133605371742864815 := by
  unfold tailWord_329487
  simp only [CollatzResearch.WordTrace]
  refine ⟨12017378157332345744674715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8011585438221563829783143 12017378157332345744674715)
  ·
    refine ⟨18026067235998518617012073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12017378157332345744674715 18026067235998518617012073)
    ·
      refine ⟨13519550426998888962759055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18026067235998518617012073 13519550426998888962759055)
      ·
        refine ⟨20279325640498333444138583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13519550426998888962759055 20279325640498333444138583)
        ·
          refine ⟨30418988460747500166207875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20279325640498333444138583 30418988460747500166207875)
          ·
            refine ⟨45628482691121250249311813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30418988460747500166207875 45628482691121250249311813)
            ·
              refine ⟨8555340504585234421745965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45628482691121250249311813 8555340504585234421745965)
              ·
                refine ⟨3208252689219462908154737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8555340504585234421745965 3208252689219462908154737)
                ·
                  refine ⟨2406189516914597181116053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3208252689219462908154737 2406189516914597181116053)
                  ·
                    refine ⟨112790133605371742864815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2406189516914597181116053 112790133605371742864815)
                    ·
                      rfl

theorem cell22_329487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_329487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329487 prefixEnd_329487 := by exact prefixLift 329487
  have htrace : WordTrace (prefixWord ++ tailWord_329487) baseStart_329487 baseEnd_329487 := by
    simpa [prefixWord, tailWord_329487, baseEnd_329487] using wordTrace_append hprefix tailTrace_329487
  have hstable : (prefixWord ++ tailWord_329487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329487).length < 2 ^ (prefixWord ++ tailWord_329487).sum := by decide
  have hdescent : baseEnd_329487 < baseStart_329487 := by decide
  rcases family_descends (prefixWord ++ tailWord_329487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329506 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_329506 : Nat := 118140960795 + 329506 * 2 ^ 59
def prefixEnd_329506 : Nat := 4983230072969 + 3 ^ 40 * 329506 * 2
def baseEnd_329506 : Nat := 112796637693662026639757

theorem tailTrace_329506 : CollatzResearch.WordTrace tailWord_329506 prefixEnd_329506 112796637693662026639757 := by
  unfold tailWord_329506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3004517786065877997404093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8012047429509007993077581 3004517786065877997404093)
  ·
    refine ⟨1126694169774704249026535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3004517786065877997404093 1126694169774704249026535)
    ·
      refine ⟨1690041254662056373539803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1126694169774704249026535 1690041254662056373539803)
      ·
        refine ⟨2535061881993084560309705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1690041254662056373539803 2535061881993084560309705)
        ·
          refine ⟨1901296411494813420232279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2535061881993084560309705 1901296411494813420232279)
          ·
            refine ⟨2851944617242220130348419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901296411494813420232279 2851944617242220130348419)
            ·
              refine ⟨4277916925863330195522629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2851944617242220130348419 4277916925863330195522629)
              ·
                refine ⟨802109423599374411660493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4277916925863330195522629 802109423599374411660493)
                ·
                  refine ⟨300791033849765404372685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802109423599374411660493 300791033849765404372685)
                  ·
                    refine ⟨112796637693662026639757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 300791033849765404372685 112796637693662026639757)
                    ·
                      rfl

theorem cell22_329506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_329506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329506 prefixEnd_329506 := by exact prefixLift 329506
  have htrace : WordTrace (prefixWord ++ tailWord_329506) baseStart_329506 baseEnd_329506 := by
    simpa [prefixWord, tailWord_329506, baseEnd_329506] using wordTrace_append hprefix tailTrace_329506
  have hstable : (prefixWord ++ tailWord_329506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329506).length < 2 ^ (prefixWord ++ tailWord_329506).sum := by decide
  have hdescent : baseEnd_329506 < baseStart_329506 := by decide
  rcases family_descends (prefixWord ++ tailWord_329506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329553 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 5]
def baseStart_329553 : Nat := 118140960795 + 329553 * 2 ^ 59
def prefixEnd_329553 : Nat := 4983230072969 + 3 ^ 40 * 329553 * 2
def baseEnd_329553 : Nat := 37604242251389856904871

theorem tailTrace_329553 : CollatzResearch.WordTrace tailWord_329553 prefixEnd_329553 37604242251389856904871 := by
  unfold tailWord_329553
  simp only [CollatzResearch.WordTrace]
  refine ⟨12019785375093239016577313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8013190250062159344384875 12019785375093239016577313)
  ·
    refine ⟨9014839031319929262432985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12019785375093239016577313 9014839031319929262432985)
    ·
      refine ⟨6761129273489946946824739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9014839031319929262432985 6761129273489946946824739)
      ·
        refine ⟨10141693910234920420237109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6761129273489946946824739 10141693910234920420237109)
        ·
          refine ⟨950783804084523789397229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10141693910234920420237109 950783804084523789397229)
          ·
            refine ⟨356543926531696421023961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 950783804084523789397229 356543926531696421023961)
            ·
              refine ⟨267407944898772315767971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356543926531696421023961 267407944898772315767971)
              ·
                refine ⟨401111917348158473651957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267407944898772315767971 401111917348158473651957)
                ·
                  refine ⟨37604242251389856904871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 401111917348158473651957 37604242251389856904871)
                  ·
                    rfl

theorem cell22_329553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 5].length) (baseStart_329553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329553 prefixEnd_329553 := by exact prefixLift 329553
  have htrace : WordTrace (prefixWord ++ tailWord_329553) baseStart_329553 baseEnd_329553 := by
    simpa [prefixWord, tailWord_329553, baseEnd_329553] using wordTrace_append hprefix tailTrace_329553
  have hstable : (prefixWord ++ tailWord_329553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329553).length < 2 ^ (prefixWord ++ tailWord_329553).sum := by decide
  have hdescent : baseEnd_329553 < baseStart_329553 := by decide
  rcases family_descends (prefixWord ++ tailWord_329553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329628 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_329628 : Nat := 118140960795 + 329628 * 2 ^ 59
def prefixEnd_329628 : Nat := 4983230072969 + 3 ^ 40 * 329628 * 2
def baseEnd_329628 : Nat := 112838400786894375089383

theorem tailTrace_329628 : CollatzResearch.WordTrace tailWord_329628 prefixEnd_329628 112838400786894375089383 := by
  unfold tailWord_329628
  simp only [CollatzResearch.WordTrace]
  refine ⟨6011260424910763412778769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8015013899881017883705025 6011260424910763412778769)
  ·
    refine ⟨4508445318683072559584077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6011260424910763412778769 4508445318683072559584077)
    ·
      refine ⟨1690666994506152209844029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4508445318683072559584077 1690666994506152209844029)
      ·
        refine ⟨634000122939807078691511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1690666994506152209844029 634000122939807078691511)
        ·
          refine ⟨951000184409710618037267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634000122939807078691511 951000184409710618037267)
          ·
            refine ⟨1426500276614565927055901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951000184409710618037267 1426500276614565927055901)
            ·
              refine ⟨534937603730462222645963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1426500276614565927055901 534937603730462222645963)
              ·
                refine ⟨802406405595693333968945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534937603730462222645963 802406405595693333968945)
                ·
                  refine ⟨601804804196770000476709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 802406405595693333968945 601804804196770000476709)
                  ·
                    refine ⟨112838400786894375089383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 601804804196770000476709 112838400786894375089383)
                    ·
                      rfl

theorem cell22_329628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_329628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329628 prefixEnd_329628 := by exact prefixLift 329628
  have htrace : WordTrace (prefixWord ++ tailWord_329628) baseStart_329628 baseEnd_329628 := by
    simpa [prefixWord, tailWord_329628, baseEnd_329628] using wordTrace_append hprefix tailTrace_329628
  have hstable : (prefixWord ++ tailWord_329628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329628).length < 2 ^ (prefixWord ++ tailWord_329628).sum := by decide
  have hdescent : baseEnd_329628 < baseStart_329628 := by decide
  rcases family_descends (prefixWord ++ tailWord_329628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329669 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_329669 : Nat := 118140960795 + 329669 * 2 ^ 59
def prefixEnd_329669 : Nat := 4983230072969 + 3 ^ 40 * 329669 * 2
def baseEnd_329669 : Nat := 112852435924783934814257

theorem tailTrace_329669 : CollatzResearch.WordTrace tailWord_329669 prefixEnd_329669 112852435924783934814257 := by
  unfold tailWord_329669
  simp only [CollatzResearch.WordTrace]
  refine ⟨12024016242672990827800061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8016010828448660551866707 12024016242672990827800061)
  ·
    refine ⟨4509006091002371560425023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12024016242672990827800061 4509006091002371560425023)
    ·
      refine ⟨6763509136503557340637535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4509006091002371560425023 6763509136503557340637535)
      ·
        refine ⟨10145263704755336010956303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6763509136503557340637535 10145263704755336010956303)
        ·
          refine ⟨15217895557133004016434455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10145263704755336010956303 15217895557133004016434455)
          ·
            refine ⟨22826843335699506024651683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15217895557133004016434455 22826843335699506024651683)
            ·
              refine ⟨34240265003549259036977525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22826843335699506024651683 34240265003549259036977525)
              ·
                refine ⟨3210024844082743034716643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34240265003549259036977525 3210024844082743034716643)
                ·
                  refine ⟨4815037266124114552074965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210024844082743034716643 4815037266124114552074965)
                  ·
                    refine ⟨112852435924783934814257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4815037266124114552074965 112852435924783934814257)
                    ·
                      rfl

theorem cell22_329669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_329669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329669 prefixEnd_329669 := by exact prefixLift 329669
  have htrace : WordTrace (prefixWord ++ tailWord_329669) baseStart_329669 baseEnd_329669 := by
    simpa [prefixWord, tailWord_329669, baseEnd_329669] using wordTrace_append hprefix tailTrace_329669
  have hstable : (prefixWord ++ tailWord_329669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329669).length < 2 ^ (prefixWord ++ tailWord_329669).sum := by decide
  have hdescent : baseEnd_329669 < baseStart_329669 := by decide
  rcases family_descends (prefixWord ++ tailWord_329669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329709 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_329709 : Nat := 118140960795 + 329709 * 2 ^ 59
def prefixEnd_329709 : Nat := 4983230072969 + 3 ^ 40 * 329709 * 2
def baseEnd_329709 : Nat := 112866128742237163814135

theorem tailTrace_329709 : CollatzResearch.WordTrace tailWord_329709 prefixEnd_329709 112866128742237163814135 := by
  unfold tailWord_329709
  simp only [CollatzResearch.WordTrace]
  refine ⟨12025475162528077659256181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8016983441685385106170787 12025475162528077659256181)
  ·
    refine ⟨1127388296487007280555267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12025475162528077659256181 1127388296487007280555267)
    ·
      refine ⟨1691082444730510920832901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1127388296487007280555267 1691082444730510920832901)
      ·
        refine ⟨317077958386970797656169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1691082444730510920832901 317077958386970797656169)
        ·
          refine ⟨237808468790228098242127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317077958386970797656169 237808468790228098242127)
          ·
            refine ⟨356712703185342147363191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237808468790228098242127 356712703185342147363191)
            ·
              refine ⟨535069054778013221044787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356712703185342147363191 535069054778013221044787)
              ·
                refine ⟨802603582167019831567181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535069054778013221044787 802603582167019831567181)
                ·
                  refine ⟨300976343312632436837693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802603582167019831567181 300976343312632436837693)
                  ·
                    refine ⟨112866128742237163814135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 300976343312632436837693 112866128742237163814135)
                    ·
                      rfl

theorem cell22_329709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_329709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329709 prefixEnd_329709 := by exact prefixLift 329709
  have htrace : WordTrace (prefixWord ++ tailWord_329709) baseStart_329709 baseEnd_329709 := by
    simpa [prefixWord, tailWord_329709, baseEnd_329709] using wordTrace_append hprefix tailTrace_329709
  have hstable : (prefixWord ++ tailWord_329709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329709).length < 2 ^ (prefixWord ++ tailWord_329709).sum := by decide
  have hdescent : baseEnd_329709 < baseStart_329709 := by decide
  rcases family_descends (prefixWord ++ tailWord_329709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329735 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 1, 4]
def baseStart_329735 : Nat := 118140960795 + 329735 * 2 ^ 59
def prefixEnd_329735 : Nat := 4983230072969 + 3 ^ 40 * 329735 * 2
def baseEnd_329735 : Nat := 112875029073581762664055

theorem tailTrace_329735 : CollatzResearch.WordTrace tailWord_329735 prefixEnd_329735 112875029073581762664055 := by
  unfold tailWord_329735
  simp only [CollatzResearch.WordTrace]
  refine ⟨12026423460433884099702659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8017615640289256066468439 12026423460433884099702659)
  ·
    refine ⟨18039635190650826149553989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12026423460433884099702659 18039635190650826149553989)
    ·
      refine ⟨3382431598247029903041373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18039635190650826149553989 3382431598247029903041373)
      ·
        refine ⟨1268411849342636213640515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3382431598247029903041373 1268411849342636213640515)
        ·
          refine ⟨1902617774013954320460773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268411849342636213640515 1902617774013954320460773)
          ·
            refine ⟨356740832627616435086395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1902617774013954320460773 356740832627616435086395)
            ·
              refine ⟨535111248941424652629593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356740832627616435086395 535111248941424652629593)
              ·
                refine ⟨401333436706068489472195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535111248941424652629593 401333436706068489472195)
                ·
                  refine ⟨602000155059102734208293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401333436706068489472195 602000155059102734208293)
                  ·
                    refine ⟨112875029073581762664055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 602000155059102734208293 112875029073581762664055)
                    ·
                      rfl

theorem cell22_329735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_329735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329735 prefixEnd_329735 := by exact prefixLift 329735
  have htrace : WordTrace (prefixWord ++ tailWord_329735) baseStart_329735 baseEnd_329735 := by
    simpa [prefixWord, tailWord_329735, baseEnd_329735] using wordTrace_append hprefix tailTrace_329735
  have hstable : (prefixWord ++ tailWord_329735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329735).length < 2 ^ (prefixWord ++ tailWord_329735).sum := by decide
  have hdescent : baseEnd_329735 < baseStart_329735 := by decide
  rcases family_descends (prefixWord ++ tailWord_329735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329761 : List Nat := [1, 2, 3, 2, 4, 10]
def baseStart_329761 : Nat := 118140960795 + 329761 * 2 ^ 59
def prefixEnd_329761 : Nat := 4983230072969 + 3 ^ 40 * 329761 * 2
def baseEnd_329761 : Nat := 1393628758085510635975

theorem tailTrace_329761 : CollatzResearch.WordTrace tailWord_329761 prefixEnd_329761 1393628758085510635975 := by
  unfold tailWord_329761
  simp only [CollatzResearch.WordTrace]
  refine ⟨12027371758339690540149137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8018247838893127026766091 12027371758339690540149137)
  ·
    refine ⟨9020528818754767905111853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12027371758339690540149137 9020528818754767905111853)
    ·
      refine ⟨3382698307033037964416945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9020528818754767905111853 3382698307033037964416945)
      ·
        refine ⟨2537023730274778473312709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3382698307033037964416945 2537023730274778473312709)
        ·
          refine ⟨475691949426520963746133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2537023730274778473312709 475691949426520963746133)
          ·
            refine ⟨1393628758085510635975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 475691949426520963746133 1393628758085510635975)
            ·
              rfl

theorem cell22_329761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 10].length) (baseStart_329761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329761 prefixEnd_329761 := by exact prefixLift 329761
  have htrace : WordTrace (prefixWord ++ tailWord_329761) baseStart_329761 baseEnd_329761 := by
    simpa [prefixWord, tailWord_329761, baseEnd_329761] using wordTrace_append hprefix tailTrace_329761
  have hstable : (prefixWord ++ tailWord_329761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329761).length < 2 ^ (prefixWord ++ tailWord_329761).sum := by decide
  have hdescent : baseEnd_329761 < baseStart_329761 := by decide
  rcases family_descends (prefixWord ++ tailWord_329761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329765 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 2, 3]
def baseStart_329765 : Nat := 118140960795 + 329765 * 2 ^ 59
def prefixEnd_329765 : Nat := 4983230072969 + 3 ^ 40 * 329765 * 2
def baseEnd_329765 : Nat := 112885298686671684413963

theorem tailTrace_329765 : CollatzResearch.WordTrace tailWord_329765 prefixEnd_329765 112885298686671684413963 := by
  unfold tailWord_329765
  simp only [CollatzResearch.WordTrace]
  refine ⟨12027517650325199223294749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8018345100216799482196499 12027517650325199223294749)
  ·
    refine ⟨4510319118871949708735531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12027517650325199223294749 4510319118871949708735531)
    ·
      refine ⟨6765478678307924563103297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4510319118871949708735531 6765478678307924563103297)
      ·
        refine ⟨5074109008730943422327473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6765478678307924563103297 5074109008730943422327473)
        ·
          refine ⟨3805581756548207566745605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5074109008730943422327473 3805581756548207566745605)
          ·
            refine ⟨713546579352788918764801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3805581756548207566745605 713546579352788918764801)
            ·
              refine ⟨535159934514591689073601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713546579352788918764801 535159934514591689073601)
              ·
                refine ⟨401369950885943766805201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535159934514591689073601 401369950885943766805201)
                ·
                  refine ⟨301027463164457825103901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401369950885943766805201 301027463164457825103901)
                  ·
                    refine ⟨112885298686671684413963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301027463164457825103901 112885298686671684413963)
                    ·
                      rfl

theorem cell22_329765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_329765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329765 prefixEnd_329765 := by exact prefixLift 329765
  have htrace : WordTrace (prefixWord ++ tailWord_329765) baseStart_329765 baseEnd_329765 := by
    simpa [prefixWord, tailWord_329765, baseEnd_329765] using wordTrace_append hprefix tailTrace_329765
  have hstable : (prefixWord ++ tailWord_329765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329765).length < 2 ^ (prefixWord ++ tailWord_329765).sum := by decide
  have hdescent : baseEnd_329765 < baseStart_329765 := by decide
  rcases family_descends (prefixWord ++ tailWord_329765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329767 : List Nat := [1, 1, 7, 1, 2, 1, 1, 4, 4]
def baseStart_329767 : Nat := 118140960795 + 329767 * 2 ^ 59
def prefixEnd_329767 : Nat := 4983230072969 + 3 ^ 40 * 329767 * 2
def baseEnd_329767 : Nat := 37628661109181448621319

theorem tailTrace_329767 : CollatzResearch.WordTrace tailWord_329767 prefixEnd_329767 37628661109181448621319 := by
  unfold tailWord_329767
  simp only [CollatzResearch.WordTrace]
  refine ⟨12027590596317953564867555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8018393730878635709911703 12027590596317953564867555)
  ·
    refine ⟨18041385894476930347301333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12027590596317953564867555 18041385894476930347301333)
    ·
      refine ⟨422844981901803055014875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18041385894476930347301333 422844981901803055014875)
      ·
        refine ⟨634267472852704582522313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422844981901803055014875 634267472852704582522313)
        ·
          refine ⟨475700604639528436891735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 634267472852704582522313 475700604639528436891735)
          ·
            refine ⟨713550906959292655337603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475700604639528436891735 713550906959292655337603)
            ·
              refine ⟨1070326360438938983006405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713550906959292655337603 1070326360438938983006405)
              ·
                refine ⟨200686192582301059313701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1070326360438938983006405 200686192582301059313701)
                ·
                  refine ⟨37628661109181448621319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200686192582301059313701 37628661109181448621319)
                  ·
                    rfl

theorem cell22_329767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 4].length) (baseStart_329767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329767 prefixEnd_329767 := by exact prefixLift 329767
  have htrace : WordTrace (prefixWord ++ tailWord_329767) baseStart_329767 baseEnd_329767 := by
    simpa [prefixWord, tailWord_329767, baseEnd_329767] using wordTrace_append hprefix tailTrace_329767
  have hstable : (prefixWord ++ tailWord_329767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329767).length < 2 ^ (prefixWord ++ tailWord_329767).sum := by decide
  have hdescent : baseEnd_329767 < baseStart_329767 := by decide
  rcases family_descends (prefixWord ++ tailWord_329767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329778 : List Nat := [3, 2, 1, 1, 2, 5, 1, 7]
def baseStart_329778 : Nat := 118140960795 + 329778 * 2 ^ 59
def prefixEnd_329778 : Nat := 4983230072969 + 3 ^ 40 * 329778 * 2
def baseEnd_329778 : Nat := 12543305428038220426547

theorem tailTrace_329778 : CollatzResearch.WordTrace tailWord_329778 prefixEnd_329778 12543305428038220426547 := by
  unfold tailWord_329778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3006997949819525610879497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8018661199518734962345325 3006997949819525610879497)
  ·
    refine ⟨2255248462364644208159623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3006997949819525610879497 2255248462364644208159623)
    ·
      refine ⟨3382872693546966312239435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255248462364644208159623 3382872693546966312239435)
      ·
        refine ⟨5074309040320449468359153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3382872693546966312239435 5074309040320449468359153)
        ·
          refine ⟨3805731780240337101269365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5074309040320449468359153 3805731780240337101269365)
          ·
            refine ⟨356787354397531603244003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3805731780240337101269365 356787354397531603244003)
            ·
              refine ⟨535181031596297404866005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356787354397531603244003 535181031596297404866005)
              ·
                refine ⟨12543305428038220426547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 535181031596297404866005 12543305428038220426547)
                ·
                  rfl

theorem cell22_329778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_329778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329778 prefixEnd_329778 := by exact prefixLift 329778
  have htrace : WordTrace (prefixWord ++ tailWord_329778) baseStart_329778 baseEnd_329778 := by
    simpa [prefixWord, tailWord_329778, baseEnd_329778] using wordTrace_append hprefix tailTrace_329778
  have hstable : (prefixWord ++ tailWord_329778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329778).length < 2 ^ (prefixWord ++ tailWord_329778).sum := by decide
  have hdescent : baseEnd_329778 < baseStart_329778 := by decide
  rcases family_descends (prefixWord ++ tailWord_329778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329838 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_329838 : Nat := 118140960795 + 329838 * 2 ^ 59
def prefixEnd_329838 : Nat := 4983230072969 + 3 ^ 40 * 329838 * 2
def baseEnd_329838 : Nat := 112910288078523827338739

theorem tailTrace_329838 : CollatzResearch.WordTrace tailWord_329838 prefixEnd_329838 112910288078523827338739 := by
  unfold tailWord_329838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503772522382591586337771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8020120119373821793801445 1503772522382591586337771)
  ·
    refine ⟨2255658783573887379506657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1503772522382591586337771 2255658783573887379506657)
    ·
      refine ⟨1691744087680415534629993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2255658783573887379506657 1691744087680415534629993)
      ·
        refine ⟨1268808065760311650972495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1691744087680415534629993 1268808065760311650972495)
        ·
          refine ⟨1903212098640467476458743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268808065760311650972495 1903212098640467476458743)
          ·
            refine ⟨2854818147960701214688115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903212098640467476458743 2854818147960701214688115)
            ·
              refine ⟨4282227221941051822032173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854818147960701214688115 4282227221941051822032173)
              ·
                refine ⟨1605835208227894433262065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4282227221941051822032173 1605835208227894433262065)
                ·
                  refine ⟨1204376406170920824946549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605835208227894433262065 1204376406170920824946549)
                  ·
                    refine ⟨112910288078523827338739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1204376406170920824946549 112910288078523827338739)
                    ·
                      rfl

theorem cell22_329838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_329838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329838 prefixEnd_329838 := by exact prefixLift 329838
  have htrace : WordTrace (prefixWord ++ tailWord_329838) baseStart_329838 baseEnd_329838 := by
    simpa [prefixWord, tailWord_329838, baseEnd_329838] using wordTrace_append hprefix tailTrace_329838
  have hstable : (prefixWord ++ tailWord_329838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329838).length < 2 ^ (prefixWord ++ tailWord_329838).sum := by decide
  have hdescent : baseEnd_329838 < baseStart_329838 := by decide
  rcases family_descends (prefixWord ++ tailWord_329838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329840 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 5]
def baseStart_329840 : Nat := 118140960795 + 329840 * 2 ^ 59
def prefixEnd_329840 : Nat := 4983230072969 + 3 ^ 40 * 329840 * 2
def baseEnd_329840 : Nat := 37636990906465496262911

theorem tailTrace_329840 : CollatzResearch.WordTrace tailWord_329840 prefixEnd_329840 37636990906465496262911 := by
  unfold tailWord_329840
  simp only [CollatzResearch.WordTrace]
  refine ⟨6015126562526743516137487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8020168750035658021516649 6015126562526743516137487)
  ·
    refine ⟨9022689843790115274206231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6015126562526743516137487 9022689843790115274206231)
    ·
      refine ⟨13534034765685172911309347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9022689843790115274206231 13534034765685172911309347)
      ·
        refine ⟨20301052148527759366964021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13534034765685172911309347 20301052148527759366964021)
        ·
          refine ⟨1903223638924477440652877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20301052148527759366964021 1903223638924477440652877)
          ·
            refine ⟨713708864596679040244829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1903223638924477440652877 713708864596679040244829)
            ·
              refine ⟨267640824223754640091811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 713708864596679040244829 267640824223754640091811)
              ·
                refine ⟨401461236335631960137717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267640824223754640091811 401461236335631960137717)
                ·
                  refine ⟨37636990906465496262911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 401461236335631960137717 37636990906465496262911)
                  ·
                    rfl

theorem cell22_329840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 5].length) (baseStart_329840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329840 prefixEnd_329840 := by exact prefixLift 329840
  have htrace : WordTrace (prefixWord ++ tailWord_329840) baseStart_329840 baseEnd_329840 := by
    simpa [prefixWord, tailWord_329840, baseEnd_329840] using wordTrace_append hprefix tailTrace_329840
  have hstable : (prefixWord ++ tailWord_329840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329840).length < 2 ^ (prefixWord ++ tailWord_329840).sum := by decide
  have hdescent : baseEnd_329840 < baseStart_329840 := by decide
  rcases family_descends (prefixWord ++ tailWord_329840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329883 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 4, 3]
def baseStart_329883 : Nat := 118140960795 + 329883 * 2 ^ 59
def prefixEnd_329883 : Nat := 4983230072969 + 3 ^ 40 * 329883 * 2
def baseEnd_329883 : Nat := 112925692498158709963601

theorem tailTrace_329883 : CollatzResearch.WordTrace tailWord_329883 prefixEnd_329883 112925692498158709963601 := by
  unfold tailWord_329883
  simp only [CollatzResearch.WordTrace]
  refine ⟨12031821463897705376090303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8021214309265136917393535 12031821463897705376090303)
  ·
    refine ⟨18047732195846558064135455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12031821463897705376090303 18047732195846558064135455)
    ·
      refine ⟨27071598293769837096203183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18047732195846558064135455 27071598293769837096203183)
      ·
        refine ⟨40607397440654755644304775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27071598293769837096203183 40607397440654755644304775)
        ·
          refine ⟨60911096160982133466457163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40607397440654755644304775 60911096160982133466457163)
          ·
            refine ⟨91366644241473200199685745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60911096160982133466457163 91366644241473200199685745)
            ·
              refine ⟨68524983181104900149764309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91366644241473200199685745 68524983181104900149764309)
              ·
                refine ⟨1606054293307146097260101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68524983181104900149764309 1606054293307146097260101)
                ·
                  refine ⟨301135179995089893236269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1606054293307146097260101 301135179995089893236269)
                  ·
                    refine ⟨112925692498158709963601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301135179995089893236269 112925692498158709963601)
                    ·
                      rfl

theorem cell22_329883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 3].length) (baseStart_329883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329883 prefixEnd_329883 := by exact prefixLift 329883
  have htrace : WordTrace (prefixWord ++ tailWord_329883) baseStart_329883 baseEnd_329883 := by
    simpa [prefixWord, tailWord_329883, baseEnd_329883] using wordTrace_append hprefix tailTrace_329883
  have hstable : (prefixWord ++ tailWord_329883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329883).length < 2 ^ (prefixWord ++ tailWord_329883).sum := by decide
  have hdescent : baseEnd_329883 < baseStart_329883 := by decide
  rcases family_descends (prefixWord ++ tailWord_329883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329885 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 6]
def baseStart_329885 : Nat := 118140960795 + 329885 * 2 ^ 59
def prefixEnd_329885 : Nat := 4983230072969 + 3 ^ 40 * 329885 * 2
def baseEnd_329885 : Nat := 37642125713010457137865

theorem tailTrace_329885 : CollatzResearch.WordTrace tailWord_329885 prefixEnd_329885 37642125713010457137865 := by
  unfold tailWord_329885
  simp only [CollatzResearch.WordTrace]
  refine ⟨12031894409890459717663109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8021262939926973145108739 12031894409890459717663109)
  ·
    refine ⟨2255980201854461197061833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12031894409890459717663109 2255980201854461197061833)
    ·
      refine ⟨1691985151390845897796375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2255980201854461197061833 1691985151390845897796375)
      ·
        refine ⟨2537977727086268846694563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1691985151390845897796375 2537977727086268846694563)
        ·
          refine ⟨3806966590629403270041845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2537977727086268846694563 3806966590629403270041845)
          ·
            refine ⟨356903117871506556566423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3806966590629403270041845 356903117871506556566423)
            ·
              refine ⟨535354676807259834849635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356903117871506556566423 535354676807259834849635)
              ·
                refine ⟨803032015210889752274453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535354676807259834849635 803032015210889752274453)
                ·
                  refine ⟨37642125713010457137865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 803032015210889752274453 37642125713010457137865)
                  ·
                    rfl

theorem cell22_329885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_329885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329885 prefixEnd_329885 := by exact prefixLift 329885
  have htrace : WordTrace (prefixWord ++ tailWord_329885) baseStart_329885 baseEnd_329885 := by
    simpa [prefixWord, tailWord_329885, baseEnd_329885] using wordTrace_append hprefix tailTrace_329885
  have hstable : (prefixWord ++ tailWord_329885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329885).length < 2 ^ (prefixWord ++ tailWord_329885).sum := by decide
  have hdescent : baseEnd_329885 < baseStart_329885 := by decide
  rcases family_descends (prefixWord ++ tailWord_329885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329992 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 5]
def baseStart_329992 : Nat := 118140960795 + 329992 * 2 ^ 59
def prefixEnd_329992 : Nat := 4983230072969 + 3 ^ 40 * 329992 * 2
def baseEnd_329992 : Nat := 37654335141906252996089

theorem tailTrace_329992 : CollatzResearch.WordTrace tailWord_329992 prefixEnd_329992 37654335141906252996089 := by
  unfold tailWord_329992
  simp only [CollatzResearch.WordTrace]
  refine ⟨6017898510251408495904115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8023864680335211327872153 6017898510251408495904115)
  ·
    refine ⟨9026847765377112743856173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6017898510251408495904115 9026847765377112743856173)
    ·
      refine ⟨3385067912016417278946065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9026847765377112743856173 3385067912016417278946065)
      ·
        refine ⟨2538800934012312959209549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3385067912016417278946065 2538800934012312959209549)
        ·
          refine ⟨952050350254617359703581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2538800934012312959209549 952050350254617359703581)
          ·
            refine ⟨357018881345481509888843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 952050350254617359703581 357018881345481509888843)
            ·
              refine ⟨535528322018222264833265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357018881345481509888843 535528322018222264833265)
              ·
                refine ⟨401646241513666698624949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535528322018222264833265 401646241513666698624949)
                ·
                  refine ⟨37654335141906252996089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 401646241513666698624949 37654335141906252996089)
                  ·
                    rfl

theorem cell22_329992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 5].length) (baseStart_329992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_329992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_329992 prefixEnd_329992 := by exact prefixLift 329992
  have htrace : WordTrace (prefixWord ++ tailWord_329992) baseStart_329992 baseEnd_329992 := by
    simpa [prefixWord, tailWord_329992, baseEnd_329992] using wordTrace_append hprefix tailTrace_329992
  have hstable : (prefixWord ++ tailWord_329992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329992).length < 2 ^ (prefixWord ++ tailWord_329992).sum := by decide
  have hdescent : baseEnd_329992 < baseStart_329992 := by decide
  rcases family_descends (prefixWord ++ tailWord_329992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330020 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 6]
def baseStart_330020 : Nat := 118140960795 + 330020 * 2 ^ 59
def prefixEnd_330020 : Nat := 4983230072969 + 3 ^ 40 * 330020 * 2
def baseEnd_330020 : Nat := 37657530132645339762727

theorem tailTrace_330020 : CollatzResearch.WordTrace tailWord_330020 prefixEnd_330020 37657530132645339762727 := by
  unfold tailWord_330020
  simp only [CollatzResearch.WordTrace]
  refine ⟨6018409132200688886913757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8024545509600918515885009 6018409132200688886913757)
  ·
    refine ⟨2256903424575258332592659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6018409132200688886913757 2256903424575258332592659)
    ·
      refine ⟨3385355136862887498888989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2256903424575258332592659 3385355136862887498888989)
      ·
        refine ⟨1269508176323582812083371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3385355136862887498888989 1269508176323582812083371)
        ·
          refine ⟨1904262264485374218125057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269508176323582812083371 1904262264485374218125057)
          ·
            refine ⟨1428196698364030663593793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1904262264485374218125057 1428196698364030663593793)
            ·
              refine ⟨1071147523773022997695345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428196698364030663593793 1071147523773022997695345)
              ·
                refine ⟨803360642829767248271509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071147523773022997695345 803360642829767248271509)
                ·
                  refine ⟨37657530132645339762727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 803360642829767248271509 37657530132645339762727)
                  ·
                    rfl

theorem cell22_330020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_330020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330020 prefixEnd_330020 := by exact prefixLift 330020
  have htrace : WordTrace (prefixWord ++ tailWord_330020) baseStart_330020 baseEnd_330020 := by
    simpa [prefixWord, tailWord_330020, baseEnd_330020] using wordTrace_append hprefix tailTrace_330020
  have hstable : (prefixWord ++ tailWord_330020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330020).length < 2 ^ (prefixWord ++ tailWord_330020).sum := by decide
  have hdescent : baseEnd_330020 < baseStart_330020 := by decide
  rcases family_descends (prefixWord ++ tailWord_330020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330030 : List Nat := [4, 1, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_330030 : Nat := 118140960795 + 330030 * 2 ^ 59
def prefixEnd_330030 : Nat := 4983230072969 + 3 ^ 40 * 330030 * 2
def baseEnd_330030 : Nat := 112976013602299326538151

theorem tailTrace_330030 : CollatzResearch.WordTrace tailWord_330030 prefixEnd_330030 112976013602299326538151 := by
  unfold tailWord_330030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1504647874295643685211443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8024788662910099654461029 1504647874295643685211443)
  ·
    refine ⟨2256971811443465527817165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1504647874295643685211443 2256971811443465527817165)
    ·
      refine ⟨846364429291299572931437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2256971811443465527817165 846364429291299572931437)
      ·
        refine ⟨317386660984237339849289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 846364429291299572931437 317386660984237339849289)
        ·
          refine ⟨238039995738178004886967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317386660984237339849289 238039995738178004886967)
          ·
            refine ⟨357059993607267007330451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238039995738178004886967 357059993607267007330451)
            ·
              refine ⟨535589990410900510995677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357059993607267007330451 535589990410900510995677)
              ·
                refine ⟨200846246404087691623379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 535589990410900510995677 200846246404087691623379)
                ·
                  refine ⟨301269369606131537435069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200846246404087691623379 301269369606131537435069)
                  ·
                    refine ⟨112976013602299326538151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301269369606131537435069 112976013602299326538151)
                    ·
                      rfl

theorem cell22_330030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_330030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330030 prefixEnd_330030 := by exact prefixLift 330030
  have htrace : WordTrace (prefixWord ++ tailWord_330030) baseStart_330030 baseEnd_330030 := by
    simpa [prefixWord, tailWord_330030, baseEnd_330030] using wordTrace_append hprefix tailTrace_330030
  have hstable : (prefixWord ++ tailWord_330030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330030).length < 2 ^ (prefixWord ++ tailWord_330030).sum := by decide
  have hdescent : baseEnd_330030 < baseStart_330030 := by decide
  rcases family_descends (prefixWord ++ tailWord_330030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330035 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 6, 3]
def baseStart_330035 : Nat := 118140960795 + 330035 * 2 ^ 59
def prefixEnd_330035 : Nat := 4983230072969 + 3 ^ 40 * 330035 * 2
def baseEnd_330035 : Nat := 112977725204480980163135

theorem tailTrace_330035 : CollatzResearch.WordTrace tailWord_330035 prefixEnd_330035 112977725204480980163135 := by
  unfold tailWord_330035
  simp only [CollatzResearch.WordTrace]
  refine ⟨12037365359347035335623559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8024910239564690223749039 12037365359347035335623559)
  ·
    refine ⟨18056048039020553003435339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12037365359347035335623559 18056048039020553003435339)
    ·
      refine ⟨27084072058530829505153009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18056048039020553003435339 27084072058530829505153009)
      ·
        refine ⟨20313054043898122128864757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27084072058530829505153009 20313054043898122128864757)
        ·
          refine ⟨1904348816615448949581071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20313054043898122128864757 1904348816615448949581071)
          ·
            refine ⟨2856523224923173424371607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904348816615448949581071 2856523224923173424371607)
            ·
              refine ⟨4284784837384760136557411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856523224923173424371607 4284784837384760136557411)
              ·
                refine ⟨6427177256077140204836117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4284784837384760136557411 6427177256077140204836117)
                ·
                  refine ⟨301273933878615947101693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6427177256077140204836117 301273933878615947101693)
                  ·
                    refine ⟨112977725204480980163135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301273933878615947101693 112977725204480980163135)
                    ·
                      rfl

theorem cell22_330035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 3].length) (baseStart_330035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330035 prefixEnd_330035 := by exact prefixLift 330035
  have htrace : WordTrace (prefixWord ++ tailWord_330035) baseStart_330035 baseEnd_330035 := by
    simpa [prefixWord, tailWord_330035, baseEnd_330035] using wordTrace_append hprefix tailTrace_330035
  have hstable : (prefixWord ++ tailWord_330035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330035).length < 2 ^ (prefixWord ++ tailWord_330035).sum := by decide
  have hdescent : baseEnd_330035 < baseStart_330035 := by decide
  rcases family_descends (prefixWord ++ tailWord_330035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330063 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 2, 7]
def baseStart_330063 : Nat := 118140960795 + 330063 * 2 ^ 59
def prefixEnd_330063 : Nat := 4983230072969 + 3 ^ 40 * 330063 * 2
def baseEnd_330063 : Nat := 112987310176698240463049

theorem tailTrace_330063 : CollatzResearch.WordTrace tailWord_330063 prefixEnd_330063 112987310176698240463049 := by
  unfold tailWord_330063
  simp only [CollatzResearch.WordTrace]
  refine ⟨12038386603245596117642843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8025591068830397411761895 12038386603245596117642843)
  ·
    refine ⟨18057579904868394176464265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12038386603245596117642843 18057579904868394176464265)
    ·
      refine ⟨13543184928651295632348199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18057579904868394176464265 13543184928651295632348199)
      ·
        refine ⟨20314777392976943448522299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13543184928651295632348199 20314777392976943448522299)
        ·
          refine ⟨30472166089465415172783449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20314777392976943448522299 30472166089465415172783449)
          ·
            refine ⟨22854124567099061379587587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30472166089465415172783449 22854124567099061379587587)
            ·
              refine ⟨34281186850648592069381381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22854124567099061379587587 34281186850648592069381381)
              ·
                refine ⟨6427722534496611013009009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34281186850648592069381381 6427722534496611013009009)
                ·
                  refine ⟨4820791900872458259756757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6427722534496611013009009 4820791900872458259756757)
                  ·
                    refine ⟨112987310176698240463049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4820791900872458259756757 112987310176698240463049)
                    ·
                      rfl

theorem cell22_330063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_330063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330063 prefixEnd_330063 := by exact prefixLift 330063
  have htrace : WordTrace (prefixWord ++ tailWord_330063) baseStart_330063 baseEnd_330063 := by
    simpa [prefixWord, tailWord_330063, baseEnd_330063] using wordTrace_append hprefix tailTrace_330063
  have hstable : (prefixWord ++ tailWord_330063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330063).length < 2 ^ (prefixWord ++ tailWord_330063).sum := by decide
  have hdescent : baseEnd_330063 < baseStart_330063 := by decide
  rcases family_descends (prefixWord ++ tailWord_330063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330065 : List Nat := [1, 2, 2, 1, 4, 3, 2, 7]
def baseStart_330065 : Nat := 118140960795 + 330065 * 2 ^ 59
def prefixEnd_330065 : Nat := 4983230072969 + 3 ^ 40 * 330065 * 2
def baseEnd_330065 : Nat := 12554221646396766879227

theorem tailTrace_330065 : CollatzResearch.WordTrace tailWord_330065 prefixEnd_330065 12554221646396766879227 := by
  unfold tailWord_330065
  simp only [CollatzResearch.WordTrace]
  refine ⟨12038459549238350459215649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8025639699492233639477099 12038459549238350459215649)
  ·
    refine ⟨9028844661928762844411737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12038459549238350459215649 9028844661928762844411737)
    ·
      refine ⟨6771633496446572133308803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9028844661928762844411737 6771633496446572133308803)
      ·
        refine ⟨10157450244669858199963205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6771633496446572133308803 10157450244669858199963205)
        ·
          refine ⟨1904521920875598412493101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10157450244669858199963205 1904521920875598412493101)
          ·
            refine ⟨714195720328349404684913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1904521920875598412493101 714195720328349404684913)
            ·
              refine ⟨535646790246262053513685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714195720328349404684913 535646790246262053513685)
              ·
                refine ⟨12554221646396766879227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 535646790246262053513685 12554221646396766879227)
                ·
                  rfl

theorem cell22_330065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 7].length) (baseStart_330065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330065 prefixEnd_330065 := by exact prefixLift 330065
  have htrace : WordTrace (prefixWord ++ tailWord_330065) baseStart_330065 baseEnd_330065 := by
    simpa [prefixWord, tailWord_330065, baseEnd_330065] using wordTrace_append hprefix tailTrace_330065
  have hstable : (prefixWord ++ tailWord_330065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330065).length < 2 ^ (prefixWord ++ tailWord_330065).sum := by decide
  have hdescent : baseEnd_330065 < baseStart_330065 := by decide
  rcases family_descends (prefixWord ++ tailWord_330065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330069 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 2, 3]
def baseStart_330069 : Nat := 118140960795 + 330069 * 2 ^ 59
def prefixEnd_330069 : Nat := 4983230072969 + 3 ^ 40 * 330069 * 2
def baseEnd_330069 : Nat := 112989364099316224813031

theorem tailTrace_330069 : CollatzResearch.WordTrace tailWord_330069 prefixEnd_330069 112989364099316224813031 := by
  unfold tailWord_330069
  simp only [CollatzResearch.WordTrace]
  refine ⟨12038605441223859142361261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8025736960815906094907507 12038605441223859142361261)
  ·
    refine ⟨4514477040458947178385473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12038605441223859142361261 4514477040458947178385473)
    ·
      refine ⟨3385857780344210383789105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4514477040458947178385473 3385857780344210383789105)
      ·
        refine ⟨2539393335258157787841829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3385857780344210383789105 2539393335258157787841829)
        ·
          refine ⟨476136250360904585220343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2539393335258157787841829 476136250360904585220343)
          ·
            refine ⟨714204375541356877830515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476136250360904585220343 714204375541356877830515)
            ·
              refine ⟨1071306563312035316745773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714204375541356877830515 1071306563312035316745773)
              ·
                refine ⟨401739961242013243779665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1071306563312035316745773 401739961242013243779665)
                ·
                  refine ⟨301304970931509932834749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401739961242013243779665 301304970931509932834749)
                  ·
                    refine ⟨112989364099316224813031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301304970931509932834749 112989364099316224813031)
                    ·
                      rfl

theorem cell22_330069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_330069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330069 prefixEnd_330069 := by exact prefixLift 330069
  have htrace : WordTrace (prefixWord ++ tailWord_330069) baseStart_330069 baseEnd_330069 := by
    simpa [prefixWord, tailWord_330069, baseEnd_330069] using wordTrace_append hprefix tailTrace_330069
  have hstable : (prefixWord ++ tailWord_330069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330069).length < 2 ^ (prefixWord ++ tailWord_330069).sum := by decide
  have hdescent : baseEnd_330069 < baseStart_330069 := by decide
  rcases family_descends (prefixWord ++ tailWord_330069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330170 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_330170 : Nat := 118140960795 + 330170 * 2 ^ 59
def prefixEnd_330170 : Nat := 4983230072969 + 3 ^ 40 * 330170 * 2
def baseEnd_330170 : Nat := 113023938463385628037721

theorem tailTrace_330170 : CollatzResearch.WordTrace tailWord_330170 prefixEnd_330170 113023938463385628037721 := by
  unfold tailWord_330170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010572303464488347946991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8028192809238635594525309 3010572303464488347946991)
  ·
    refine ⟨4515858455196732521920487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3010572303464488347946991 4515858455196732521920487)
    ·
      refine ⟨6773787682795098782880731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4515858455196732521920487 6773787682795098782880731)
      ·
        refine ⟨10160681524192648174321097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6773787682795098782880731 10160681524192648174321097)
        ·
          refine ⟨7620511143144486130740823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10160681524192648174321097 7620511143144486130740823)
          ·
            refine ⟨11430766714716729196111235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7620511143144486130740823 11430766714716729196111235)
            ·
              refine ⟨17146150072075093794166853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11430766714716729196111235 17146150072075093794166853)
              ·
                refine ⟨3214903138514080086406285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17146150072075093794166853 3214903138514080086406285)
                ·
                  refine ⟨1205588676942780032402357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3214903138514080086406285 1205588676942780032402357)
                  ·
                    refine ⟨113023938463385628037721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1205588676942780032402357 113023938463385628037721)
                    ·
                      rfl

theorem cell22_330170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_330170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330170 prefixEnd_330170 := by exact prefixLift 330170
  have htrace : WordTrace (prefixWord ++ tailWord_330170) baseStart_330170 baseEnd_330170 := by
    simpa [prefixWord, tailWord_330170, baseEnd_330170] using wordTrace_append hprefix tailTrace_330170
  have hstable : (prefixWord ++ tailWord_330170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330170).length < 2 ^ (prefixWord ++ tailWord_330170).sum := by decide
  have hdescent : baseEnd_330170 < baseStart_330170 := by decide
  rcases family_descends (prefixWord ++ tailWord_330170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330172 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 6]
def baseStart_330172 : Nat := 118140960795 + 330172 * 2 ^ 59
def prefixEnd_330172 : Nat := 4983230072969 + 3 ^ 40 * 330172 * 2
def baseEnd_330172 : Nat := 37674874368086096495905

theorem tailTrace_330172 : CollatzResearch.WordTrace tailWord_330172 prefixEnd_330172 37674874368086096495905 := by
  unfold tailWord_330172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6021181079925353866680385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8028241439900471822240513 6021181079925353866680385)
  ·
    refine ⟨4515885809944015400010289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6021181079925353866680385 4515885809944015400010289)
    ·
      refine ⟨3386914357458011550007717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4515885809944015400010289 3386914357458011550007717)
      ·
        refine ⟨635046442023377165626447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3386914357458011550007717 635046442023377165626447)
        ·
          refine ⟨952569663035065748439671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635046442023377165626447 952569663035065748439671)
          ·
            refine ⟨1428854494552598622659507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952569663035065748439671 1428854494552598622659507)
            ·
              refine ⟨2143281741828897933989261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428854494552598622659507 2143281741828897933989261)
              ·
                refine ⟨803730653185836725245973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2143281741828897933989261 803730653185836725245973)
                ·
                  refine ⟨37674874368086096495905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 803730653185836725245973 37674874368086096495905)
                  ·
                    rfl

theorem cell22_330172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_330172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330172 prefixEnd_330172 := by exact prefixLift 330172
  have htrace : WordTrace (prefixWord ++ tailWord_330172) baseStart_330172 baseEnd_330172 := by
    simpa [prefixWord, tailWord_330172, baseEnd_330172] using wordTrace_append hprefix tailTrace_330172
  have hstable : (prefixWord ++ tailWord_330172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330172).length < 2 ^ (prefixWord ++ tailWord_330172).sum := by decide
  have hdescent : baseEnd_330172 < baseStart_330172 := by decide
  rcases family_descends (prefixWord ++ tailWord_330172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330185 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_330185 : Nat := 118140960795 + 330185 * 2 ^ 59
def prefixEnd_330185 : Nat := 4983230072969 + 3 ^ 40 * 330185 * 2
def baseEnd_330185 : Nat := 113029073269930588912675

theorem tailTrace_330185 : CollatzResearch.WordTrace tailWord_330185 prefixEnd_330185 113029073269930588912675 := by
  unfold tailWord_330185
  simp only [CollatzResearch.WordTrace]
  refine ⟨12042836308803610953584009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8028557539202407302389339 12042836308803610953584009)
  ·
    refine ⟨9032127231602708215188007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12042836308803610953584009 9032127231602708215188007)
    ·
      refine ⟨13548190847404062322782011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9032127231602708215188007 13548190847404062322782011)
      ·
        refine ⟨20322286271106093484173017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13548190847404062322782011 20322286271106093484173017)
        ·
          refine ⟨15241714703329570113129763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20322286271106093484173017 15241714703329570113129763)
          ·
            refine ⟨22862572054994355169694645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15241714703329570113129763 22862572054994355169694645)
            ·
              refine ⟨2143366130155720797158873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22862572054994355169694645 2143366130155720797158873)
              ·
                refine ⟨1607524597616790597869155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2143366130155720797158873 1607524597616790597869155)
                ·
                  refine ⟨2411286896425185896803733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607524597616790597869155 2411286896425185896803733)
                  ·
                    refine ⟨113029073269930588912675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2411286896425185896803733 113029073269930588912675)
                    ·
                      rfl

theorem cell22_330185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_330185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330185 prefixEnd_330185 := by exact prefixLift 330185
  have htrace : WordTrace (prefixWord ++ tailWord_330185) baseStart_330185 baseEnd_330185 := by
    simpa [prefixWord, tailWord_330185, baseEnd_330185] using wordTrace_append hprefix tailTrace_330185
  have hstable : (prefixWord ++ tailWord_330185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330185).length < 2 ^ (prefixWord ++ tailWord_330185).sum := by decide
  have hdescent : baseEnd_330185 < baseStart_330185 := by decide
  rcases family_descends (prefixWord ++ tailWord_330185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330202 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_330202 : Nat := 118140960795 + 330202 * 2 ^ 59
def prefixEnd_330202 : Nat := 4983230072969 + 3 ^ 40 * 330202 * 2
def baseEnd_330202 : Nat := 113034892717348211237623

theorem tailTrace_330202 : CollatzResearch.WordTrace tailWord_330202 prefixEnd_330202 113034892717348211237623 := by
  unfold tailWord_330202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010864087435505714238215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8028970899828015237968573 3010864087435505714238215)
  ·
    refine ⟨4516296131153258571357323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3010864087435505714238215 4516296131153258571357323)
    ·
      refine ⟨6774444196729887857035985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4516296131153258571357323 6774444196729887857035985)
      ·
        refine ⟨5080833147547415892776989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6774444196729887857035985 5080833147547415892776989)
        ·
          refine ⟨1905312430330280959791371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5080833147547415892776989 1905312430330280959791371)
          ·
            refine ⟨2857968645495421439687057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905312430330280959791371 2857968645495421439687057)
            ·
              refine ⟨2143476484121566079765293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2857968645495421439687057 2143476484121566079765293)
              ·
                refine ⟨803803681545587279911985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2143476484121566079765293 803803681545587279911985)
                ·
                  refine ⟨602852761159190459933989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 803803681545587279911985 602852761159190459933989)
                  ·
                    refine ⟨113034892717348211237623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 602852761159190459933989 113034892717348211237623)
                    ·
                      rfl

theorem cell22_330202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_330202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330202 prefixEnd_330202 := by exact prefixLift 330202
  have htrace : WordTrace (prefixWord ++ tailWord_330202) baseStart_330202 baseEnd_330202 := by
    simpa [prefixWord, tailWord_330202, baseEnd_330202] using wordTrace_append hprefix tailTrace_330202
  have hstable : (prefixWord ++ tailWord_330202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330202).length < 2 ^ (prefixWord ++ tailWord_330202).sum := by decide
  have hdescent : baseEnd_330202 < baseStart_330202 := by decide
  rcases family_descends (prefixWord ++ tailWord_330202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330253 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_330253 : Nat := 118140960795 + 330253 * 2 ^ 59
def prefixEnd_330253 : Nat := 4983230072969 + 3 ^ 40 * 330253 * 2
def baseEnd_330253 : Nat := 113052351059601078212467

theorem tailTrace_330253 : CollatzResearch.WordTrace tailWord_330253 prefixEnd_330253 113052351059601078212467 := by
  unfold tailWord_330253
  simp only [CollatzResearch.WordTrace]
  refine ⟨12045316472557258567059413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8030210981704839044706275 12045316472557258567059413)
  ·
    refine ⟨282312104825560747665455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12045316472557258567059413 282312104825560747665455)
    ·
      refine ⟨423468157238341121498183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282312104825560747665455 423468157238341121498183)
      ·
        refine ⟨635202235857511682247275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423468157238341121498183 635202235857511682247275)
        ·
          refine ⟨952803353786267523370913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635202235857511682247275 952803353786267523370913)
          ·
            refine ⟨714602515339700642528185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952803353786267523370913 714602515339700642528185)
            ·
              refine ⟨535951886504775481896139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714602515339700642528185 535951886504775481896139)
              ·
                refine ⟨803927829757163222844209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535951886504775481896139 803927829757163222844209)
                ·
                  refine ⟨602945872317872417133157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 803927829757163222844209 602945872317872417133157)
                  ·
                    refine ⟨113052351059601078212467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 602945872317872417133157 113052351059601078212467)
                    ·
                      rfl

theorem cell22_330253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_330253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330253 prefixEnd_330253 := by exact prefixLift 330253
  have htrace : WordTrace (prefixWord ++ tailWord_330253) baseStart_330253 baseEnd_330253 := by
    simpa [prefixWord, tailWord_330253, baseEnd_330253] using wordTrace_append hprefix tailTrace_330253
  have hstable : (prefixWord ++ tailWord_330253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330253).length < 2 ^ (prefixWord ++ tailWord_330253).sum := by decide
  have hdescent : baseEnd_330253 < baseStart_330253 := by decide
  rcases family_descends (prefixWord ++ tailWord_330253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330285 : List Nat := [1, 5, 4, 1, 2, 1, 1, 7]
def baseStart_330285 : Nat := 118140960795 + 330285 * 2 ^ 59
def prefixEnd_330285 : Nat := 4983230072969 + 3 ^ 40 * 330285 * 2
def baseEnd_330285 : Nat := 12562589479284851268041

theorem tailTrace_330285 : CollatzResearch.WordTrace tailWord_330285 prefixEnd_330285 12562589479284851268041 := by
  unfold tailWord_330285
  simp only [CollatzResearch.WordTrace]
  refine ⟨12046483608441328032224309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8030989072294218688149539 12046483608441328032224309)
  ·
    refine ⟨1129357838291374503021029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12046483608441328032224309 1129357838291374503021029)
    ·
      refine ⟨211754594679632719316443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1129357838291374503021029 211754594679632719316443)
      ·
        refine ⟨317631892019449078974665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211754594679632719316443 317631892019449078974665)
        ·
          refine ⟨238223919014586809230999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317631892019449078974665 238223919014586809230999)
          ·
            refine ⟨357335878521880213846499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238223919014586809230999 357335878521880213846499)
            ·
              refine ⟨536003817782820320769749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357335878521880213846499 536003817782820320769749)
              ·
                refine ⟨12562589479284851268041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 536003817782820320769749 12562589479284851268041)
                ·
                  rfl

theorem cell22_330285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 7].length) (baseStart_330285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330285 prefixEnd_330285 := by exact prefixLift 330285
  have htrace : WordTrace (prefixWord ++ tailWord_330285) baseStart_330285 baseEnd_330285 := by
    simpa [prefixWord, tailWord_330285, baseEnd_330285] using wordTrace_append hprefix tailTrace_330285
  have hstable : (prefixWord ++ tailWord_330285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330285).length < 2 ^ (prefixWord ++ tailWord_330285).sum := by decide
  have hdescent : baseEnd_330285 < baseStart_330285 := by decide
  rcases family_descends (prefixWord ++ tailWord_330285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330294 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_330294 : Nat := 118140960795 + 330294 * 2 ^ 59
def prefixEnd_330294 : Nat := 4983230072969 + 3 ^ 40 * 330294 * 2
def baseEnd_330294 : Nat := 113066386197490637937341

theorem tailTrace_330294 : CollatzResearch.WordTrace tailWord_330294 prefixEnd_330294 113066386197490637937341 := by
  unfold tailWord_330294
  simp only [CollatzResearch.WordTrace]
  refine ⟨752925741588045160581371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8031207910272481712867957 752925741588045160581371)
  ·
    refine ⟨1129388612382067740872057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 752925741588045160581371 1129388612382067740872057)
    ·
      refine ⟨847041459286550805654043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1129388612382067740872057 847041459286550805654043)
      ·
        refine ⟨1270562188929826208481065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847041459286550805654043 1270562188929826208481065)
        ·
          refine ⟨952921641697369656360799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1270562188929826208481065 952921641697369656360799)
          ·
            refine ⟨1429382462546054484541199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952921641697369656360799 1429382462546054484541199)
            ·
              refine ⟨2144073693819081726811799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429382462546054484541199 2144073693819081726811799)
              ·
                refine ⟨3216110540728622590217699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144073693819081726811799 3216110540728622590217699)
                ·
                  refine ⟨4824165811092933885326549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216110540728622590217699 4824165811092933885326549)
                  ·
                    refine ⟨113066386197490637937341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4824165811092933885326549 113066386197490637937341)
                    ·
                      rfl

theorem cell22_330294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_330294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330294 prefixEnd_330294 := by exact prefixLift 330294
  have htrace : WordTrace (prefixWord ++ tailWord_330294) baseStart_330294 baseEnd_330294 := by
    simpa [prefixWord, tailWord_330294, baseEnd_330294] using wordTrace_append hprefix tailTrace_330294
  have hstable : (prefixWord ++ tailWord_330294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330294).length < 2 ^ (prefixWord ++ tailWord_330294).sum := by decide
  have hdescent : baseEnd_330294 < baseStart_330294 := by decide
  rcases family_descends (prefixWord ++ tailWord_330294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330339 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 4, 3]
def baseStart_330339 : Nat := 118140960795 + 330339 * 2 ^ 59
def prefixEnd_330339 : Nat := 4983230072969 + 3 ^ 40 * 330339 * 2
def baseEnd_330339 : Nat := 113081790617125520562203

theorem tailTrace_330339 : CollatzResearch.WordTrace tailWord_330339 prefixEnd_330339 113081790617125520562203 := by
  unfold tailWord_330339
  simp only [CollatzResearch.WordTrace]
  refine ⟨12048453150245695254690071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8032302100163796836460047 12048453150245695254690071)
  ·
    refine ⟨18072679725368542882035107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12048453150245695254690071 18072679725368542882035107)
    ·
      refine ⟨27109019588052814323052661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18072679725368542882035107 27109019588052814323052661)
      ·
        refine ⟨2541470586379951342786187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27109019588052814323052661 2541470586379951342786187)
        ·
          refine ⟨3812205879569927014179281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541470586379951342786187 3812205879569927014179281)
          ·
            refine ⟨2859154409677445260634461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3812205879569927014179281 2859154409677445260634461)
            ·
              refine ⟨1072182903629041972737923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2859154409677445260634461 1072182903629041972737923)
              ·
                refine ⟨1608274355443562959106885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072182903629041972737923 1608274355443562959106885)
                ·
                  refine ⟨301551441645668054832541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1608274355443562959106885 301551441645668054832541)
                  ·
                    refine ⟨113081790617125520562203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301551441645668054832541 113081790617125520562203)
                    ·
                      rfl

theorem cell22_330339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 3].length) (baseStart_330339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330339 prefixEnd_330339 := by exact prefixLift 330339
  have htrace : WordTrace (prefixWord ++ tailWord_330339) baseStart_330339 baseEnd_330339 := by
    simpa [prefixWord, tailWord_330339, baseEnd_330339] using wordTrace_append hprefix tailTrace_330339
  have hstable : (prefixWord ++ tailWord_330339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330339).length < 2 ^ (prefixWord ++ tailWord_330339).sum := by decide
  have hdescent : baseEnd_330339 < baseStart_330339 := by decide
  rcases family_descends (prefixWord ++ tailWord_330339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330407 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 2, 3]
def baseStart_330407 : Nat := 118140960795 + 330407 * 2 ^ 59
def prefixEnd_330407 : Nat := 4983230072969 + 3 ^ 40 * 330407 * 2
def baseEnd_330407 : Nat := 113105068406796009861995

theorem tailTrace_330407 : CollatzResearch.WordTrace tailWord_330407 prefixEnd_330407 113105068406796009861995 := by
  unfold tailWord_330407
  simp only [CollatzResearch.WordTrace]
  refine ⟨12050933313999342868165475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8033955542666228578776983 12050933313999342868165475)
  ·
    refine ⟨18076399970999014302248213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12050933313999342868165475 18076399970999014302248213)
    ·
      refine ⟨847331248640578795417885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18076399970999014302248213 847331248640578795417885)
      ·
        refine ⟨317749218240217048281707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 847331248640578795417885 317749218240217048281707)
        ·
          refine ⟨476623827360325572422561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317749218240217048281707 476623827360325572422561)
          ·
            refine ⟨357467870520244179316921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476623827360325572422561 357467870520244179316921)
            ·
              refine ⟨268100902890183134487691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357467870520244179316921 268100902890183134487691)
              ·
                refine ⟨402151354335274701731537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268100902890183134487691 402151354335274701731537)
                ·
                  refine ⟨301613515751456026298653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402151354335274701731537 301613515751456026298653)
                  ·
                    refine ⟨113105068406796009861995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301613515751456026298653 113105068406796009861995)
                    ·
                      rfl

theorem cell22_330407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_330407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330407 prefixEnd_330407 := by exact prefixLift 330407
  have htrace : WordTrace (prefixWord ++ tailWord_330407) baseStart_330407 baseEnd_330407 := by
    simpa [prefixWord, tailWord_330407, baseEnd_330407] using wordTrace_append hprefix tailTrace_330407
  have hstable : (prefixWord ++ tailWord_330407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330407).length < 2 ^ (prefixWord ++ tailWord_330407).sum := by decide
  have hdescent : baseEnd_330407 < baseStart_330407 := by decide
  rcases family_descends (prefixWord ++ tailWord_330407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330504 : List Nat := [2, 1, 3, 2, 2, 3, 9]
def baseStart_330504 : Nat := 118140960795 + 330504 * 2 ^ 59
def prefixEnd_330504 : Nat := 4983230072969 + 3 ^ 40 * 330504 * 2
def baseEnd_330504 : Nat := 4190306425522966303211

theorem tailTrace_330504 : CollatzResearch.WordTrace tailWord_330504 prefixEnd_330504 4190306425522966303211 := by
  unfold tailWord_330504
  simp only [CollatzResearch.WordTrace]
  refine ⟨6027235597323964217223283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8036314129765285622964377 6027235597323964217223283)
  ·
    refine ⟨9040853395985946325834925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6027235597323964217223283 9040853395985946325834925)
    ·
      refine ⟨3390320023494729872188097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9040853395985946325834925 3390320023494729872188097)
      ·
        refine ⟨2542740017621047404141073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3390320023494729872188097 2542740017621047404141073)
        ·
          refine ⟨1907055013215785553105805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2542740017621047404141073 1907055013215785553105805)
          ·
            refine ⟨715145629955919582414677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1907055013215785553105805 715145629955919582414677)
            ·
              refine ⟨4190306425522966303211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 715145629955919582414677 4190306425522966303211)
              ·
                rfl

theorem cell22_330504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 9].length) (baseStart_330504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330504 prefixEnd_330504 := by exact prefixLift 330504
  have htrace : WordTrace (prefixWord ++ tailWord_330504) baseStart_330504 baseEnd_330504 := by
    simpa [prefixWord, tailWord_330504, baseEnd_330504] using wordTrace_append hprefix tailTrace_330504
  have hstable : (prefixWord ++ tailWord_330504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330504).length < 2 ^ (prefixWord ++ tailWord_330504).sum := by decide
  have hdescent : baseEnd_330504 < baseStart_330504 := by decide
  rcases family_descends (prefixWord ++ tailWord_330504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330525 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_330525 : Nat := 118140960795 + 330525 * 2 ^ 59
def prefixEnd_330525 : Nat := 4983230072969 + 3 ^ 40 * 330525 * 2
def baseEnd_330525 : Nat := 113145462218283035411633

theorem tailTrace_330525 : CollatzResearch.WordTrace tailWord_330525 prefixEnd_330525 113145462218283035411633 := by
  unfold tailWord_330525
  simp only [CollatzResearch.WordTrace]
  refine ⟨12055237127571849020961029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8036824751714566013974019 12055237127571849020961029)
  ·
    refine ⟨2260356961419721691430193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12055237127571849020961029 2260356961419721691430193)
    ·
      refine ⟨1695267721064791268572645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2260356961419721691430193 1695267721064791268572645)
      ·
        refine ⟨317862697699648362857371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1695267721064791268572645 317862697699648362857371)
        ·
          refine ⟨476794046549472544286057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317862697699648362857371 476794046549472544286057)
          ·
            refine ⟨357595534912104408214543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476794046549472544286057 357595534912104408214543)
            ·
              refine ⟨536393302368156612321815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357595534912104408214543 536393302368156612321815)
              ·
                refine ⟨804589953552234918482723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536393302368156612321815 804589953552234918482723)
                ·
                  refine ⟨1206884930328352377724085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804589953552234918482723 1206884930328352377724085)
                  ·
                    refine ⟨113145462218283035411633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1206884930328352377724085 113145462218283035411633)
                    ·
                      rfl

theorem cell22_330525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_330525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330525 prefixEnd_330525 := by exact prefixLift 330525
  have htrace : WordTrace (prefixWord ++ tailWord_330525) baseStart_330525 baseEnd_330525 := by
    simpa [prefixWord, tailWord_330525, baseEnd_330525] using wordTrace_append hprefix tailTrace_330525
  have hstable : (prefixWord ++ tailWord_330525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330525).length < 2 ^ (prefixWord ++ tailWord_330525).sum := by decide
  have hdescent : baseEnd_330525 < baseStart_330525 := by decide
  rcases family_descends (prefixWord ++ tailWord_330525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330538 : List Nat := [3, 1, 4, 3, 1, 1, 1, 8]
def baseStart_330538 : Nat := 118140960795 + 330538 * 2 ^ 59
def prefixEnd_330538 : Nat := 4983230072969 + 3 ^ 40 * 330538 * 2
def baseEnd_330538 : Nat := 12572212487106148315177

theorem tailTrace_330538 : CollatzResearch.WordTrace tailWord_330538 prefixEnd_330538 12572212487106148315177 := by
  unfold tailWord_330538
  simp only [CollatzResearch.WordTrace]
  refine ⟨3013927819131188060296067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8037140851016501494122845 3013927819131188060296067)
  ·
    refine ⟨4520891728696782090444101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3013927819131188060296067 4520891728696782090444101)
    ·
      refine ⟨847667199130646641958269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4520891728696782090444101 847667199130646641958269)
      ·
        refine ⟨317875199673992490734351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 847667199130646641958269 317875199673992490734351)
        ·
          refine ⟨476812799510988736101527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317875199673992490734351 476812799510988736101527)
          ·
            refine ⟨715219199266483104152291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476812799510988736101527 715219199266483104152291)
            ·
              refine ⟨1072828798899724656228437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715219199266483104152291 1072828798899724656228437)
              ·
                refine ⟨12572212487106148315177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1072828798899724656228437 12572212487106148315177)
                ·
                  rfl

theorem cell22_330538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_330538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330538 prefixEnd_330538 := by exact prefixLift 330538
  have htrace : WordTrace (prefixWord ++ tailWord_330538) baseStart_330538 baseEnd_330538 := by
    simpa [prefixWord, tailWord_330538, baseEnd_330538] using wordTrace_append hprefix tailTrace_330538
  have hstable : (prefixWord ++ tailWord_330538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330538).length < 2 ^ (prefixWord ++ tailWord_330538).sum := by decide
  have hdescent : baseEnd_330538 < baseStart_330538 := by decide
  rcases family_descends (prefixWord ++ tailWord_330538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330583 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 5]
def baseStart_330583 : Nat := 118140960795 + 330583 * 2 ^ 59
def prefixEnd_330583 : Nat := 4983230072969 + 3 ^ 40 * 330583 * 2
def baseEnd_330583 : Nat := 37721772267863405820485

theorem tailTrace_330583 : CollatzResearch.WordTrace tailWord_330583 prefixEnd_330583 37721772267863405820485 := by
  unfold tailWord_330583
  simp only [CollatzResearch.WordTrace]
  refine ⟨12057352561361724926572403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8038235040907816617714935 12057352561361724926572403)
  ·
    refine ⟨18086028842042587389858605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12057352561361724926572403 18086028842042587389858605)
    ·
      refine ⟨6782260815765970271196977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18086028842042587389858605 6782260815765970271196977)
      ·
        refine ⟨5086695611824477703397733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6782260815765970271196977 5086695611824477703397733)
        ·
          refine ⟨953755427217089569387075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5086695611824477703397733 953755427217089569387075)
          ·
            refine ⟨1430633140825634354080613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953755427217089569387075 1430633140825634354080613)
            ·
              refine ⟨268243713904806441390115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1430633140825634354080613 268243713904806441390115)
              ·
                refine ⟨402365570857209662085173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268243713904806441390115 402365570857209662085173)
                ·
                  refine ⟨37721772267863405820485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 402365570857209662085173 37721772267863405820485)
                  ·
                    rfl

theorem cell22_330583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 5].length) (baseStart_330583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330583 prefixEnd_330583 := by exact prefixLift 330583
  have htrace : WordTrace (prefixWord ++ tailWord_330583) baseStart_330583 baseEnd_330583 := by
    simpa [prefixWord, tailWord_330583, baseEnd_330583] using wordTrace_append hprefix tailTrace_330583
  have hstable : (prefixWord ++ tailWord_330583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330583).length < 2 ^ (prefixWord ++ tailWord_330583).sum := by decide
  have hdescent : baseEnd_330583 < baseStart_330583 := by decide
  rcases family_descends (prefixWord ++ tailWord_330583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330658 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_330658 : Nat := 118140960795 + 330658 * 2 ^ 59
def prefixEnd_330658 : Nat := 4983230072969 + 3 ^ 40 * 330658 * 2
def baseEnd_330658 : Nat := 113190990836315021836225

theorem tailTrace_330658 : CollatzResearch.WordTrace tailWord_330658 prefixEnd_330658 113190990836315021836225 := by
  unfold tailWord_330658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3015022009022503183888157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8040058690726675157035085 3015022009022503183888157)
  ·
    refine ⟨1130633253383438693958059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3015022009022503183888157 1130633253383438693958059)
    ·
      refine ⟨1695949880075158040937089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1130633253383438693958059 1695949880075158040937089)
      ·
        refine ⟨1271962410056368530702817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1695949880075158040937089 1271962410056368530702817)
        ·
          refine ⟨953971807542276398027113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1271962410056368530702817 953971807542276398027113)
          ·
            refine ⟨715478855656707298520335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 953971807542276398027113 715478855656707298520335)
            ·
              refine ⟨1073218283485060947780503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715478855656707298520335 1073218283485060947780503)
              ·
                refine ⟨1609827425227591421670755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073218283485060947780503 1609827425227591421670755)
                ·
                  refine ⟨2414741137841387132506133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609827425227591421670755 2414741137841387132506133)
                  ·
                    refine ⟨113190990836315021836225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2414741137841387132506133 113190990836315021836225)
                    ·
                      rfl

theorem cell22_330658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_330658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330658 prefixEnd_330658 := by exact prefixLift 330658
  have htrace : WordTrace (prefixWord ++ tailWord_330658) baseStart_330658 baseEnd_330658 := by
    simpa [prefixWord, tailWord_330658, baseEnd_330658] using wordTrace_append hprefix tailTrace_330658
  have hstable : (prefixWord ++ tailWord_330658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330658).length < 2 ^ (prefixWord ++ tailWord_330658).sum := by decide
  have hdescent : baseEnd_330658 < baseStart_330658 := by decide
  rcases family_descends (prefixWord ++ tailWord_330658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330688 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 3, 3]
def baseStart_330688 : Nat := 118140960795 + 330688 * 2 ^ 59
def prefixEnd_330688 : Nat := 4983230072969 + 3 ^ 40 * 330688 * 2
def baseEnd_330688 : Nat := 113201260449404943586133

theorem tailTrace_330688 : CollatzResearch.WordTrace tailWord_330688 prefixEnd_330688 113201260449404943586133 := by
  unfold tailWord_330688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6030591112990663929572359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8040788150654218572763145 6030591112990663929572359)
  ·
    refine ⟨9045886669485995894358539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6030591112990663929572359 9045886669485995894358539)
    ·
      refine ⟨13568830004228993841537809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9045886669485995894358539 13568830004228993841537809)
      ·
        refine ⟨10176622503171745381153357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13568830004228993841537809 10176622503171745381153357)
        ·
          refine ⟨3816233438689404517932509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10176622503171745381153357 3816233438689404517932509)
          ·
            refine ⟨1431087539508526694224691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3816233438689404517932509 1431087539508526694224691)
            ·
              refine ⟨2146631309262790041337037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1431087539508526694224691 2146631309262790041337037)
              ·
                refine ⟨804986740973546265501389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2146631309262790041337037 804986740973546265501389)
                ·
                  refine ⟨301870027865079849563021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804986740973546265501389 301870027865079849563021)
                  ·
                    refine ⟨113201260449404943586133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301870027865079849563021 113201260449404943586133)
                    ·
                      rfl

theorem cell22_330688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3, 3].length) (baseStart_330688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330688 prefixEnd_330688 := by exact prefixLift 330688
  have htrace : WordTrace (prefixWord ++ tailWord_330688) baseStart_330688 baseEnd_330688 := by
    simpa [prefixWord, tailWord_330688, baseEnd_330688] using wordTrace_append hprefix tailTrace_330688
  have hstable : (prefixWord ++ tailWord_330688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330688).length < 2 ^ (prefixWord ++ tailWord_330688).sum := by decide
  have hdescent : baseEnd_330688 < baseStart_330688 := by decide
  rcases family_descends (prefixWord ++ tailWord_330688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330731 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 7, 4]
def baseStart_330731 : Nat := 118140960795 + 330731 * 2 ^ 59
def prefixEnd_330731 : Nat := 4983230072969 + 3 ^ 40 * 330731 * 2
def baseEnd_330731 : Nat := 113215980228167164761001

theorem tailTrace_330731 : CollatzResearch.WordTrace tailWord_330731 prefixEnd_330731 113215980228167164761001 := by
  unfold tailWord_330731
  simp only [CollatzResearch.WordTrace]
  refine ⟨12062750564825546202960047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8041833709883697468640031 12062750564825546202960047)
  ·
    refine ⟨18094125847238319304440071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12062750564825546202960047 18094125847238319304440071)
    ·
      refine ⟨27141188770857478956660107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18094125847238319304440071 27141188770857478956660107)
      ·
        refine ⟨40711783156286218434990161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27141188770857478956660107 40711783156286218434990161)
        ·
          refine ⟨30533837367214663826242621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40711783156286218434990161 30533837367214663826242621)
          ·
            refine ⟨11450189012705498934840983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30533837367214663826242621 11450189012705498934840983)
            ·
              refine ⟨17175283519058248402261475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11450189012705498934840983 17175283519058248402261475)
              ·
                refine ⟨25762925278587372603392213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17175283519058248402261475 25762925278587372603392213)
                ·
                  refine ⟨603818561216891545392005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 25762925278587372603392213 603818561216891545392005)
                  ·
                    refine ⟨113215980228167164761001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 603818561216891545392005 113215980228167164761001)
                    ·
                      rfl

theorem cell22_330731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 4].length) (baseStart_330731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330731 prefixEnd_330731 := by exact prefixLift 330731
  have htrace : WordTrace (prefixWord ++ tailWord_330731) baseStart_330731 baseEnd_330731 := by
    simpa [prefixWord, tailWord_330731, baseEnd_330731] using wordTrace_append hprefix tailTrace_330731
  have hstable : (prefixWord ++ tailWord_330731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330731).length < 2 ^ (prefixWord ++ tailWord_330731).sum := by decide
  have hdescent : baseEnd_330731 < baseStart_330731 := by decide
  rcases family_descends (prefixWord ++ tailWord_330731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330761 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_330761 : Nat := 118140960795 + 330761 * 2 ^ 59
def prefixEnd_330761 : Nat := 4983230072969 + 3 ^ 40 * 330761 * 2
def baseEnd_330761 : Nat := 113226249841257086510909

theorem tailTrace_330761 : CollatzResearch.WordTrace tailWord_330761 prefixEnd_330761 113226249841257086510909 := by
  unfold tailWord_330761
  simp only [CollatzResearch.WordTrace]
  refine ⟨12063844754716861326552137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8042563169811240884368091 12063844754716861326552137)
  ·
    refine ⟨9047883566037645994914103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12063844754716861326552137 9047883566037645994914103)
    ·
      refine ⟨13571825349056468992371155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9047883566037645994914103 13571825349056468992371155)
      ·
        refine ⟨20357738023584703488556733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13571825349056468992371155 20357738023584703488556733)
        ·
          refine ⟨7634151758844263808208775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20357738023584703488556733 7634151758844263808208775)
          ·
            refine ⟨11451227638266395712313163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7634151758844263808208775 11451227638266395712313163)
            ·
              refine ⟨17176841457399593568469745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11451227638266395712313163 17176841457399593568469745)
              ·
                refine ⟨12882631093049695176352309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17176841457399593568469745 12882631093049695176352309)
                ·
                  refine ⟨1207746664973408922783029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12882631093049695176352309 1207746664973408922783029)
                  ·
                    refine ⟨113226249841257086510909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1207746664973408922783029 113226249841257086510909)
                    ·
                      rfl

theorem cell22_330761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_330761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330761 prefixEnd_330761 := by exact prefixLift 330761
  have htrace : WordTrace (prefixWord ++ tailWord_330761) baseStart_330761 baseEnd_330761 := by
    simpa [prefixWord, tailWord_330761, baseEnd_330761] using wordTrace_append hprefix tailTrace_330761
  have hstable : (prefixWord ++ tailWord_330761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330761).length < 2 ^ (prefixWord ++ tailWord_330761).sum := by decide
  have hdescent : baseEnd_330761 < baseStart_330761 := by decide
  rcases family_descends (prefixWord ++ tailWord_330761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330778 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_330778 : Nat := 118140960795 + 330778 * 2 ^ 59
def prefixEnd_330778 : Nat := 4983230072969 + 3 ^ 40 * 330778 * 2
def baseEnd_330778 : Nat := 113232069288674708835857

theorem tailTrace_330778 : CollatzResearch.WordTrace tailWord_330778 prefixEnd_330778 113232069288674708835857 := by
  unfold tailWord_330778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016116198913818307480247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8042976530436848819947325 3016116198913818307480247)
  ·
    refine ⟨4524174298370727461220371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3016116198913818307480247 4524174298370727461220371)
    ·
      refine ⟨6786261447556091191830557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4524174298370727461220371 6786261447556091191830557)
      ·
        refine ⟨2544848042833534196936459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6786261447556091191830557 2544848042833534196936459)
        ·
          refine ⟨3817272064250301295404689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2544848042833534196936459 3817272064250301295404689)
          ·
            refine ⟨2862954048187725971553517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3817272064250301295404689 2862954048187725971553517)
            ·
              refine ⟨1073607768070397239332569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2862954048187725971553517 1073607768070397239332569)
              ·
                refine ⟨805205826052797929499427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1073607768070397239332569 805205826052797929499427)
                ·
                  refine ⟨1207808739079196894249141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805205826052797929499427 1207808739079196894249141)
                  ·
                    refine ⟨113232069288674708835857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1207808739079196894249141 113232069288674708835857)
                    ·
                      rfl

theorem cell22_330778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_330778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330778 prefixEnd_330778 := by exact prefixLift 330778
  have htrace : WordTrace (prefixWord ++ tailWord_330778) baseStart_330778 baseEnd_330778 := by
    simpa [prefixWord, tailWord_330778, baseEnd_330778] using wordTrace_append hprefix tailTrace_330778
  have hstable : (prefixWord ++ tailWord_330778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330778).length < 2 ^ (prefixWord ++ tailWord_330778).sum := by decide
  have hdescent : baseEnd_330778 < baseStart_330778 := by decide
  rcases family_descends (prefixWord ++ tailWord_330778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330795 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 2, 3]
def baseStart_330795 : Nat := 118140960795 + 330795 * 2 ^ 59
def prefixEnd_330795 : Nat := 4983230072969 + 3 ^ 40 * 330795 * 2
def baseEnd_330795 : Nat := 113237888736092331160805

theorem tailTrace_330795 : CollatzResearch.WordTrace tailWord_330795 prefixEnd_330795 113237888736092331160805 := by
  unfold tailWord_330795
  simp only [CollatzResearch.WordTrace]
  refine ⟨12065084836593685133289839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8043389891062456755526559 12065084836593685133289839)
  ·
    refine ⟨18097627254890527699934759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12065084836593685133289839 18097627254890527699934759)
    ·
      refine ⟨27146440882335791549902139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18097627254890527699934759 27146440882335791549902139)
      ·
        refine ⟨40719661323503687324853209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27146440882335791549902139 40719661323503687324853209)
        ·
          refine ⟨30539745992627765493639907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40719661323503687324853209 30539745992627765493639907)
          ·
            refine ⟨45809618988941648240459861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30539745992627765493639907 45809618988941648240459861)
            ·
              refine ⟨536831472526659940317889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 45809618988941648240459861 536831472526659940317889)
              ·
                refine ⟨402623604394994955238417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536831472526659940317889 402623604394994955238417)
                ·
                  refine ⟨301967703296246216428813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402623604394994955238417 301967703296246216428813)
                  ·
                    refine ⟨113237888736092331160805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301967703296246216428813 113237888736092331160805)
                    ·
                      rfl

theorem cell22_330795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 3].length) (baseStart_330795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330795 prefixEnd_330795 := by exact prefixLift 330795
  have htrace : WordTrace (prefixWord ++ tailWord_330795) baseStart_330795 baseEnd_330795 := by
    simpa [prefixWord, tailWord_330795, baseEnd_330795] using wordTrace_append hprefix tailTrace_330795
  have hstable : (prefixWord ++ tailWord_330795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330795).length < 2 ^ (prefixWord ++ tailWord_330795).sum := by decide
  have hdescent : baseEnd_330795 < baseStart_330795 := by decide
  rcases family_descends (prefixWord ++ tailWord_330795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330808 : List Nat := [2, 1, 2, 1, 5, 1, 3, 7]
def baseStart_330808 : Nat := 118140960795 + 330808 * 2 ^ 59
def prefixEnd_330808 : Nat := 4983230072969 + 3 ^ 40 * 330808 * 2
def baseEnd_330808 : Nat := 12582482100196070065085

theorem tailTrace_330808 : CollatzResearch.WordTrace tailWord_330808 prefixEnd_330808 12582482100196070065085 := by
  unfold tailWord_330808
  simp only [CollatzResearch.WordTrace]
  refine ⟨6032779492773294176756539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8043705990364392235675385 6032779492773294176756539)
  ·
    refine ⟨9049169239159941265134809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6032779492773294176756539 9049169239159941265134809)
    ·
      refine ⟨6786876929369955948851107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9049169239159941265134809 6786876929369955948851107)
      ·
        refine ⟨10180315394054933923276661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6786876929369955948851107 10180315394054933923276661)
        ·
          refine ⟨954404568192650055307187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10180315394054933923276661 954404568192650055307187)
          ·
            refine ⟨1431606852288975082960781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954404568192650055307187 1431606852288975082960781)
            ·
              refine ⟨536852569608365656110293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1431606852288975082960781 536852569608365656110293)
              ·
                refine ⟨12582482100196070065085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 536852569608365656110293 12582482100196070065085)
                ·
                  rfl

theorem cell22_330808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 7].length) (baseStart_330808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330808 prefixEnd_330808 := by exact prefixLift 330808
  have htrace : WordTrace (prefixWord ++ tailWord_330808) baseStart_330808 baseEnd_330808 := by
    simpa [prefixWord, tailWord_330808, baseEnd_330808] using wordTrace_append hprefix tailTrace_330808
  have hstable : (prefixWord ++ tailWord_330808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330808).length < 2 ^ (prefixWord ++ tailWord_330808).sum := by decide
  have hdescent : baseEnd_330808 < baseStart_330808 := by decide
  rcases family_descends (prefixWord ++ tailWord_330808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330846 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_330846 : Nat := 118140960795 + 330846 * 2 ^ 59
def prefixEnd_330846 : Nat := 4983230072969 + 3 ^ 40 * 330846 * 2
def baseEnd_330846 : Nat := 113255347078345198135649

theorem tailTrace_330846 : CollatzResearch.WordTrace tailWord_330846 prefixEnd_330846 113255347078345198135649 := by
  unfold tailWord_330846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508368119926115105424549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8044629972939280562264261 1508368119926115105424549)
  ·
    refine ⟨282819022486146582267103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1508368119926115105424549 282819022486146582267103)
    ·
      refine ⟨424228533729219873400655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282819022486146582267103 424228533729219873400655)
      ·
        refine ⟨636342800593829810100983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424228533729219873400655 636342800593829810100983)
        ·
          refine ⟨954514200890744715151475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636342800593829810100983 954514200890744715151475)
          ·
            refine ⟨1431771301336117072727213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954514200890744715151475 1431771301336117072727213)
            ·
              refine ⟨536914238001043902272705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1431771301336117072727213 536914238001043902272705)
              ·
                refine ⟨402685678500782926704529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536914238001043902272705 402685678500782926704529)
                ·
                  refine ⟨302014258875587195028397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402685678500782926704529 302014258875587195028397)
                  ·
                    refine ⟨113255347078345198135649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 302014258875587195028397 113255347078345198135649)
                    ·
                      rfl

theorem cell22_330846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_330846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330846 prefixEnd_330846 := by exact prefixLift 330846
  have htrace : WordTrace (prefixWord ++ tailWord_330846) baseStart_330846 baseEnd_330846 := by
    simpa [prefixWord, tailWord_330846, baseEnd_330846] using wordTrace_append hprefix tailTrace_330846
  have hstable : (prefixWord ++ tailWord_330846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330846).length < 2 ^ (prefixWord ++ tailWord_330846).sum := by decide
  have hdescent : baseEnd_330846 < baseStart_330846 := by decide
  rcases family_descends (prefixWord ++ tailWord_330846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330853 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 7]
def baseStart_330853 : Nat := 118140960795 + 330853 * 2 ^ 59
def prefixEnd_330853 : Nat := 4983230072969 + 3 ^ 40 * 330853 * 2
def baseEnd_330853 : Nat := 37752581107133171070209

theorem tailTrace_330853 : CollatzResearch.WordTrace tailWord_330853 prefixEnd_330853 37752581107133171070209 := by
  unfold tailWord_330853
  simp only [CollatzResearch.WordTrace]
  refine ⟨12067200270383561038901213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8044800180255707359267475 12067200270383561038901213)
  ·
    refine ⟨4525200101393835389587955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12067200270383561038901213 4525200101393835389587955)
    ·
      refine ⟨6787800152090753084381933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4525200101393835389587955 6787800152090753084381933)
      ·
        refine ⟨2545425057034032406643225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6787800152090753084381933 2545425057034032406643225)
        ·
          refine ⟨1909068792775524304982419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2545425057034032406643225 1909068792775524304982419)
          ·
            refine ⟨2863603189163286457473629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909068792775524304982419 2863603189163286457473629)
            ·
              refine ⟨1073851195936232421552611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2863603189163286457473629 1073851195936232421552611)
              ·
                refine ⟨1610776793904348632328917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073851195936232421552611 1610776793904348632328917)
                ·
                  refine ⟨37752581107133171070209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1610776793904348632328917 37752581107133171070209)
                  ·
                    rfl

theorem cell22_330853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_330853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330853 prefixEnd_330853 := by exact prefixLift 330853
  have htrace : WordTrace (prefixWord ++ tailWord_330853) baseStart_330853 baseEnd_330853 := by
    simpa [prefixWord, tailWord_330853, baseEnd_330853] using wordTrace_append hprefix tailTrace_330853
  have hstable : (prefixWord ++ tailWord_330853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330853).length < 2 ^ (prefixWord ++ tailWord_330853).sum := by decide
  have hdescent : baseEnd_330853 < baseStart_330853 := by decide
  rcases family_descends (prefixWord ++ tailWord_330853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330857 : List Nat := [1, 2, 1, 1, 1, 6, 2, 4, 1, 3]
def baseStart_330857 : Nat := 118140960795 + 330857 * 2 ^ 59
def prefixEnd_330857 : Nat := 4983230072969 + 3 ^ 40 * 330857 * 2
def baseEnd_330857 : Nat := 113259112603144836110615

theorem tailTrace_330857 : CollatzResearch.WordTrace tailWord_330857 prefixEnd_330857 113259112603144836110615 := by
  unfold tailWord_330857
  simp only [CollatzResearch.WordTrace]
  refine ⟨12067346162369069722046825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8044897441579379814697883 12067346162369069722046825)
  ·
    refine ⟨9050509621776802291535119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12067346162369069722046825 9050509621776802291535119)
    ·
      refine ⟨13575764432665203437302679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9050509621776802291535119 13575764432665203437302679)
      ·
        refine ⟨20363646648997805155954019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13575764432665203437302679 20363646648997805155954019)
        ·
          refine ⟨30545469973496707733931029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20363646648997805155954019 30545469973496707733931029)
          ·
            refine ⟨1431818905007658175028017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30545469973496707733931029 1431818905007658175028017)
            ·
              refine ⟨1073864178755743631271013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1431818905007658175028017 1073864178755743631271013)
              ·
                refine ⟨201349533516701930863315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1073864178755743631271013 201349533516701930863315)
                ·
                  refine ⟨302024300275052896294973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201349533516701930863315 302024300275052896294973)
                  ·
                    refine ⟨113259112603144836110615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 302024300275052896294973 113259112603144836110615)
                    ·
                      rfl

theorem cell22_330857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 1, 3].length) (baseStart_330857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330857 prefixEnd_330857 := by exact prefixLift 330857
  have htrace : WordTrace (prefixWord ++ tailWord_330857) baseStart_330857 baseEnd_330857 := by
    simpa [prefixWord, tailWord_330857, baseEnd_330857] using wordTrace_append hprefix tailTrace_330857
  have hstable : (prefixWord ++ tailWord_330857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330857).length < 2 ^ (prefixWord ++ tailWord_330857).sum := by decide
  have hdescent : baseEnd_330857 < baseStart_330857 := by decide
  rcases family_descends (prefixWord ++ tailWord_330857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330915 : List Nat := [1, 1, 1, 4, 1, 1, 1, 8, 4]
def baseStart_330915 : Nat := 118140960795 + 330915 * 2 ^ 59
def prefixEnd_330915 : Nat := 4983230072969 + 3 ^ 40 * 330915 * 2
def baseEnd_330915 : Nat := 37759655729484006053479

theorem tailTrace_330915 : CollatzResearch.WordTrace tailWord_330915 prefixEnd_330915 37759655729484006053479 := by
  unfold tailWord_330915
  simp only [CollatzResearch.WordTrace]
  refine ⟨12069461596158945627658199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8046307730772630418438799 12069461596158945627658199)
  ·
    refine ⟨18104192394238418441487299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12069461596158945627658199 18104192394238418441487299)
    ·
      refine ⟨27156288591357627662230949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18104192394238418441487299 27156288591357627662230949)
      ·
        refine ⟨5091804110879555186668303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27156288591357627662230949 5091804110879555186668303)
        ·
          refine ⟨7637706166319332780002455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5091804110879555186668303 7637706166319332780002455)
          ·
            refine ⟨11456559249478999170003683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7637706166319332780002455 11456559249478999170003683)
            ·
              refine ⟨17184838874218498755005525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11456559249478999170003683 17184838874218498755005525)
              ·
                refine ⟨201384830557248032285221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 17184838874218498755005525 201384830557248032285221)
                ·
                  refine ⟨37759655729484006053479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201384830557248032285221 37759655729484006053479)
                  ·
                    rfl

theorem cell22_330915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 4].length) (baseStart_330915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330915 prefixEnd_330915 := by exact prefixLift 330915
  have htrace : WordTrace (prefixWord ++ tailWord_330915) baseStart_330915 baseEnd_330915 := by
    simpa [prefixWord, tailWord_330915, baseEnd_330915] using wordTrace_append hprefix tailTrace_330915
  have hstable : (prefixWord ++ tailWord_330915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330915).length < 2 ^ (prefixWord ++ tailWord_330915).sum := by decide
  have hdescent : baseEnd_330915 < baseStart_330915 := by decide
  rcases family_descends (prefixWord ++ tailWord_330915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330943 : List Nat := [1, 1, 2, 2, 2, 2, 4, 8]
def baseStart_330943 : Nat := 118140960795 + 330943 * 2 ^ 59
def prefixEnd_330943 : Nat := 4983230072969 + 3 ^ 40 * 330943 * 2
def baseEnd_330943 : Nat := 12587616906741030940039

theorem tailTrace_330943 : CollatzResearch.WordTrace tailWord_330943 prefixEnd_330943 12587616906741030940039 := by
  unfold tailWord_330943
  simp only [CollatzResearch.WordTrace]
  refine ⟨12070482840057506409677483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8046988560038337606451655 12070482840057506409677483)
  ·
    refine ⟨18105724260086259614516225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12070482840057506409677483 18105724260086259614516225)
    ·
      refine ⟨13579293195064694710887169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18105724260086259614516225 13579293195064694710887169)
      ·
        refine ⟨10184469896298521033165377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13579293195064694710887169 10184469896298521033165377)
        ·
          refine ⟨7638352422223890774874033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10184469896298521033165377 7638352422223890774874033)
          ·
            refine ⟨5728764316667918081155525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7638352422223890774874033 5728764316667918081155525)
            ·
              refine ⟨1074143309375234640216661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5728764316667918081155525 1074143309375234640216661)
              ·
                refine ⟨12587616906741030940039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1074143309375234640216661 12587616906741030940039)
                ·
                  rfl

theorem cell22_330943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 8].length) (baseStart_330943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330943 prefixEnd_330943 := by exact prefixLift 330943
  have htrace : WordTrace (prefixWord ++ tailWord_330943) baseStart_330943 baseEnd_330943 := by
    simpa [prefixWord, tailWord_330943, baseEnd_330943] using wordTrace_append hprefix tailTrace_330943
  have hstable : (prefixWord ++ tailWord_330943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330943).length < 2 ^ (prefixWord ++ tailWord_330943).sum := by decide
  have hdescent : baseEnd_330943 < baseStart_330943 := by decide
  rcases family_descends (prefixWord ++ tailWord_330943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330966 : List Nat := [5, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_330966 : Nat := 118140960795 + 330966 * 2 ^ 59
def prefixEnd_330966 : Nat := 4983230072969 + 3 ^ 40 * 330966 * 2
def baseEnd_330966 : Nat := 37765475176901628378427

theorem tailTrace_330966 : CollatzResearch.WordTrace tailWord_330966 prefixEnd_330966 37765475176901628378427 := by
  unfold tailWord_330966
  simp only [CollatzResearch.WordTrace]
  refine ⟨754457607435886333610297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8047547812649454225176501 754457607435886333610297)
  ·
    refine ⟨565843205576914750207723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 754457607435886333610297 565843205576914750207723)
    ·
      refine ⟨848764808365372125311585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565843205576914750207723 848764808365372125311585)
      ·
        refine ⟨636573606274029093983689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 848764808365372125311585 636573606274029093983689)
        ·
          refine ⟨477430204705521820487767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636573606274029093983689 477430204705521820487767)
          ·
            refine ⟨716145307058282730731651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477430204705521820487767 716145307058282730731651)
            ·
              refine ⟨1074217960587424096097477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716145307058282730731651 1074217960587424096097477)
              ·
                refine ⟨201415867610142018018277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1074217960587424096097477 201415867610142018018277)
                ·
                  refine ⟨37765475176901628378427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201415867610142018018277 37765475176901628378427)
                  ·
                    rfl

theorem cell22_330966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_330966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330966 prefixEnd_330966 := by exact prefixLift 330966
  have htrace : WordTrace (prefixWord ++ tailWord_330966) baseStart_330966 baseEnd_330966 := by
    simpa [prefixWord, tailWord_330966, baseEnd_330966] using wordTrace_append hprefix tailTrace_330966
  have hstable : (prefixWord ++ tailWord_330966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330966).length < 2 ^ (prefixWord ++ tailWord_330966).sum := by decide
  have hdescent : baseEnd_330966 < baseStart_330966 := by decide
  rcases family_descends (prefixWord ++ tailWord_330966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330996 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_330996 : Nat := 118140960795 + 330996 * 2 ^ 59
def prefixEnd_330996 : Nat := 4983230072969 + 3 ^ 40 * 330996 * 2
def baseEnd_330996 : Nat := 113306695143794806885189

theorem tailTrace_330996 : CollatzResearch.WordTrace tailWord_330996 prefixEnd_330996 113306695143794806885189 := by
  unfold tailWord_330996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6036207954432748230678421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8048277272576997640904561 6036207954432748230678421)
  ·
    refine ⟨282947247864035073313051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6036207954432748230678421 282947247864035073313051)
    ·
      refine ⟨424420871796052609969577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282947247864035073313051 424420871796052609969577)
      ·
        refine ⟨318315653847039457477183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424420871796052609969577 318315653847039457477183)
        ·
          refine ⟨477473480770559186215775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318315653847039457477183 477473480770559186215775)
          ·
            refine ⟨716210221155838779323663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477473480770559186215775 716210221155838779323663)
            ·
              refine ⟨1074315331733758168985495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716210221155838779323663 1074315331733758168985495)
              ·
                refine ⟨1611472997600637253478243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074315331733758168985495 1611472997600637253478243)
                ·
                  refine ⟨2417209496400955880217365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1611472997600637253478243 2417209496400955880217365)
                  ·
                    refine ⟨113306695143794806885189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2417209496400955880217365 113306695143794806885189)
                    ·
                      rfl

theorem cell22_330996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_330996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_330996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_330996 prefixEnd_330996 := by exact prefixLift 330996
  have htrace : WordTrace (prefixWord ++ tailWord_330996) baseStart_330996 baseEnd_330996 := by
    simpa [prefixWord, tailWord_330996, baseEnd_330996] using wordTrace_append hprefix tailTrace_330996
  have hstable : (prefixWord ++ tailWord_330996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330996).length < 2 ^ (prefixWord ++ tailWord_330996).sum := by decide
  have hdescent : baseEnd_330996 < baseStart_330996 := by decide
  rcases family_descends (prefixWord ++ tailWord_330996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331009 : List Nat := [1, 2, 4, 1, 1, 3, 1, 5, 1, 3]
def baseStart_331009 : Nat := 118140960795 + 331009 * 2 ^ 59
def prefixEnd_331009 : Nat := 4983230072969 + 3 ^ 40 * 331009 * 2
def baseEnd_331009 : Nat := 113311145309467106310149

theorem tailTrace_331009 : CollatzResearch.WordTrace tailWord_331009 prefixEnd_331009 113311145309467106310149 := by
  unfold tailWord_331009
  simp only [CollatzResearch.WordTrace]
  refine ⟨12072890057818399681580081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8048593371878933121053387 12072890057818399681580081)
  ·
    refine ⟨9054667543363799761185061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12072890057818399681580081 9054667543363799761185061)
    ·
      refine ⟨1697750164380712455222199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9054667543363799761185061 1697750164380712455222199)
      ·
        refine ⟨2546625246571068682833299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1697750164380712455222199 2546625246571068682833299)
        ·
          refine ⟨3819937869856603024249949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2546625246571068682833299 3819937869856603024249949)
          ·
            refine ⟨1432476701196226134093731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3819937869856603024249949 1432476701196226134093731)
            ·
              refine ⟨2148715051794339201140597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432476701196226134093731 2148715051794339201140597)
              ·
                refine ⟨201442036105719300106931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2148715051794339201140597 201442036105719300106931)
                ·
                  refine ⟨302163054158578950160397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201442036105719300106931 302163054158578950160397)
                  ·
                    refine ⟨113311145309467106310149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 302163054158578950160397 113311145309467106310149)
                    ·
                      rfl

theorem cell22_331009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_331009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331009 prefixEnd_331009 := by exact prefixLift 331009
  have htrace : WordTrace (prefixWord ++ tailWord_331009) baseStart_331009 baseEnd_331009 := by
    simpa [prefixWord, tailWord_331009, baseEnd_331009] using wordTrace_append hprefix tailTrace_331009
  have hstable : (prefixWord ++ tailWord_331009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331009).length < 2 ^ (prefixWord ++ tailWord_331009).sum := by decide
  have hdescent : baseEnd_331009 < baseStart_331009 := by decide
  rcases family_descends (prefixWord ++ tailWord_331009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331020 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_331020 : Nat := 118140960795 + 331020 * 2 ^ 59
def prefixEnd_331020 : Nat := 4983230072969 + 3 ^ 40 * 331020 * 2
def baseEnd_331020 : Nat := 113314910834266744285115

theorem tailTrace_331020 : CollatzResearch.WordTrace tailWord_331020 prefixEnd_331020 113314910834266744285115 := by
  unfold tailWord_331020
  simp only [CollatzResearch.WordTrace]
  refine ⟨6036645630389274280115257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8048860840519032373487009 6036645630389274280115257)
  ·
    refine ⟨4527484222791955710086443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6036645630389274280115257 4527484222791955710086443)
    ·
      refine ⟨6791226334187933565129665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4527484222791955710086443 6791226334187933565129665)
      ·
        refine ⟨5093419750640950173847249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6791226334187933565129665 5093419750640950173847249)
        ·
          refine ⟨3820064812980712630385437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5093419750640950173847249 3820064812980712630385437)
          ·
            refine ⟨1432524304867767236394539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3820064812980712630385437 1432524304867767236394539)
            ·
              refine ⟨2148786457301650854591809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432524304867767236394539 2148786457301650854591809)
              ·
                refine ⟨1611589842976238140943857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2148786457301650854591809 1611589842976238140943857)
                ·
                  refine ⟨1208692382232178605707893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1611589842976238140943857 1208692382232178605707893)
                  ·
                    refine ⟨113314910834266744285115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1208692382232178605707893 113314910834266744285115)
                    ·
                      rfl

theorem cell22_331020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_331020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331020 prefixEnd_331020 := by exact prefixLift 331020
  have htrace : WordTrace (prefixWord ++ tailWord_331020) baseStart_331020 baseEnd_331020 := by
    simpa [prefixWord, tailWord_331020, baseEnd_331020] using wordTrace_append hprefix tailTrace_331020
  have hstable : (prefixWord ++ tailWord_331020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331020).length < 2 ^ (prefixWord ++ tailWord_331020).sum := by decide
  have hdescent : baseEnd_331020 < baseStart_331020 := by decide
  rcases family_descends (prefixWord ++ tailWord_331020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331022 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_331022 : Nat := 118140960795 + 331022 * 2 ^ 59
def prefixEnd_331022 : Nat := 4983230072969 + 3 ^ 40 * 331022 * 2
def baseEnd_331022 : Nat := 37771865158379801911703

theorem tailTrace_331022 : CollatzResearch.WordTrace tailWord_331022 prefixEnd_331022 37771865158379801911703 := by
  unfold tailWord_331022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1509170525846412862725415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8048909471180868601202213 1509170525846412862725415)
  ·
    refine ⟨2263755788769619294088123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1509170525846412862725415 2263755788769619294088123)
    ·
      refine ⟨3395633683154428941132185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2263755788769619294088123 3395633683154428941132185)
      ·
        refine ⟨2546725262365821705849139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3395633683154428941132185 2546725262365821705849139)
        ·
          refine ⟨3820087893548732558773709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2546725262365821705849139 3820087893548732558773709)
          ·
            refine ⟨1432532960080774709540141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3820087893548732558773709 1432532960080774709540141)
            ·
              refine ⟨537199860030290516077553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1432532960080774709540141 537199860030290516077553)
              ·
                refine ⟨402899895022717887058165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537199860030290516077553 402899895022717887058165)
                ·
                  refine ⟨37771865158379801911703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 402899895022717887058165 37771865158379801911703)
                  ·
                    rfl

theorem cell22_331022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_331022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331022 prefixEnd_331022 := by exact prefixLift 331022
  have htrace : WordTrace (prefixWord ++ tailWord_331022) baseStart_331022 baseEnd_331022 := by
    simpa [prefixWord, tailWord_331022, baseEnd_331022] using wordTrace_append hprefix tailTrace_331022
  have hstable : (prefixWord ++ tailWord_331022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331022).length < 2 ^ (prefixWord ++ tailWord_331022).sum := by decide
  have hdescent : baseEnd_331022 < baseStart_331022 := by decide
  rcases family_descends (prefixWord ++ tailWord_331022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331037 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_331037 : Nat := 118140960795 + 331037 * 2 ^ 59
def prefixEnd_331037 : Nat := 4983230072969 + 3 ^ 40 * 331037 * 2
def baseEnd_331037 : Nat := 113320730281684366610063

theorem tailTrace_331037 : CollatzResearch.WordTrace tailWord_331037 prefixEnd_331037 113320730281684366610063 := by
  unfold tailWord_331037
  simp only [CollatzResearch.WordTrace]
  refine ⟨12073911301716960463599365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8049274201144640309066243 12073911301716960463599365)
  ·
    refine ⟨2263858369071930086924881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12073911301716960463599365 2263858369071930086924881)
    ·
      refine ⟨1697893776803947565193661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2263858369071930086924881 1697893776803947565193661)
      ·
        refine ⟨636710166301480336947623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1697893776803947565193661 636710166301480336947623)
        ·
          refine ⟨955065249452220505421435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636710166301480336947623 955065249452220505421435)
          ·
            refine ⟨1432597874178330758132153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955065249452220505421435 1432597874178330758132153)
            ·
              refine ⟨1074448405633748068599115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1432597874178330758132153 1074448405633748068599115)
              ·
                refine ⟨1611672608450622102898673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074448405633748068599115 1611672608450622102898673)
                ·
                  refine ⟨1208754456337966577174005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1611672608450622102898673 1208754456337966577174005)
                  ·
                    refine ⟨113320730281684366610063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1208754456337966577174005 113320730281684366610063)
                    ·
                      rfl

theorem cell22_331037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_331037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331037 prefixEnd_331037 := by exact prefixLift 331037
  have htrace : WordTrace (prefixWord ++ tailWord_331037) baseStart_331037 baseEnd_331037 := by
    simpa [prefixWord, tailWord_331037, baseEnd_331037] using wordTrace_append hprefix tailTrace_331037
  have hstable : (prefixWord ++ tailWord_331037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331037).length < 2 ^ (prefixWord ++ tailWord_331037).sum := by decide
  have hdescent : baseEnd_331037 < baseStart_331037 := by decide
  rcases family_descends (prefixWord ++ tailWord_331037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331039 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 5]
def baseStart_331039 : Nat := 118140960795 + 331039 * 2 ^ 59
def prefixEnd_331039 : Nat := 4983230072969 + 3 ^ 40 * 331039 * 2
def baseEnd_331039 : Nat := 37773804974185676020019

theorem tailTrace_331039 : CollatzResearch.WordTrace tailWord_331039 prefixEnd_331039 37773804974185676020019 := by
  unfold tailWord_331039
  simp only [CollatzResearch.WordTrace]
  refine ⟨12073984247709714805172171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8049322831806476536781447 12073984247709714805172171)
  ·
    refine ⟨18110976371564572207758257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12073984247709714805172171 18110976371564572207758257)
    ·
      refine ⟨13583232278673429155818693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18110976371564572207758257 13583232278673429155818693)
      ·
        refine ⟨2546856052251267966716005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13583232278673429155818693 2546856052251267966716005)
        ·
          refine ⟨477535509797112743759251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2546856052251267966716005 477535509797112743759251)
          ·
            refine ⟨716303264695669115638877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477535509797112743759251 716303264695669115638877)
            ·
              refine ⟨268613724260875918364579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 716303264695669115638877 268613724260875918364579)
              ·
                refine ⟨402920586391313877546869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268613724260875918364579 402920586391313877546869)
                ·
                  refine ⟨37773804974185676020019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 402920586391313877546869 37773804974185676020019)
                  ·
                    rfl

theorem cell22_331039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 5].length) (baseStart_331039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331039 prefixEnd_331039 := by exact prefixLift 331039
  have htrace : WordTrace (prefixWord ++ tailWord_331039) baseStart_331039 baseEnd_331039 := by
    simpa [prefixWord, tailWord_331039, baseEnd_331039] using wordTrace_append hprefix tailTrace_331039
  have hstable : (prefixWord ++ tailWord_331039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331039).length < 2 ^ (prefixWord ++ tailWord_331039).sum := by decide
  have hdescent : baseEnd_331039 < baseStart_331039 := by decide
  rcases family_descends (prefixWord ++ tailWord_331039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331095 : List Nat := [1, 1, 3, 2, 3, 2, 1, 9]
def baseStart_331095 : Nat := 118140960795 + 331095 * 2 ^ 59
def prefixEnd_331095 : Nat := 4983230072969 + 3 ^ 40 * 331095 * 2
def baseEnd_331095 : Nat := 12593398318554616517765

theorem tailTrace_331095 : CollatzResearch.WordTrace tailWord_331095 prefixEnd_331095 12593398318554616517765 := by
  unfold tailWord_331095
  simp only [CollatzResearch.WordTrace]
  refine ⟨12076026735506836369210739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8050684490337890912807159 12076026735506836369210739)
  ·
    refine ⟨18114040103260254553816109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12076026735506836369210739 18114040103260254553816109)
    ·
      refine ⟨6792765038722595457681041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18114040103260254553816109 6792765038722595457681041)
      ·
        refine ⟨5094573779041946593260781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6792765038722595457681041 5094573779041946593260781)
        ·
          refine ⟨1910465167140729972472793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5094573779041946593260781 1910465167140729972472793)
          ·
            refine ⟨1432848875355547479354595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1910465167140729972472793 1432848875355547479354595)
            ·
              refine ⟨2149273313033321219031893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432848875355547479354595 2149273313033321219031893)
              ·
                refine ⟨12593398318554616517765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2149273313033321219031893 12593398318554616517765)
                ·
                  rfl

theorem cell22_331095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 9].length) (baseStart_331095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331095 prefixEnd_331095 := by exact prefixLift 331095
  have htrace : WordTrace (prefixWord ++ tailWord_331095) baseStart_331095 baseEnd_331095 := by
    simpa [prefixWord, tailWord_331095, baseEnd_331095] using wordTrace_append hprefix tailTrace_331095
  have hstable : (prefixWord ++ tailWord_331095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331095).length < 2 ^ (prefixWord ++ tailWord_331095).sum := by decide
  have hdescent : baseEnd_331095 < baseStart_331095 := by decide
  rcases family_descends (prefixWord ++ tailWord_331095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331157 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 5]
def baseStart_331157 : Nat := 118140960795 + 331157 * 2 ^ 59
def prefixEnd_331157 : Nat := 4983230072969 + 3 ^ 40 * 331157 * 2
def baseEnd_331157 : Nat := 37787269578014684536565

theorem tailTrace_331157 : CollatzResearch.WordTrace tailWord_331157 prefixEnd_331157 37787269578014684536565 := by
  unfold tailWord_331157
  simp only [CollatzResearch.WordTrace]
  refine ⟨12078288061282220957967725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8052192040854813971978483 12078288061282220957967725)
  ·
    refine ⟨4529358022980832859237897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12078288061282220957967725 4529358022980832859237897)
    ·
      refine ⟨3397018517235624644428423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4529358022980832859237897 3397018517235624644428423)
      ·
        refine ⟨5095527775853436966642635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397018517235624644428423 5095527775853436966642635)
        ·
          refine ⟨7643291663780155449963953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5095527775853436966642635 7643291663780155449963953)
          ·
            refine ⟨5732468747835116587472965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7643291663780155449963953 5732468747835116587472965)
            ·
              refine ⟨1074837890219084360151181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5732468747835116587472965 1074837890219084360151181)
              ·
                refine ⟨403064208832156635056693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1074837890219084360151181 403064208832156635056693)
                ·
                  refine ⟨37787269578014684536565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 403064208832156635056693 37787269578014684536565)
                  ·
                    rfl

theorem cell22_331157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_331157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331157 prefixEnd_331157 := by exact prefixLift 331157
  have htrace : WordTrace (prefixWord ++ tailWord_331157) baseStart_331157 baseEnd_331157 := by
    simpa [prefixWord, tailWord_331157, baseEnd_331157] using wordTrace_append hprefix tailTrace_331157
  have hstable : (prefixWord ++ tailWord_331157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331157).length < 2 ^ (prefixWord ++ tailWord_331157).sum := by decide
  have hdescent : baseEnd_331157 < baseStart_331157 := by decide
  rcases family_descends (prefixWord ++ tailWord_331157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331249 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 2, 4]
def baseStart_331249 : Nat := 118140960795 + 331249 * 2 ^ 59
def prefixEnd_331249 : Nat := 4983230072969 + 3 ^ 40 * 331249 * 2
def baseEnd_331249 : Nat := 113393302214186480309413

theorem tailTrace_331249 : CollatzResearch.WordTrace tailWord_331249 prefixEnd_331249 113393302214186480309413 := by
  unfold tailWord_331249
  simp only [CollatzResearch.WordTrace]
  refine ⟨12081643576948920670316801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8054429051299280446877867 12081643576948920670316801)
  ·
    refine ⟨9061232682711690502737601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12081643576948920670316801 9061232682711690502737601)
    ·
      refine ⟨6795924512033767877053201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9061232682711690502737601 6795924512033767877053201)
      ·
        refine ⟨5096943384025325907789901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6795924512033767877053201 5096943384025325907789901)
        ·
          refine ⟨1911353769009497215421213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5096943384025325907789901 1911353769009497215421213)
          ·
            refine ⟨716757663378561455782955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1911353769009497215421213 716757663378561455782955)
            ·
              refine ⟨1075136495067842183674433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716757663378561455782955 1075136495067842183674433)
              ·
                refine ⟨806352371300881637755825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075136495067842183674433 806352371300881637755825)
                ·
                  refine ⟨604764278475661228316869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 806352371300881637755825 604764278475661228316869)
                  ·
                    refine ⟨113393302214186480309413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 604764278475661228316869 113393302214186480309413)
                    ·
                      rfl

theorem cell22_331249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_331249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331249 prefixEnd_331249 := by exact prefixLift 331249
  have htrace : WordTrace (prefixWord ++ tailWord_331249) baseStart_331249 baseEnd_331249 := by
    simpa [prefixWord, tailWord_331249, baseEnd_331249] using wordTrace_append hprefix tailTrace_331249
  have hstable : (prefixWord ++ tailWord_331249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331249).length < 2 ^ (prefixWord ++ tailWord_331249).sum := by decide
  have hdescent : baseEnd_331249 < baseStart_331249 := by decide
  rcases family_descends (prefixWord ++ tailWord_331249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331268 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_331268 : Nat := 118140960795 + 331268 * 2 ^ 59
def prefixEnd_331268 : Nat := 4983230072969 + 3 ^ 40 * 331268 * 2
def baseEnd_331268 : Nat := 113399806302476764084355

theorem tailTrace_331268 : CollatzResearch.WordTrace tailWord_331268 prefixEnd_331268 113399806302476764084355 := by
  unfold tailWord_331268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6041168281940043457629229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8054891042586724610172305 6041168281940043457629229)
  ·
    refine ⟨2265438105727516296610961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6041168281940043457629229 2265438105727516296610961)
    ·
      refine ⟨1699078579295637222458221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2265438105727516296610961 1699078579295637222458221)
      ·
        refine ⟨637154467235863958421833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1699078579295637222458221 637154467235863958421833)
        ·
          refine ⟨477865850426897968816375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637154467235863958421833 477865850426897968816375)
          ·
            refine ⟨716798775640346953224563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477865850426897968816375 716798775640346953224563)
            ·
              refine ⟨1075198163460520429836845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716798775640346953224563 1075198163460520429836845)
              ·
                refine ⟨403199311297695161188817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1075198163460520429836845 403199311297695161188817)
                ·
                  refine ⟨302399483473271370891613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403199311297695161188817 302399483473271370891613)
                  ·
                    refine ⟨113399806302476764084355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 302399483473271370891613 113399806302476764084355)
                    ·
                      rfl

theorem cell22_331268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_331268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331268 prefixEnd_331268 := by exact prefixLift 331268
  have htrace : WordTrace (prefixWord ++ tailWord_331268) baseStart_331268 baseEnd_331268 := by
    simpa [prefixWord, tailWord_331268, baseEnd_331268] using wordTrace_append hprefix tailTrace_331268
  have hstable : (prefixWord ++ tailWord_331268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331268).length < 2 ^ (prefixWord ++ tailWord_331268).sum := by decide
  have hdescent : baseEnd_331268 < baseStart_331268 := by decide
  rcases family_descends (prefixWord ++ tailWord_331268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331339 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 1, 4]
def baseStart_331339 : Nat := 118140960795 + 331339 * 2 ^ 59
def prefixEnd_331339 : Nat := 4983230072969 + 3 ^ 40 * 331339 * 2
def baseEnd_331339 : Nat := 113424111053456245559137

theorem tailTrace_331339 : CollatzResearch.WordTrace tailWord_331339 prefixEnd_331339 113424111053456245559137 := by
  unfold tailWord_331339
  simp only [CollatzResearch.WordTrace]
  refine ⟨12084926146622866041093071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8056617431081910694062047 12084926146622866041093071)
  ·
    refine ⟨18127389219934299061639607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12084926146622866041093071 18127389219934299061639607)
    ·
      refine ⟨27191083829901448592459411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18127389219934299061639607 27191083829901448592459411)
      ·
        refine ⟨40786625744852172888689117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27191083829901448592459411 40786625744852172888689117)
        ·
          refine ⟨15294984654319564833258419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40786625744852172888689117 15294984654319564833258419)
          ·
            refine ⟨22942476981479347249887629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15294984654319564833258419 22942476981479347249887629)
            ·
              refine ⟨8603428868054755218707861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22942476981479347249887629 8603428868054755218707861)
              ·
                refine ⟨403285728190066650876931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8603428868054755218707861 403285728190066650876931)
                ·
                  refine ⟨604928592285099976315397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403285728190066650876931 604928592285099976315397)
                  ·
                    refine ⟨113424111053456245559137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 604928592285099976315397 113424111053456245559137)
                    ·
                      rfl

theorem cell22_331339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 4].length) (baseStart_331339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331339 prefixEnd_331339 := by exact prefixLift 331339
  have htrace : WordTrace (prefixWord ++ tailWord_331339) baseStart_331339 baseEnd_331339 := by
    simpa [prefixWord, tailWord_331339, baseEnd_331339] using wordTrace_append hprefix tailTrace_331339
  have hstable : (prefixWord ++ tailWord_331339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331339).length < 2 ^ (prefixWord ++ tailWord_331339).sum := by decide
  have hdescent : baseEnd_331339 < baseStart_331339 := by decide
  rcases family_descends (prefixWord ++ tailWord_331339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331399 : List Nat := [1, 1, 4, 2, 1, 4, 1, 8]
def baseStart_331399 : Nat := 118140960795 + 331399 * 2 ^ 59
def prefixEnd_331399 : Nat := 4983230072969 + 3 ^ 40 * 331399 * 2
def baseEnd_331399 : Nat := 12604961142181787673217

theorem tailTrace_331399 : CollatzResearch.WordTrace tailWord_331399 prefixEnd_331399 12604961142181787673217 := by
  unfold tailWord_331399
  simp only [CollatzResearch.WordTrace]
  refine ⟨12087114526405496288277251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8058076350936997525518167 12087114526405496288277251)
  ·
    refine ⟨18130671789608244432415877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12087114526405496288277251 18130671789608244432415877)
    ·
      refine ⟨3399500960551545831077977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18130671789608244432415877 3399500960551545831077977)
      ·
        refine ⟨2549625720413659373308483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3399500960551545831077977 2549625720413659373308483)
        ·
          refine ⟨3824438580620489059962725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2549625720413659373308483 3824438580620489059962725)
          ·
            refine ⟨717082233866341698743011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3824438580620489059962725 717082233866341698743011)
            ·
              refine ⟨1075623350799512548114517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717082233866341698743011 1075623350799512548114517)
              ·
                refine ⟨12604961142181787673217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1075623350799512548114517 12604961142181787673217)
                ·
                  rfl

theorem cell22_331399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 8].length) (baseStart_331399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331399 prefixEnd_331399 := by exact prefixLift 331399
  have htrace : WordTrace (prefixWord ++ tailWord_331399) baseStart_331399 baseEnd_331399 := by
    simpa [prefixWord, tailWord_331399, baseEnd_331399] using wordTrace_append hprefix tailTrace_331399
  have hstable : (prefixWord ++ tailWord_331399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331399).length < 2 ^ (prefixWord ++ tailWord_331399).sum := by decide
  have hdescent : baseEnd_331399 < baseStart_331399 := by decide
  rcases family_descends (prefixWord ++ tailWord_331399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331482 : List Nat := [3, 1, 1, 2, 2, 5, 2, 2, 1, 3]
def baseStart_331482 : Nat := 118140960795 + 331482 * 2 ^ 59
def prefixEnd_331482 : Nat := 4983230072969 + 3 ^ 40 * 331482 * 2
def baseEnd_331482 : Nat := 113473062875851539233699

theorem tailTrace_331482 : CollatzResearch.WordTrace tailWord_331482 prefixEnd_331482 113473062875851539233699 := by
  unfold tailWord_331482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3022535446276200365887175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8060094523403200975699133 3022535446276200365887175)
  ·
    refine ⟨4533803169414300548830763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3022535446276200365887175 4533803169414300548830763)
    ·
      refine ⟨6800704754121450823246145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4533803169414300548830763 6800704754121450823246145)
      ·
        refine ⟨5100528565591088117434609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6800704754121450823246145 5100528565591088117434609)
        ·
          refine ⟨3825396424193316088075957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5100528565591088117434609 3825396424193316088075957)
          ·
            refine ⟨358630914768123383257121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3825396424193316088075957 358630914768123383257121)
            ·
              refine ⟨268973186076092537442841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358630914768123383257121 268973186076092537442841)
              ·
                refine ⟨201729889557069403082131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268973186076092537442841 201729889557069403082131)
                ·
                  refine ⟨302594834335604104623197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201729889557069403082131 302594834335604104623197)
                  ·
                    refine ⟨113473062875851539233699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 302594834335604104623197 113473062875851539233699)
                    ·
                      rfl

theorem cell22_331482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_331482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_331482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_331482 prefixEnd_331482 := by exact prefixLift 331482
  have htrace : WordTrace (prefixWord ++ tailWord_331482) baseStart_331482 baseEnd_331482 := by
    simpa [prefixWord, tailWord_331482, baseEnd_331482] using wordTrace_append hprefix tailTrace_331482
  have hstable : (prefixWord ++ tailWord_331482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331482).length < 2 ^ (prefixWord ++ tailWord_331482).sum := by decide
  have hdescent : baseEnd_331482 < baseStart_331482 := by decide
  rcases family_descends (prefixWord ++ tailWord_331482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
