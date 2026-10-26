import V185TrunkScan23Chunk0327

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1938591 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 2, 2, 2]
def baseStart_1938591 : Nat := 118140960795 + 1938591 * 2 ^ 59
def prefixEnd_1938591 : Nat := 4983230072969 + 3 ^ 40 * 1938591 * 2
def baseEnd_1938591 : Nat := 995428975480329987497089

theorem tailTrace_1938591 : CollatzResearch.WordTrace tailWord_1938591 prefixEnd_1938591 995428975480329987497089 := by
  unfold tailWord_1938591
  simp only [CollatzResearch.WordTrace]
  refine ⟨70706222519823366828887627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47137481679882244552591751 70706222519823366828887627)
  ·
    refine ⟨106059333779735050243331441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70706222519823366828887627 106059333779735050243331441)
    ·
      refine ⟨79544500334801287682498581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106059333779735050243331441 79544500334801287682498581)
      ·
        refine ⟨3728648453193810360117121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79544500334801287682498581 3728648453193810360117121)
        ·
          refine ⟨2796486339895357770087841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3728648453193810360117121 2796486339895357770087841)
          ·
            refine ⟨2097364754921518327565881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2796486339895357770087841 2097364754921518327565881)
            ·
              refine ⟨1573023566191138745674411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097364754921518327565881 1573023566191138745674411)
              ·
                refine ⟨2359535349286708118511617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573023566191138745674411 2359535349286708118511617)
                ·
                  refine ⟨1769651511965031088883713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2359535349286708118511617 1769651511965031088883713)
                  ·
                    refine ⟨1327238633973773316662785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1769651511965031088883713 1327238633973773316662785)
                    ·
                      refine ⟨995428975480329987497089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327238633973773316662785 995428975480329987497089)
                      ·
                        rfl

theorem cell23_1938591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_1938591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938591 prefixEnd_1938591 := by exact prefixLift 1938591
  have htrace : WordTrace (prefixWord ++ tailWord_1938591) baseStart_1938591 baseEnd_1938591 := by
    simpa [prefixWord, tailWord_1938591, baseEnd_1938591] using wordTrace_append hprefix tailTrace_1938591
  have hstable : (prefixWord ++ tailWord_1938591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938591).length < 2 ^ (prefixWord ++ tailWord_1938591).sum := by decide
  have hdescent : baseEnd_1938591 < baseStart_1938591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938674 : List Nat := [3, 2, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_1938674 : Nat := 118140960795 + 1938674 * 2 ^ 59
def prefixEnd_1938674 : Nat := 4983230072969 + 3 ^ 40 * 1938674 * 2
def baseEnd_1938674 : Nat := 331823864791551054253069

theorem tailTrace_1938674 : CollatzResearch.WordTrace tailWord_1938674 prefixEnd_1938674 331823864791551054253069 := by
  unfold tailWord_1938674
  simp only [CollatzResearch.WordTrace]
  refine ⟨17677312444630668001039769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47139499852348448002772717 17677312444630668001039769)
  ·
    refine ⟨13257984333473001000779827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17677312444630668001039769 13257984333473001000779827)
    ·
      refine ⟨19886976500209501501169741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13257984333473001000779827 19886976500209501501169741)
      ·
        refine ⟨7457616187578563062938653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19886976500209501501169741 7457616187578563062938653)
        ·
          refine ⟨2796606070341961148601995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7457616187578563062938653 2796606070341961148601995)
          ·
            refine ⟨4194909105512941722902993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796606070341961148601995 4194909105512941722902993)
            ·
              refine ⟨3146181829134706292177245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4194909105512941722902993 3146181829134706292177245)
              ·
                refine ⟨1179818185925514859566467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3146181829134706292177245 1179818185925514859566467)
                ·
                  refine ⟨1769727278888272289349701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179818185925514859566467 1769727278888272289349701)
                  ·
                    refine ⟨331823864791551054253069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1769727278888272289349701 331823864791551054253069)
                    ·
                      rfl

theorem cell23_1938674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_1938674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938674 prefixEnd_1938674 := by exact prefixLift 1938674
  have htrace : WordTrace (prefixWord ++ tailWord_1938674) baseStart_1938674 baseEnd_1938674 := by
    simpa [prefixWord, tailWord_1938674, baseEnd_1938674] using wordTrace_append hprefix tailTrace_1938674
  have hstable : (prefixWord ++ tailWord_1938674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938674).length < 2 ^ (prefixWord ++ tailWord_1938674).sum := by decide
  have hdescent : baseEnd_1938674 < baseStart_1938674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938697 : List Nat := [1, 2, 1, 1, 3, 3, 1, 6, 1, 1, 3]
def baseStart_1938697 : Nat := 118140960795 + 1938697 * 2 ^ 59
def prefixEnd_1938697 : Nat := 4983230072969 + 3 ^ 40 * 1938697 * 2
def baseEnd_1938697 : Nat := 995483404429706572771601

theorem tailTrace_1938697 : CollatzResearch.WordTrace tailWord_1938697 prefixEnd_1938697 995483404429706572771601 := by
  unfold tailWord_1938697
  simp only [CollatzResearch.WordTrace]
  refine ⟨70710088657439346932246345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47140059104959564621497563 70710088657439346932246345)
  ·
    refine ⟨53032566493079510199184759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70710088657439346932246345 53032566493079510199184759)
    ·
      refine ⟨79548849739619265298777139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53032566493079510199184759 79548849739619265298777139)
      ·
        refine ⟨119323274609428897948165709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79548849739619265298777139 119323274609428897948165709)
        ·
          refine ⟨44746227978535836730562141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119323274609428897948165709 44746227978535836730562141)
          ·
            refine ⟨16779835491950938773960803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44746227978535836730562141 16779835491950938773960803)
            ·
              refine ⟨25169753237926408160941205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16779835491950938773960803 25169753237926408160941205)
              ·
                refine ⟨1179832183027800382544119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25169753237926408160941205 1179832183027800382544119)
                ·
                  refine ⟨1769748274541700573816179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179832183027800382544119 1769748274541700573816179)
                  ·
                    refine ⟨2654622411812550860724269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1769748274541700573816179 2654622411812550860724269)
                    ·
                      refine ⟨995483404429706572771601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2654622411812550860724269 995483404429706572771601)
                      ·
                        rfl

theorem cell23_1938697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 1, 1, 3].length) (baseStart_1938697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938697 prefixEnd_1938697 := by exact prefixLift 1938697
  have htrace : WordTrace (prefixWord ++ tailWord_1938697) baseStart_1938697 baseEnd_1938697 := by
    simpa [prefixWord, tailWord_1938697, baseEnd_1938697] using wordTrace_append hprefix tailTrace_1938697
  have hstable : (prefixWord ++ tailWord_1938697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938697).length < 2 ^ (prefixWord ++ tailWord_1938697).sum := by decide
  have hdescent : baseEnd_1938697 < baseStart_1938697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938717 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1938717 : Nat := 118140960795 + 1938717 * 2 ^ 59
def prefixEnd_1938717 : Nat := 4983230072969 + 3 ^ 40 * 1938717 * 2
def baseEnd_1938717 : Nat := 331831224680932164840503

theorem tailTrace_1938717 : CollatzResearch.WordTrace tailWord_1938717 prefixEnd_1938717 331831224680932164840503 := by
  unfold tailWord_1938717
  simp only [CollatzResearch.WordTrace]
  refine ⟨70710818117366890347974405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47140545411577926898649603 70710818117366890347974405)
  ·
    refine ⟨13258278397006291940245201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70710818117366890347974405 13258278397006291940245201)
    ·
      refine ⟨9943708797754718955183901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13258278397006291940245201 9943708797754718955183901)
      ·
        refine ⟨3728890799158019608193963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9943708797754718955183901 3728890799158019608193963)
        ·
          refine ⟨5593336198737029412290945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3728890799158019608193963 5593336198737029412290945)
          ·
            refine ⟨4195002149052772059218209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5593336198737029412290945 4195002149052772059218209)
            ·
              refine ⟨3146251611789579044413657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4195002149052772059218209 3146251611789579044413657)
              ·
                refine ⟨2359688708842184283310243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3146251611789579044413657 2359688708842184283310243)
                ·
                  refine ⟨3539533063263276424965365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359688708842184283310243 3539533063263276424965365)
                  ·
                    refine ⟨331831224680932164840503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3539533063263276424965365 331831224680932164840503)
                    ·
                      rfl

theorem cell23_1938717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1938717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938717 prefixEnd_1938717 := by exact prefixLift 1938717
  have htrace : WordTrace (prefixWord ++ tailWord_1938717) baseStart_1938717 baseEnd_1938717 := by
    simpa [prefixWord, tailWord_1938717, baseEnd_1938717] using wordTrace_append hprefix tailTrace_1938717
  have hstable : (prefixWord ++ tailWord_1938717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938717).length < 2 ^ (prefixWord ++ tailWord_1938717).sum := by decide
  have hdescent : baseEnd_1938717 < baseStart_1938717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938764 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 2, 4]
def baseStart_1938764 : Nat := 118140960795 + 1938764 * 2 ^ 59
def prefixEnd_1938764 : Nat := 4983230072969 + 3 ^ 40 * 1938764 * 2
def baseEnd_1938764 : Nat := 331839269211185936877931

theorem tailTrace_1938764 : CollatzResearch.WordTrace tailWord_1938764 prefixEnd_1938764 331839269211185936877931 := by
  unfold tailWord_1938764
  simp only [CollatzResearch.WordTrace]
  refine ⟨35356266174098308687467673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47141688232131078249956897 35356266174098308687467673)
  ·
    refine ⟨26517199630573731515600755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35356266174098308687467673 26517199630573731515600755)
    ·
      refine ⟨39775799445860597273401133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26517199630573731515600755 39775799445860597273401133)
      ·
        refine ⟨14915924792197723977525425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39775799445860597273401133 14915924792197723977525425)
        ·
          refine ⟨11186943594148292983144069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14915924792197723977525425 11186943594148292983144069)
          ·
            refine ⟨2097551923902804934339513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11186943594148292983144069 2097551923902804934339513)
            ·
              refine ⟨1573163942927103700754635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097551923902804934339513 1573163942927103700754635)
              ·
                refine ⟨2359745914390655551131953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573163942927103700754635 2359745914390655551131953)
                ·
                  refine ⟨1769809435792991663348965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2359745914390655551131953 1769809435792991663348965)
                  ·
                    refine ⟨331839269211185936877931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1769809435792991663348965 331839269211185936877931)
                    ·
                      rfl

theorem cell23_1938764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_1938764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938764 prefixEnd_1938764 := by exact prefixLift 1938764
  have htrace : WordTrace (prefixWord ++ tailWord_1938764) baseStart_1938764 baseEnd_1938764 := by
    simpa [prefixWord, tailWord_1938764, baseEnd_1938764] using wordTrace_append hprefix tailTrace_1938764
  have hstable : (prefixWord ++ tailWord_1938764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938764).length < 2 ^ (prefixWord ++ tailWord_1938764).sum := by decide
  have hdescent : baseEnd_1938764 < baseStart_1938764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938770 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_1938770 : Nat := 118140960795 + 1938770 * 2 ^ 59
def prefixEnd_1938770 : Nat := 4983230072969 + 3 ^ 40 * 1938770 * 2
def baseEnd_1938770 : Nat := 995520888517484787158765

theorem tailTrace_1938770 : CollatzResearch.WordTrace tailWord_1938770 prefixEnd_1938770 995520888517484787158765 := by
  unfold tailWord_1938770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17678187796543720099913441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47141834124116586933102509 17678187796543720099913441)
  ·
    refine ⟨13258640847407790074935081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17678187796543720099913441 13258640847407790074935081)
    ·
      refine ⟨9943980635555842556201311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13258640847407790074935081 9943980635555842556201311)
      ·
        refine ⟨14915970953333763834301967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9943980635555842556201311 14915970953333763834301967)
        ·
          refine ⟨22373956430000645751452951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14915970953333763834301967 22373956430000645751452951)
          ·
            refine ⟨33560934645000968627179427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22373956430000645751452951 33560934645000968627179427)
            ·
              refine ⟨50341401967501452940769141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33560934645000968627179427 50341401967501452940769141)
              ·
                refine ⟨4719506434453261213197107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50341401967501452940769141 4719506434453261213197107)
                ·
                  refine ⟨7079259651679891819795661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719506434453261213197107 7079259651679891819795661)
                  ·
                    refine ⟨2654722369379959432423373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7079259651679891819795661 2654722369379959432423373)
                    ·
                      refine ⟨995520888517484787158765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2654722369379959432423373 995520888517484787158765)
                      ·
                        rfl

theorem cell23_1938770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_1938770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938770 prefixEnd_1938770 := by exact prefixLift 1938770
  have htrace : WordTrace (prefixWord ++ tailWord_1938770) baseStart_1938770 baseEnd_1938770 := by
    simpa [prefixWord, tailWord_1938770, baseEnd_1938770] using wordTrace_append hprefix tailTrace_1938770
  have hstable : (prefixWord ++ tailWord_1938770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938770).length < 2 ^ (prefixWord ++ tailWord_1938770).sum := by decide
  have hdescent : baseEnd_1938770 < baseStart_1938770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938805 : List Nat := [1, 3, 4, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_1938805 : Nat := 118140960795 + 1938805 * 2 ^ 59
def prefixEnd_1938805 : Nat := 4983230072969 + 3 ^ 40 * 1938805 * 2
def baseEnd_1938805 : Nat := 995538860340392150221105

theorem tailTrace_1938805 : CollatzResearch.WordTrace tailWord_1938805 prefixEnd_1938805 995538860340392150221105 := by
  unfold tailWord_1938805
  simp only [CollatzResearch.WordTrace]
  refine ⟨70714027741048081377177869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47142685160698720918118579 70714027741048081377177869)
  ·
    refine ⟨26517760402893030516441701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70714027741048081377177869 26517760402893030516441701)
    ·
      refine ⟨4972080075542443221832819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26517760402893030516441701 4972080075542443221832819)
      ·
        refine ⟨7458120113313664832749229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4972080075542443221832819 7458120113313664832749229)
        ·
          refine ⟨2796795042492624312280961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7458120113313664832749229 2796795042492624312280961)
          ·
            refine ⟨2097596281869468234210721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2796795042492624312280961 2097596281869468234210721)
            ·
              refine ⟨1573197211402101175658041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097596281869468234210721 1573197211402101175658041)
              ·
                refine ⟨1179897908551575881743531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573197211402101175658041 1179897908551575881743531)
                ·
                  refine ⟨1769846862827363822615297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179897908551575881743531 1769846862827363822615297)
                  ·
                    refine ⟨1327385147120522866961473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1769846862827363822615297 1327385147120522866961473)
                    ·
                      refine ⟨995538860340392150221105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327385147120522866961473 995538860340392150221105)
                      ·
                        rfl

theorem cell23_1938805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_1938805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938805 prefixEnd_1938805 := by exact prefixLift 1938805
  have htrace : WordTrace (prefixWord ++ tailWord_1938805) baseStart_1938805 baseEnd_1938805 := by
    simpa [prefixWord, tailWord_1938805, baseEnd_1938805] using wordTrace_append hprefix tailTrace_1938805
  have hstable : (prefixWord ++ tailWord_1938805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938805).length < 2 ^ (prefixWord ++ tailWord_1938805).sum := by decide
  have hdescent : baseEnd_1938805 < baseStart_1938805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938820 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1938820 : Nat := 118140960795 + 1938820 * 2 ^ 59
def prefixEnd_1938820 : Nat := 4983230072969 + 3 ^ 40 * 1938820 * 2
def baseEnd_1938820 : Nat := 331848854183403197177845

theorem tailTrace_1938820 : CollatzResearch.WordTrace tailWord_1938820 prefixEnd_1938820 331848854183403197177845 := by
  unfold tailWord_1938820
  simp only [CollatzResearch.WordTrace]
  refine ⟨35357287417996869469486957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47143049890662492625982609 35357287417996869469486957)
  ·
    refine ⟨13258982781748826051057609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35357287417996869469486957 13258982781748826051057609)
    ·
      refine ⟨9944237086311619538293207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13258982781748826051057609 9944237086311619538293207)
      ·
        refine ⟨14916355629467429307439811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9944237086311619538293207 14916355629467429307439811)
        ·
          refine ⟨22374533444201143961159717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14916355629467429307439811 22374533444201143961159717)
          ·
            refine ⟨4195225020787714492717447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22374533444201143961159717 4195225020787714492717447)
            ·
              refine ⟨6292837531181571739076171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195225020787714492717447 6292837531181571739076171)
              ·
                refine ⟨9439256296772357608614257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292837531181571739076171 9439256296772357608614257)
                ·
                  refine ⟨7079442222579268206460693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9439256296772357608614257 7079442222579268206460693)
                  ·
                    refine ⟨331848854183403197177845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7079442222579268206460693 331848854183403197177845)
                    ·
                      rfl

theorem cell23_1938820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1938820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938820 prefixEnd_1938820 := by exact prefixLift 1938820
  have htrace : WordTrace (prefixWord ++ tailWord_1938820) baseStart_1938820 baseEnd_1938820 := by
    simpa [prefixWord, tailWord_1938820, baseEnd_1938820] using wordTrace_append hprefix tailTrace_1938820
  have hstable : (prefixWord ++ tailWord_1938820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938820).length < 2 ^ (prefixWord ++ tailWord_1938820).sum := by decide
  have hdescent : baseEnd_1938820 < baseStart_1938820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938827 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 1, 4, 2]
def baseStart_1938827 : Nat := 118140960795 + 1938827 * 2 ^ 59
def prefixEnd_1938827 : Nat := 4983230072969 + 3 ^ 40 * 1938827 * 2
def baseEnd_1938827 : Nat := 995550156914791064146003

theorem tailTrace_1938827 : CollatzResearch.WordTrace tailWord_1938827 prefixEnd_1938827 995550156914791064146003 := by
  unfold tailWord_1938827
  simp only [CollatzResearch.WordTrace]
  refine ⟨70714830146968379134478735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47143220097978919422985823 70714830146968379134478735)
  ·
    refine ⟨106072245220452568701718103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70714830146968379134478735 106072245220452568701718103)
    ·
      refine ⟨159108367830678853052577155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106072245220452568701718103 159108367830678853052577155)
      ·
        refine ⟨238662551746018279578865733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159108367830678853052577155 238662551746018279578865733)
        ·
          refine ⟨44749228452378427421037325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238662551746018279578865733 44749228452378427421037325)
          ·
            refine ⟨16780960669641910282888997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44749228452378427421037325 16780960669641910282888997)
            ·
              refine ⟨3146430125557858178041687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16780960669641910282888997 3146430125557858178041687)
              ·
                refine ⟨4719645188336787267062531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146430125557858178041687 4719645188336787267062531)
                ·
                  refine ⟨7079467782505180900593797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719645188336787267062531 7079467782505180900593797)
                  ·
                    refine ⟨1327400209219721418861337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079467782505180900593797 1327400209219721418861337)
                    ·
                      refine ⟨995550156914791064146003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327400209219721418861337 995550156914791064146003)
                      ·
                        rfl

theorem cell23_1938827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 4, 2].length) (baseStart_1938827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938827 prefixEnd_1938827 := by exact prefixLift 1938827
  have htrace : WordTrace (prefixWord ++ tailWord_1938827) baseStart_1938827 baseEnd_1938827 := by
    simpa [prefixWord, tailWord_1938827, baseEnd_1938827] using wordTrace_append hprefix tailTrace_1938827
  have hstable : (prefixWord ++ tailWord_1938827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938827).length < 2 ^ (prefixWord ++ tailWord_1938827).sum := by decide
  have hdescent : baseEnd_1938827 < baseStart_1938827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938833 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 7]
def baseStart_1938833 : Nat := 118140960795 + 1938833 * 2 ^ 59
def prefixEnd_1938833 : Nat := 4983230072969 + 3 ^ 40 * 1938833 * 2
def baseEnd_1938833 : Nat := 110617026422079782296775

theorem tailTrace_1938833 : CollatzResearch.WordTrace tailWord_1938833 prefixEnd_1938833 110617026422079782296775 := by
  unfold tailWord_1938833
  simp only [CollatzResearch.WordTrace]
  refine ⟨70715048984946642159197153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47143365989964428106131435 70715048984946642159197153)
  ·
    refine ⟨53036286738709981619397865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70715048984946642159197153 53036286738709981619397865)
    ·
      refine ⟨39777215054032486214548399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53036286738709981619397865 39777215054032486214548399)
      ·
        refine ⟨59665822581048729321822599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39777215054032486214548399 59665822581048729321822599)
        ·
          refine ⟨89498733871573093982733899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59665822581048729321822599 89498733871573093982733899)
          ·
            refine ⟨134248100807359640974100849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89498733871573093982733899 134248100807359640974100849)
            ·
              refine ⟨100686075605519730730575637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134248100807359640974100849 100686075605519730730575637)
              ·
                refine ⟨4719659794008737377995733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100686075605519730730575637 4719659794008737377995733)
                ·
                  refine ⟨110617026422079782296775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4719659794008737377995733 110617026422079782296775)
                  ·
                    rfl

theorem cell23_1938833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 7].length) (baseStart_1938833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938833 prefixEnd_1938833 := by exact prefixLift 1938833
  have htrace : WordTrace (prefixWord ++ tailWord_1938833) baseStart_1938833 baseEnd_1938833 := by
    simpa [prefixWord, tailWord_1938833, baseEnd_1938833] using wordTrace_append hprefix tailTrace_1938833
  have hstable : (prefixWord ++ tailWord_1938833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938833).length < 2 ^ (prefixWord ++ tailWord_1938833).sum := by decide
  have hdescent : baseEnd_1938833 < baseStart_1938833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938860 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 3]
def baseStart_1938860 : Nat := 118140960795 + 1938860 * 2 ^ 59
def prefixEnd_1938860 : Nat := 4983230072969 + 3 ^ 40 * 1938860 * 2
def baseEnd_1938860 : Nat := 995567101776389435033351

theorem tailTrace_1938860 : CollatzResearch.WordTrace tailWord_1938860 prefixEnd_1938860 995567101776389435033351 := by
  unfold tailWord_1938860
  simp only [CollatzResearch.WordTrace]
  refine ⟨35358016877924412885215017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47144022503899217180286689 35358016877924412885215017)
  ·
    refine ⟨26518512658443309663911263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35358016877924412885215017 26518512658443309663911263)
    ·
      refine ⟨39777768987664964495866895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26518512658443309663911263 39777768987664964495866895)
      ·
        refine ⟨59666653481497446743800343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39777768987664964495866895 59666653481497446743800343)
        ·
          refine ⟨89499980222246170115700515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59666653481497446743800343 89499980222246170115700515)
          ·
            refine ⟨134249970333369255173550773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89499980222246170115700515 134249970333369255173550773)
            ·
              refine ⟨12585934718753367672520385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134249970333369255173550773 12585934718753367672520385)
              ·
                refine ⟨9439451039065025754390289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12585934718753367672520385 9439451039065025754390289)
                ·
                  refine ⟨7079588279298769315792717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9439451039065025754390289 7079588279298769315792717)
                  ·
                    refine ⟨2654845604737038493422269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7079588279298769315792717 2654845604737038493422269)
                    ·
                      refine ⟨995567101776389435033351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2654845604737038493422269 995567101776389435033351)
                      ·
                        rfl

theorem cell23_1938860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_1938860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938860 prefixEnd_1938860 := by exact prefixLift 1938860
  have htrace : WordTrace (prefixWord ++ tailWord_1938860) baseStart_1938860 baseEnd_1938860 := by
    simpa [prefixWord, tailWord_1938860, baseEnd_1938860] using wordTrace_append hprefix tailTrace_1938860
  have hstable : (prefixWord ++ tailWord_1938860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938860).length < 2 ^ (prefixWord ++ tailWord_1938860).sum := by decide
  have hdescent : baseEnd_1938860 < baseStart_1938860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938861 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_1938861 : Nat := 118140960795 + 1938861 * 2 ^ 59
def prefixEnd_1938861 : Nat := 4983230072969 + 3 ^ 40 * 1938861 * 2
def baseEnd_1938861 : Nat := 995567615257043931120847

theorem tailTrace_1938861 : CollatzResearch.WordTrace tailWord_1938861 prefixEnd_1938861 995567615257043931120847 := by
  unfold tailWord_1938861
  simp only [CollatzResearch.WordTrace]
  refine ⟨70716070228845202941216437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47144046819230135294144291 70716070228845202941216437)
  ·
    refine ⟨6629631583954237775739041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70716070228845202941216437 6629631583954237775739041)
    ·
      refine ⟨4972223687965678331804281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6629631583954237775739041 4972223687965678331804281)
      ·
        refine ⟨3729167765974258748853211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4972223687965678331804281 3729167765974258748853211)
        ·
          refine ⟨5593751648961388123279817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3729167765974258748853211 5593751648961388123279817)
          ·
            refine ⟨4195313736721041092459863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5593751648961388123279817 4195313736721041092459863)
            ·
              refine ⟨6292970605081561638689795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195313736721041092459863 6292970605081561638689795)
              ·
                refine ⟨9439455907622342458034693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292970605081561638689795 9439455907622342458034693)
                ·
                  refine ⟨1769897982679189210881505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9439455907622342458034693 1769897982679189210881505)
                  ·
                    refine ⟨1327423487009391908161129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1769897982679189210881505 1327423487009391908161129)
                    ·
                      refine ⟨995567615257043931120847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327423487009391908161129 995567615257043931120847)
                      ·
                        rfl

theorem cell23_1938861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_1938861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938861 prefixEnd_1938861 := by exact prefixLift 1938861
  have htrace : WordTrace (prefixWord ++ tailWord_1938861) baseStart_1938861 baseEnd_1938861 := by
    simpa [prefixWord, tailWord_1938861, baseEnd_1938861] using wordTrace_append hprefix tailTrace_1938861
  have hstable : (prefixWord ++ tailWord_1938861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938861).length < 2 ^ (prefixWord ++ tailWord_1938861).sum := by decide
  have hdescent : baseEnd_1938861 < baseStart_1938861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938882 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_1938882 : Nat := 118140960795 + 1938882 * 2 ^ 59
def prefixEnd_1938882 : Nat := 4983230072969 + 3 ^ 40 * 1938882 * 2
def baseEnd_1938882 : Nat := 995578398350788348958251

theorem tailTrace_1938882 : CollatzResearch.WordTrace tailWord_1938882 prefixEnd_1938882 995578398350788348958251 := by
  unfold tailWord_1938882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17679209040442280881932725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47144557441179415685153933 17679209040442280881932725)
  ·
    refine ⟨1657425847541463832681193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17679209040442280881932725 1657425847541463832681193)
    ·
      refine ⟨1243069385656097874510895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1657425847541463832681193 1243069385656097874510895)
      ·
        refine ⟨1864604078484146811766343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243069385656097874510895 1864604078484146811766343)
        ·
          refine ⟨2796906117726220217649515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864604078484146811766343 2796906117726220217649515)
          ·
            refine ⟨4195359176589330326474273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796906117726220217649515 4195359176589330326474273)
            ·
              refine ⟨3146519382441997744855705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4195359176589330326474273 3146519382441997744855705)
              ·
                refine ⟨2359889536831498308641779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3146519382441997744855705 2359889536831498308641779)
                ·
                  refine ⟨3539834305247247462962669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359889536831498308641779 3539834305247247462962669)
                  ·
                    refine ⟨1327437864467717798611001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3539834305247247462962669 1327437864467717798611001)
                    ·
                      refine ⟨995578398350788348958251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327437864467717798611001 995578398350788348958251)
                      ·
                        rfl

theorem cell23_1938882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_1938882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938882 prefixEnd_1938882 := by exact prefixLift 1938882
  have htrace : WordTrace (prefixWord ++ tailWord_1938882) baseStart_1938882 baseEnd_1938882 := by
    simpa [prefixWord, tailWord_1938882, baseEnd_1938882] using wordTrace_append hprefix tailTrace_1938882
  have hstable : (prefixWord ++ tailWord_1938882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938882).length < 2 ^ (prefixWord ++ tailWord_1938882).sum := by decide
  have hdescent : baseEnd_1938882 < baseStart_1938882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938917 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1938917 : Nat := 118140960795 + 1938917 * 2 ^ 59
def prefixEnd_1938917 : Nat := 4983230072969 + 3 ^ 40 * 1938917 * 2
def baseEnd_1938917 : Nat := 995596370173695712020589

theorem tailTrace_1938917 : CollatzResearch.WordTrace tailWord_1938917 prefixEnd_1938917 995596370173695712020589 := by
  unfold tailWord_1938917
  simp only [CollatzResearch.WordTrace]
  refine ⟨70718112716642324505255005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47145408477761549670170003 70718112716642324505255005)
  ·
    refine ⟨26519292268740871689470627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70718112716642324505255005 26519292268740871689470627)
    ·
      refine ⟨39778938403111307534205941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26519292268740871689470627 39778938403111307534205941)
      ·
        refine ⟨3729275475291685081331807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39778938403111307534205941 3729275475291685081331807)
        ·
          refine ⟨5593913212937527621997711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3729275475291685081331807 5593913212937527621997711)
          ·
            refine ⟨8390869819406291432996567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5593913212937527621997711 8390869819406291432996567)
            ·
              refine ⟨12586304729109437149494851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8390869819406291432996567 12586304729109437149494851)
              ·
                refine ⟨18879457093664155724242277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12586304729109437149494851 18879457093664155724242277)
                ·
                  refine ⟨3539898205062029198295427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18879457093664155724242277 3539898205062029198295427)
                  ·
                    refine ⟨5309847307593043797443141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3539898205062029198295427 5309847307593043797443141)
                    ·
                      refine ⟨995596370173695712020589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5309847307593043797443141 995596370173695712020589)
                      ·
                        rfl

theorem cell23_1938917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1938917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938917 prefixEnd_1938917 := by exact prefixLift 1938917
  have htrace : WordTrace (prefixWord ++ tailWord_1938917) baseStart_1938917 baseEnd_1938917 := by
    simpa [prefixWord, tailWord_1938917, baseEnd_1938917] using wordTrace_append hprefix tailTrace_1938917
  have hstable : (prefixWord ++ tailWord_1938917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938917).length < 2 ^ (prefixWord ++ tailWord_1938917).sum := by decide
  have hdescent : baseEnd_1938917 < baseStart_1938917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938927 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 3, 4]
def baseStart_1938927 : Nat := 118140960795 + 1938927 * 2 ^ 59
def prefixEnd_1938927 : Nat := 4983230072969 + 3 ^ 40 * 1938927 * 2
def baseEnd_1938927 : Nat := 331867168326746890965181

theorem tailTrace_1938927 : CollatzResearch.WordTrace tailWord_1938927 prefixEnd_1938927 331867168326746890965181 := by
  unfold tailWord_1938927
  simp only [CollatzResearch.WordTrace]
  refine ⟨70718477446606096213119035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47145651631070730808746023 70718477446606096213119035)
  ·
    refine ⟨106077716169909144319678553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70718477446606096213119035 106077716169909144319678553)
    ·
      refine ⟨79558287127431858239758915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106077716169909144319678553 79558287127431858239758915)
      ·
        refine ⟨119337430691147787359638373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79558287127431858239758915 119337430691147787359638373)
        ·
          refine ⟨22375768254590210129932195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119337430691147787359638373 22375768254590210129932195)
          ·
            refine ⟨33563652381885315194898293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22375768254590210129932195 33563652381885315194898293)
            ·
              refine ⟨3146592410801748299521715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33563652381885315194898293 3146592410801748299521715)
              ·
                refine ⟨4719888616202622449282573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146592410801748299521715 4719888616202622449282573)
                ·
                  refine ⟨1769958231075983418480965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4719888616202622449282573 1769958231075983418480965)
                  ·
                    refine ⟨331867168326746890965181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1769958231075983418480965 331867168326746890965181)
                    ·
                      rfl

theorem cell23_1938927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 4].length) (baseStart_1938927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938927 prefixEnd_1938927 := by exact prefixLift 1938927
  have htrace : WordTrace (prefixWord ++ tailWord_1938927) baseStart_1938927 baseEnd_1938927 := by
    simpa [prefixWord, tailWord_1938927, baseEnd_1938927] using wordTrace_append hprefix tailTrace_1938927
  have hstable : (prefixWord ++ tailWord_1938927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938927).length < 2 ^ (prefixWord ++ tailWord_1938927).sum := by decide
  have hdescent : baseEnd_1938927 < baseStart_1938927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938954 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_1938954 : Nat := 118140960795 + 1938954 * 2 ^ 59
def prefixEnd_1938954 : Nat := 4983230072969 + 3 ^ 40 * 1938954 * 2
def baseEnd_1938954 : Nat := 995615368957912067257919

theorem tailTrace_1938954 : CollatzResearch.WordTrace tailWord_1938954 prefixEnd_1938954 995615368957912067257919 := by
  unfold tailWord_1938954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17679865554377069956087979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47146308145005519882901277 17679865554377069956087979)
  ·
    refine ⟨26519798331565604934131969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17679865554377069956087979 26519798331565604934131969)
    ·
      refine ⟨19889848748674203700598977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26519798331565604934131969 19889848748674203700598977)
      ·
        refine ⟨14917386561505652775449233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19889848748674203700598977 14917386561505652775449233)
        ·
          refine ⟨11188039921129239581586925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14917386561505652775449233 11188039921129239581586925)
          ·
            refine ⟨4195514970423464843095097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11188039921129239581586925 4195514970423464843095097)
            ·
              refine ⟨3146636227817598632321323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4195514970423464843095097 3146636227817598632321323)
              ·
                refine ⟨4719954341726397948481985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146636227817598632321323 4719954341726397948481985)
                ·
                  refine ⟨3539965756294798461361489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4719954341726397948481985 3539965756294798461361489)
                  ·
                    refine ⟨2654974317221098846021117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3539965756294798461361489 2654974317221098846021117)
                    ·
                      refine ⟨995615368957912067257919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2654974317221098846021117 995615368957912067257919)
                      ·
                        rfl

theorem cell23_1938954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_1938954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938954 prefixEnd_1938954 := by exact prefixLift 1938954
  have htrace : WordTrace (prefixWord ++ tailWord_1938954) baseStart_1938954 baseEnd_1938954 := by
    simpa [prefixWord, tailWord_1938954, baseEnd_1938954] using wordTrace_append hprefix tailTrace_1938954
  have hstable : (prefixWord ++ tailWord_1938954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938954).length < 2 ^ (prefixWord ++ tailWord_1938954).sum := by decide
  have hdescent : baseEnd_1938954 < baseStart_1938954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939007 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 4]
def baseStart_1939007 : Nat := 118140960795 + 1939007 * 2 ^ 59
def prefixEnd_1939007 : Nat := 4983230072969 + 3 ^ 40 * 1939007 * 2
def baseEnd_1939007 : Nat := 995642583432600359895175

theorem tailTrace_1939007 : CollatzResearch.WordTrace tailWord_1939007 prefixEnd_1939007 995642583432600359895175 := by
  unfold tailWord_1939007
  simp only [CollatzResearch.WordTrace]
  refine ⟨70721395286316269876031275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47147596857544179917354183 70721395286316269876031275)
  ·
    refine ⟨106082092929474404814046913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70721395286316269876031275 106082092929474404814046913)
    ·
      refine ⟨79561569697105803610535185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106082092929474404814046913 79561569697105803610535185)
      ·
        refine ⟨59671177272829352707901389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79561569697105803610535185 59671177272829352707901389)
        ·
          refine ⟨22376691477311007265463021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59671177272829352707901389 22376691477311007265463021)
          ·
            refine ⟨8391259303991627724548633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22376691477311007265463021 8391259303991627724548633)
            ·
              refine ⟨6293444477993720793411475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8391259303991627724548633 6293444477993720793411475)
              ·
                refine ⟨9440166716990581190117213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293444477993720793411475 9440166716990581190117213)
                ·
                  refine ⟨3540062518871467946293955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9440166716990581190117213 3540062518871467946293955)
                  ·
                    refine ⟨5310093778307201919440933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3540062518871467946293955 5310093778307201919440933)
                    ·
                      refine ⟨995642583432600359895175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5310093778307201919440933 995642583432600359895175)
                      ·
                        rfl

theorem cell23_1939007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_1939007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939007 prefixEnd_1939007 := by exact prefixLift 1939007
  have htrace : WordTrace (prefixWord ++ tailWord_1939007) baseStart_1939007 baseEnd_1939007 := by
    simpa [prefixWord, tailWord_1939007, baseEnd_1939007] using wordTrace_append hprefix tailTrace_1939007
  have hstable : (prefixWord ++ tailWord_1939007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939007).length < 2 ^ (prefixWord ++ tailWord_1939007).sum := by decide
  have hdescent : baseEnd_1939007 < baseStart_1939007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939021 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_1939021 : Nat := 118140960795 + 1939021 * 2 ^ 59
def prefixEnd_1939021 : Nat := 4983230072969 + 3 ^ 40 * 1939021 * 2
def baseEnd_1939021 : Nat := 331883257387254435040037

theorem tailTrace_1939021 : CollatzResearch.WordTrace tailWord_1939021 prefixEnd_1939021 331883257387254435040037 := by
  unfold tailWord_1939021
  simp only [CollatzResearch.WordTrace]
  refine ⟨70721905908265550267040917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47147937272177033511360611 70721905908265550267040917)
  ·
    refine ⟨3315089339449947668767543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70721905908265550267040917 3315089339449947668767543)
    ·
      refine ⟨4972634009174921503151315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315089339449947668767543 4972634009174921503151315)
      ·
        refine ⟨7458951013762382254726973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4972634009174921503151315 7458951013762382254726973)
        ·
          refine ⟨2797106630160893345522615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7458951013762382254726973 2797106630160893345522615)
          ·
            refine ⟨4195659945241340018283923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797106630160893345522615 4195659945241340018283923)
            ·
              refine ⟨6293489917862010027425885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195659945241340018283923 6293489917862010027425885)
              ·
                refine ⟨2360058719198253760284707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6293489917862010027425885 2360058719198253760284707)
                ·
                  refine ⟨3540088078797380640427061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360058719198253760284707 3540088078797380640427061)
                  ·
                    refine ⟨331883257387254435040037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3540088078797380640427061 331883257387254435040037)
                    ·
                      rfl

theorem cell23_1939021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_1939021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939021 prefixEnd_1939021 := by exact prefixLift 1939021
  have htrace : WordTrace (prefixWord ++ tailWord_1939021) baseStart_1939021 baseEnd_1939021 := by
    simpa [prefixWord, tailWord_1939021, baseEnd_1939021] using wordTrace_append hprefix tailTrace_1939021
  have hstable : (prefixWord ++ tailWord_1939021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939021).length < 2 ^ (prefixWord ++ tailWord_1939021).sum := by decide
  have hdescent : baseEnd_1939021 < baseStart_1939021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939024 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 5, 2, 2]
def baseStart_1939024 : Nat := 118140960795 + 1939024 * 2 ^ 59
def prefixEnd_1939024 : Nat := 4983230072969 + 3 ^ 40 * 1939024 * 2
def baseEnd_1939024 : Nat := 995651312603726793382597

theorem tailTrace_1939024 : CollatzResearch.WordTrace tailWord_1939024 prefixEnd_1939024 995651312603726793382597 := by
  unfold tailWord_1939024
  simp only [CollatzResearch.WordTrace]
  refine ⟨35361007663627340889700063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47148010218169787852933417 35361007663627340889700063)
  ·
    refine ⟨53041511495441011334550095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35361007663627340889700063 53041511495441011334550095)
    ·
      refine ⟨79562267243161517001825143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53041511495441011334550095 79562267243161517001825143)
      ·
        refine ⟨119343400864742275502737715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79562267243161517001825143 119343400864742275502737715)
        ·
          refine ⟨179015101297113413254106573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119343400864742275502737715 179015101297113413254106573)
          ·
            refine ⟨67130662986417529970289965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179015101297113413254106573 67130662986417529970289965)
            ·
              refine ⟨25173998619906573738858737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67130662986417529970289965 25173998619906573738858737)
              ·
                refine ⟨18880498964929930304144053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25173998619906573738858737 18880498964929930304144053)
                ·
                  refine ⟨1770046777962180966013505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18880498964929930304144053 1770046777962180966013505)
                  ·
                    refine ⟨1327535083471635724510129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1770046777962180966013505 1327535083471635724510129)
                    ·
                      refine ⟨995651312603726793382597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327535083471635724510129 995651312603726793382597)
                      ·
                        rfl

theorem cell23_1939024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5, 2, 2].length) (baseStart_1939024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939024 prefixEnd_1939024 := by exact prefixLift 1939024
  have htrace : WordTrace (prefixWord ++ tailWord_1939024) baseStart_1939024 baseEnd_1939024 := by
    simpa [prefixWord, tailWord_1939024, baseEnd_1939024] using wordTrace_append hprefix tailTrace_1939024
  have hstable : (prefixWord ++ tailWord_1939024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939024).length < 2 ^ (prefixWord ++ tailWord_1939024).sum := by decide
  have hdescent : baseEnd_1939024 < baseStart_1939024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939040 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1939040 : Nat := 118140960795 + 1939040 * 2 ^ 59
def prefixEnd_1939040 : Nat := 4983230072969 + 3 ^ 40 * 1939040 * 2
def baseEnd_1939040 : Nat := 995659528294198730782523

theorem tailTrace_1939040 : CollatzResearch.WordTrace tailWord_1939040 prefixEnd_1939040 995659528294198730782523 := by
  unfold tailWord_1939040
  simp only [CollatzResearch.WordTrace]
  refine ⟨35361299447598358255991287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47148399263464477674655049 35361299447598358255991287)
  ·
    refine ⟨53041949171397537383986931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35361299447598358255991287 53041949171397537383986931)
    ·
      refine ⟨79562923757096306075980397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53041949171397537383986931 79562923757096306075980397)
      ·
        refine ⟨29836096408911114778492649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79562923757096306075980397 29836096408911114778492649)
        ·
          refine ⟨22377072306683336083869487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29836096408911114778492649 22377072306683336083869487)
          ·
            refine ⟨33565608460025004125804231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22377072306683336083869487 33565608460025004125804231)
            ·
              refine ⟨50348412690037506188706347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33565608460025004125804231 50348412690037506188706347)
              ·
                refine ⟨75522619035056259283059521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50348412690037506188706347 75522619035056259283059521)
                ·
                  refine ⟨56641964276292194462294641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75522619035056259283059521 56641964276292194462294641)
                  ·
                    refine ⟨42481473207219145846720981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56641964276292194462294641 42481473207219145846720981)
                    ·
                      refine ⟨995659528294198730782523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42481473207219145846720981 995659528294198730782523)
                      ·
                        rfl

theorem cell23_1939040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1939040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939040 prefixEnd_1939040 := by exact prefixLift 1939040
  have htrace : WordTrace (prefixWord ++ tailWord_1939040) baseStart_1939040 baseEnd_1939040 := by
    simpa [prefixWord, tailWord_1939040, baseEnd_1939040] using wordTrace_append hprefix tailTrace_1939040
  have hstable : (prefixWord ++ tailWord_1939040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939040).length < 2 ^ (prefixWord ++ tailWord_1939040).sum := by decide
  have hdescent : baseEnd_1939040 < baseStart_1939040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939041 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 3, 2, 2]
def baseStart_1939041 : Nat := 118140960795 + 1939041 * 2 ^ 59
def prefixEnd_1939041 : Nat := 4983230072969 + 3 ^ 40 * 1939041 * 2
def baseEnd_1939041 : Nat := 995660041774853226870019

theorem tailTrace_1939041 : CollatzResearch.WordTrace tailWord_1939041 prefixEnd_1939041 995660041774853226870019 := by
  unfold tailWord_1939041
  simp only [CollatzResearch.WordTrace]
  refine ⟨70722635368193093682768977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47148423578795395788512651 70722635368193093682768977)
  ·
    refine ⟨53041976526144820262076733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70722635368193093682768977 53041976526144820262076733)
    ·
      refine ⟨19890741197304307598278775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53041976526144820262076733 19890741197304307598278775)
      ·
        refine ⟨29836111795956461397418163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19890741197304307598278775 29836111795956461397418163)
        ·
          refine ⟨44754167693934692096127245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29836111795956461397418163 44754167693934692096127245)
          ·
            refine ⟨16782812885225509536047717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44754167693934692096127245 16782812885225509536047717)
            ·
              refine ⟨3146777415979783038008947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16782812885225509536047717 3146777415979783038008947)
              ·
                refine ⟨4720166123969674557013421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146777415979783038008947 4720166123969674557013421)
                ·
                  refine ⟨1770062296488627958880033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4720166123969674557013421 1770062296488627958880033)
                  ·
                    refine ⟨1327546722366470969160025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1770062296488627958880033 1327546722366470969160025)
                    ·
                      refine ⟨995660041774853226870019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327546722366470969160025 995660041774853226870019)
                      ·
                        rfl

theorem cell23_1939041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_1939041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939041 prefixEnd_1939041 := by exact prefixLift 1939041
  have htrace : WordTrace (prefixWord ++ tailWord_1939041) baseStart_1939041 baseEnd_1939041 := by
    simpa [prefixWord, tailWord_1939041, baseEnd_1939041] using wordTrace_append hprefix tailTrace_1939041
  have hstable : (prefixWord ++ tailWord_1939041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939041).length < 2 ^ (prefixWord ++ tailWord_1939041).sum := by decide
  have hdescent : baseEnd_1939041 < baseStart_1939041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939054 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1939054 : Nat := 118140960795 + 1939054 * 2 ^ 59
def prefixEnd_1939054 : Nat := 4983230072969 + 3 ^ 40 * 1939054 * 2
def baseEnd_1939054 : Nat := 995666717023361676007459

theorem tailTrace_1939054 : CollatzResearch.WordTrace tailWord_1939054 prefixEnd_1939054 995666717023361676007459 := by
  unfold tailWord_1939054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8840388689643249612874027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47148739678097331268661477 8840388689643249612874027)
  ·
    refine ⟨13260583034464874419311041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8840388689643249612874027 13260583034464874419311041)
    ·
      refine ⟨9945437275848655814483281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13260583034464874419311041 9945437275848655814483281)
      ·
        refine ⟨7459077956886491860862461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9945437275848655814483281 7459077956886491860862461)
        ·
          refine ⟨2797154233832434447823423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7459077956886491860862461 2797154233832434447823423)
          ·
            refine ⟨4195731350748651671735135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797154233832434447823423 4195731350748651671735135)
            ·
              refine ⟨6293597026122977507602703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195731350748651671735135 6293597026122977507602703)
              ·
                refine ⟨9440395539184466261404055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293597026122977507602703 9440395539184466261404055)
                ·
                  refine ⟨14160593308776699392106083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9440395539184466261404055 14160593308776699392106083)
                  ·
                    refine ⟨21240889963165049088159125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14160593308776699392106083 21240889963165049088159125)
                    ·
                      refine ⟨995666717023361676007459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21240889963165049088159125 995666717023361676007459)
                      ·
                        rfl

theorem cell23_1939054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1939054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939054 prefixEnd_1939054 := by exact prefixLift 1939054
  have htrace : WordTrace (prefixWord ++ tailWord_1939054) baseStart_1939054 baseEnd_1939054 := by
    simpa [prefixWord, tailWord_1939054, baseEnd_1939054] using wordTrace_append hprefix tailTrace_1939054
  have hstable : (prefixWord ++ tailWord_1939054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939054).length < 2 ^ (prefixWord ++ tailWord_1939054).sum := by decide
  have hdescent : baseEnd_1939054 < baseStart_1939054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939061 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1939061 : Nat := 118140960795 + 1939061 * 2 ^ 59
def prefixEnd_1939061 : Nat := 4983230072969 + 3 ^ 40 * 1939061 * 2
def baseEnd_1939061 : Nat := 995670311387943148619927

theorem tailTrace_1939061 : CollatzResearch.WordTrace tailWord_1939061 prefixEnd_1939061 995670311387943148619927 := by
  unfold tailWord_1939061
  simp only [CollatzResearch.WordTrace]
  refine ⟨70723364828120637098497037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47148909885413758065664691 70723364828120637098497037)
  ·
    refine ⟨26521261810545238911936389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70723364828120637098497037 26521261810545238911936389)
    ·
      refine ⟨4972736589477232295988073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26521261810545238911936389 4972736589477232295988073)
      ·
        refine ⟨3729552442107924221991055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4972736589477232295988073 3729552442107924221991055)
        ·
          refine ⟨5594328663161886332986583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3729552442107924221991055 5594328663161886332986583)
          ·
            refine ⟨8391492994742829499479875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5594328663161886332986583 8391492994742829499479875)
            ·
              refine ⟨12587239492114244249219813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391492994742829499479875 12587239492114244249219813)
              ·
                refine ⟨2360107404771420796728715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12587239492114244249219813 2360107404771420796728715)
                ·
                  refine ⟨3540161107157131195093073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360107404771420796728715 3540161107157131195093073)
                  ·
                    refine ⟨2655120830367848396319805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3540161107157131195093073 2655120830367848396319805)
                    ·
                      refine ⟨995670311387943148619927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655120830367848396319805 995670311387943148619927)
                      ·
                        rfl

theorem cell23_1939061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1939061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939061 prefixEnd_1939061 := by exact prefixLift 1939061
  have htrace : WordTrace (prefixWord ++ tailWord_1939061) baseStart_1939061 baseEnd_1939061 := by
    simpa [prefixWord, tailWord_1939061, baseEnd_1939061] using wordTrace_append hprefix tailTrace_1939061
  have hstable : (prefixWord ++ tailWord_1939061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939061).length < 2 ^ (prefixWord ++ tailWord_1939061).sum := by decide
  have hdescent : baseEnd_1939061 < baseStart_1939061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939092 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_1939092 : Nat := 118140960795 + 1939092 * 2 ^ 59
def prefixEnd_1939092 : Nat := 4983230072969 + 3 ^ 40 * 1939092 * 2
def baseEnd_1939092 : Nat := 995686229288232527332285

theorem tailTrace_1939092 : CollatzResearch.WordTrace tailWord_1939092 prefixEnd_1939092 995686229288232527332285 := by
  unfold tailWord_1939092
  simp only [CollatzResearch.WordTrace]
  refine ⟨35362247745504164696437765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47149663660672219595250353 35362247745504164696437765)
  ·
    refine ⟨6630421452282030880582081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35362247745504164696437765 6630421452282030880582081)
    ·
      refine ⟨4972816089211523160436561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6630421452282030880582081 4972816089211523160436561)
      ·
        refine ⟨3729612066908642370327421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4972816089211523160436561 3729612066908642370327421)
        ·
          refine ⟨1398604525090740888872783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3729612066908642370327421 1398604525090740888872783)
          ·
            refine ⟨2097906787636111333309175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398604525090740888872783 2097906787636111333309175)
            ·
              refine ⟨3146860181454166999963763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097906787636111333309175 3146860181454166999963763)
              ·
                refine ⟨4720290272181250499945645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146860181454166999963763 4720290272181250499945645)
                ·
                  refine ⟨1770108852067968937479617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4720290272181250499945645 1770108852067968937479617)
                  ·
                    refine ⟨1327581639050976703109713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1770108852067968937479617 1327581639050976703109713)
                    ·
                      refine ⟨995686229288232527332285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327581639050976703109713 995686229288232527332285)
                      ·
                        rfl

theorem cell23_1939092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_1939092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939092 prefixEnd_1939092 := by exact prefixLift 1939092
  have htrace : WordTrace (prefixWord ++ tailWord_1939092) baseStart_1939092 baseEnd_1939092 := by
    simpa [prefixWord, tailWord_1939092, baseEnd_1939092] using wordTrace_append hprefix tailTrace_1939092
  have hstable : (prefixWord ++ tailWord_1939092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939092).length < 2 ^ (prefixWord ++ tailWord_1939092).sum := by decide
  have hdescent : baseEnd_1939092 < baseStart_1939092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939108 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 2, 1, 3]
def baseStart_1939108 : Nat := 118140960795 + 1939108 * 2 ^ 59
def prefixEnd_1939108 : Nat := 4983230072969 + 3 ^ 40 * 1939108 * 2
def baseEnd_1939108 : Nat := 995694444978704464732211

theorem tailTrace_1939108 : CollatzResearch.WordTrace tailWord_1939108 prefixEnd_1939108 995694444978704464732211 := by
  unfold tailWord_1939108
  simp only [CollatzResearch.WordTrace]
  refine ⟨35362539529475182062728989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47150052705966909416971985 35362539529475182062728989)
  ·
    refine ⟨13260952323553193273523371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35362539529475182062728989 13260952323553193273523371)
    ·
      refine ⟨19891428485329789910285057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13260952323553193273523371 19891428485329789910285057)
      ·
        refine ⟨14918571363997342432713793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19891428485329789910285057 14918571363997342432713793)
        ·
          refine ⟨11188928522998006824535345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14918571363997342432713793 11188928522998006824535345)
          ·
            refine ⟨8391696392248505118401509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11188928522998006824535345 8391696392248505118401509)
            ·
              refine ⟨1573443073546594709700283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8391696392248505118401509 1573443073546594709700283)
              ·
                refine ⟨2360164610319892064550425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573443073546594709700283 2360164610319892064550425)
                ·
                  refine ⟨1770123457739919048412819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2360164610319892064550425 1770123457739919048412819)
                  ·
                    refine ⟨2655185186609878572619229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1770123457739919048412819 2655185186609878572619229)
                    ·
                      refine ⟨995694444978704464732211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655185186609878572619229 995694444978704464732211)
                      ·
                        rfl

theorem cell23_1939108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_1939108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939108 prefixEnd_1939108 := by exact prefixLift 1939108
  have htrace : WordTrace (prefixWord ++ tailWord_1939108) baseStart_1939108 baseEnd_1939108 := by
    simpa [prefixWord, tailWord_1939108, baseEnd_1939108] using wordTrace_append hprefix tailTrace_1939108
  have hstable : (prefixWord ++ tailWord_1939108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939108).length < 2 ^ (prefixWord ++ tailWord_1939108).sum := by decide
  have hdescent : baseEnd_1939108 < baseStart_1939108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939112 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1939112 : Nat := 118140960795 + 1939112 * 2 ^ 59
def prefixEnd_1939112 : Nat := 4983230072969 + 3 ^ 40 * 1939112 * 2
def baseEnd_1939112 : Nat := 995696498901322449082193

theorem tailTrace_1939112 : CollatzResearch.WordTrace tailWord_1939112 prefixEnd_1939112 995696498901322449082193 := by
  unfold tailWord_1939112
  simp only [CollatzResearch.WordTrace]
  refine ⟨35362612475467936404301795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47150149967290581872402393 35362612475467936404301795)
  ·
    refine ⟨53043918713201904606452693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35362612475467936404301795 53043918713201904606452693)
    ·
      refine ⟨1243216844840669639213735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 53043918713201904606452693 1243216844840669639213735)
      ·
        refine ⟨1864825267261004458820603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243216844840669639213735 1864825267261004458820603)
        ·
          refine ⟨2797237900891506688230905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864825267261004458820603 2797237900891506688230905)
          ·
            refine ⟨2097928425668630016173179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2797237900891506688230905 2097928425668630016173179)
            ·
              refine ⟨3146892638502945024259769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097928425668630016173179 3146892638502945024259769)
              ·
                refine ⟨2360169478877208768194827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3146892638502945024259769 2360169478877208768194827)
                ·
                  refine ⟨3540254218315813152292241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360169478877208768194827 3540254218315813152292241)
                  ·
                    refine ⟨2655190663736859864219181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3540254218315813152292241 2655190663736859864219181)
                    ·
                      refine ⟨995696498901322449082193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655190663736859864219181 995696498901322449082193)
                      ·
                        rfl

theorem cell23_1939112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1939112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939112 prefixEnd_1939112 := by exact prefixLift 1939112
  have htrace : WordTrace (prefixWord ++ tailWord_1939112) baseStart_1939112 baseEnd_1939112 := by
    simpa [prefixWord, tailWord_1939112, baseEnd_1939112] using wordTrace_append hprefix tailTrace_1939112
  have hstable : (prefixWord ++ tailWord_1939112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939112).length < 2 ^ (prefixWord ++ tailWord_1939112).sum := by decide
  have hdescent : baseEnd_1939112 < baseStart_1939112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939134 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1939134 : Nat := 118140960795 + 1939134 * 2 ^ 59
def prefixEnd_1939134 : Nat := 4983230072969 + 3 ^ 40 * 1939134 * 2
def baseEnd_1939134 : Nat := 995707795475721363007091

theorem tailTrace_1939134 : CollatzResearch.WordTrace tailWord_1939134 prefixEnd_1939134 995707795475721363007091 := by
  unfold tailWord_1939134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8840753419607021320738057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47150684904570780377269637 8840753419607021320738057)
  ·
    refine ⟨6630565064705265990553543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8840753419607021320738057 6630565064705265990553543)
    ·
      refine ⟨9945847597057898985830315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6630565064705265990553543 9945847597057898985830315)
      ·
        refine ⟨14918771395586848478745473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9945847597057898985830315 14918771395586848478745473)
        ·
          refine ⟨11189078546690136359059105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14918771395586848478745473 11189078546690136359059105)
          ·
            refine ⟨8391808910017602269294329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11189078546690136359059105 8391808910017602269294329)
            ·
              refine ⟨6293856682513201701970747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8391808910017602269294329 6293856682513201701970747)
              ·
                refine ⟨9440785023769802552956121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293856682513201701970747 9440785023769802552956121)
                ·
                  refine ⟨7080588767827351914717091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9440785023769802552956121 7080588767827351914717091)
                  ·
                    refine ⟨10620883151741027872075637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7080588767827351914717091 10620883151741027872075637)
                    ·
                      refine ⟨995707795475721363007091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10620883151741027872075637 995707795475721363007091)
                      ·
                        rfl

theorem cell23_1939134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1939134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939134 prefixEnd_1939134 := by exact prefixLift 1939134
  have htrace : WordTrace (prefixWord ++ tailWord_1939134) baseStart_1939134 baseEnd_1939134 := by
    simpa [prefixWord, tailWord_1939134, baseEnd_1939134] using wordTrace_append hprefix tailTrace_1939134
  have hstable : (prefixWord ++ tailWord_1939134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939134).length < 2 ^ (prefixWord ++ tailWord_1939134).sum := by decide
  have hdescent : baseEnd_1939134 < baseStart_1939134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939142 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1939142 : Nat := 118140960795 + 1939142 * 2 ^ 59
def prefixEnd_1939142 : Nat := 4983230072969 + 3 ^ 40 * 1939142 * 2
def baseEnd_1939142 : Nat := 995711903320957331707055

theorem tailTrace_1939142 : CollatzResearch.WordTrace tailWord_1939142 prefixEnd_1939142 995711903320957331707055 := by
  unfold tailWord_1939142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210197473150849622881115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47150879427218125288130453 2210197473150849622881115)
  ·
    refine ⟨3315296209726274434321673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2210197473150849622881115 3315296209726274434321673)
    ·
      refine ⟨2486472157294705825741255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3315296209726274434321673 2486472157294705825741255)
      ·
        refine ⟨3729708235942058738611883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2486472157294705825741255 3729708235942058738611883)
        ·
          refine ⟨5594562353913088107917825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3729708235942058738611883 5594562353913088107917825)
          ·
            refine ⟨4195921765434816080938369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5594562353913088107917825 4195921765434816080938369)
            ·
              refine ⟨3146941324076112060703777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4195921765434816080938369 3146941324076112060703777)
              ·
                refine ⟨2360205993057084045527833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3146941324076112060703777 2360205993057084045527833)
                ·
                  refine ⟨1770154494792813034145875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2360205993057084045527833 1770154494792813034145875)
                  ·
                    refine ⟨2655231742189219551218813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1770154494792813034145875 2655231742189219551218813)
                    ·
                      refine ⟨995711903320957331707055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655231742189219551218813 995711903320957331707055)
                      ·
                        rfl

theorem cell23_1939142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1939142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939142 prefixEnd_1939142 := by exact prefixLift 1939142
  have htrace : WordTrace (prefixWord ++ tailWord_1939142) baseStart_1939142 baseEnd_1939142 := by
    simpa [prefixWord, tailWord_1939142, baseEnd_1939142] using wordTrace_append hprefix tailTrace_1939142
  have hstable : (prefixWord ++ tailWord_1939142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939142).length < 2 ^ (prefixWord ++ tailWord_1939142).sum := by decide
  have hdescent : baseEnd_1939142 < baseStart_1939142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939147 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 3]
def baseStart_1939147 : Nat := 118140960795 + 1939147 * 2 ^ 59
def prefixEnd_1939147 : Nat := 4983230072969 + 3 ^ 40 * 1939147 * 2
def baseEnd_1939147 : Nat := 995714470724229812144531

theorem tailTrace_1939147 : CollatzResearch.WordTrace tailWord_1939147 prefixEnd_1939147 995714470724229812144531 := by
  unfold tailWord_1939147
  simp only [CollatzResearch.WordTrace]
  refine ⟨70726501505809073786127695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47151001003872715857418463 70726501505809073786127695)
  ·
    refine ⟨106089752258713610679191543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70726501505809073786127695 106089752258713610679191543)
    ·
      refine ⟨159134628388070416018787315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106089752258713610679191543 159134628388070416018787315)
      ·
        refine ⟨238701942582105624028180973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159134628388070416018787315 238701942582105624028180973)
        ·
          refine ⟨89513228468289609010567865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238701942582105624028180973 89513228468289609010567865)
          ·
            refine ⟨67134921351217206757925899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89513228468289609010567865 67134921351217206757925899)
            ·
              refine ⟨100702382026825810136888849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67134921351217206757925899 100702382026825810136888849)
              ·
                refine ⟨75526786520119357602666637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100702382026825810136888849 75526786520119357602666637)
                ·
                  refine ⟨28322544945044759100999989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75526786520119357602666637 28322544945044759100999989)
                  ·
                    refine ⟨2655238588597946165718749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28322544945044759100999989 2655238588597946165718749)
                    ·
                      refine ⟨995714470724229812144531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655238588597946165718749 995714470724229812144531)
                      ·
                        rfl

theorem cell23_1939147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 3].length) (baseStart_1939147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939147 prefixEnd_1939147 := by exact prefixLift 1939147
  have htrace : WordTrace (prefixWord ++ tailWord_1939147) baseStart_1939147 baseEnd_1939147 := by
    simpa [prefixWord, tailWord_1939147, baseEnd_1939147] using wordTrace_append hprefix tailTrace_1939147
  have hstable : (prefixWord ++ tailWord_1939147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939147).length < 2 ^ (prefixWord ++ tailWord_1939147).sum := by decide
  have hdescent : baseEnd_1939147 < baseStart_1939147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939158 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1939158 : Nat := 118140960795 + 1939158 * 2 ^ 59
def prefixEnd_1939158 : Nat := 4983230072969 + 3 ^ 40 * 1939158 * 2
def baseEnd_1939158 : Nat := 331906706337143089702327

theorem tailTrace_1939158 : CollatzResearch.WordTrace tailWord_1939158 prefixEnd_1939158 331906706337143089702327 := by
  unfold tailWord_1939158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4420431419298076416548633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47151268472512815109852085 4420431419298076416548633)
  ·
    refine ⟨3315323564473557312411475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4420431419298076416548633 3315323564473557312411475)
    ·
      refine ⟨4972985346710335968617213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3315323564473557312411475 4972985346710335968617213)
      ·
        refine ⟨1864869505016375988231455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4972985346710335968617213 1864869505016375988231455)
        ·
          refine ⟨2797304257524563982347183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864869505016375988231455 2797304257524563982347183)
          ·
            refine ⟨4195956386286845973520775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797304257524563982347183 4195956386286845973520775)
            ·
              refine ⟨6293934579430268960281163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195956386286845973520775 6293934579430268960281163)
              ·
                refine ⟨9440901869145403440421745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293934579430268960281163 9440901869145403440421745)
                ·
                  refine ⟨7080676401859052580316309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9440901869145403440421745 7080676401859052580316309)
                  ·
                    refine ⟨331906706337143089702327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7080676401859052580316309 331906706337143089702327)
                    ·
                      rfl

theorem cell23_1939158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1939158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939158 prefixEnd_1939158 := by exact prefixLift 1939158
  have htrace : WordTrace (prefixWord ++ tailWord_1939158) baseStart_1939158 baseEnd_1939158 := by
    simpa [prefixWord, tailWord_1939158, baseEnd_1939158] using wordTrace_append hprefix tailTrace_1939158
  have hstable : (prefixWord ++ tailWord_1939158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939158).length < 2 ^ (prefixWord ++ tailWord_1939158).sum := by decide
  have hdescent : baseEnd_1939158 < baseStart_1939158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939165 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1939165 : Nat := 118140960795 + 1939165 * 2 ^ 59
def prefixEnd_1939165 : Nat := 4983230072969 + 3 ^ 40 * 1939165 * 2
def baseEnd_1939165 : Nat := 995723713376010741719449

theorem tailTrace_1939165 : CollatzResearch.WordTrace tailWord_1939165 prefixEnd_1939165 995723713376010741719449 := by
  unfold tailWord_1939165
  simp only [CollatzResearch.WordTrace]
  refine ⟨70727158019743862860282949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47151438679829241906855299 70727158019743862860282949)
  ·
    refine ⟨13261342128701974286303053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70727158019743862860282949 13261342128701974286303053)
    ·
      refine ⟨4973003298263240357363645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13261342128701974286303053 4973003298263240357363645)
      ·
        refine ⟨1864876236848715134011367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4973003298263240357363645 1864876236848715134011367)
        ·
          refine ⟨2797314355273072701017051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864876236848715134011367 2797314355273072701017051)
          ·
            refine ⟨4195971532909609051525577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797314355273072701017051 4195971532909609051525577)
            ·
              refine ⟨3146978649682206788644183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4195971532909609051525577 3146978649682206788644183)
              ·
                refine ⟨4720467974523310182966275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146978649682206788644183 4720467974523310182966275)
                ·
                  refine ⟨7080701961784965274449413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4720467974523310182966275 7080701961784965274449413)
                  ·
                    refine ⟨1327631617834680988959265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7080701961784965274449413 1327631617834680988959265)
                    ·
                      refine ⟨995723713376010741719449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327631617834680988959265 995723713376010741719449)
                      ·
                        rfl

theorem cell23_1939165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1939165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939165 prefixEnd_1939165 := by exact prefixLift 1939165
  have htrace : WordTrace (prefixWord ++ tailWord_1939165) baseStart_1939165 baseEnd_1939165 := by
    simpa [prefixWord, tailWord_1939165, baseEnd_1939165] using wordTrace_append hprefix tailTrace_1939165
  have hstable : (prefixWord ++ tailWord_1939165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939165).length < 2 ^ (prefixWord ++ tailWord_1939165).sum := by decide
  have hdescent : baseEnd_1939165 < baseStart_1939165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939167 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 1, 7]
def baseStart_1939167 : Nat := 118140960795 + 1939167 * 2 ^ 59
def prefixEnd_1939167 : Nat := 4983230072969 + 3 ^ 40 * 1939167 * 2
def baseEnd_1939167 : Nat := 331908246779106577964813

theorem tailTrace_1939167 : CollatzResearch.WordTrace tailWord_1939167 prefixEnd_1939167 331908246779106577964813 := by
  unfold tailWord_1939167
  simp only [CollatzResearch.WordTrace]
  refine ⟨70727230965736617201855755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47151487310491078134570503 70727230965736617201855755)
  ·
    refine ⟨106090846448604925802783633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70727230965736617201855755 106090846448604925802783633)
    ·
      refine ⟨79568134836453694352087725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106090846448604925802783633 79568134836453694352087725)
      ·
        refine ⟨29838050563670135382032897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79568134836453694352087725 29838050563670135382032897)
        ·
          refine ⟨22378537922752601536524673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29838050563670135382032897 22378537922752601536524673)
          ·
            refine ⟨16783903442064451152393505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22378537922752601536524673 16783903442064451152393505)
            ·
              refine ⟨12587927581548338364295129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16783903442064451152393505 12587927581548338364295129)
              ·
                refine ⟨9440945686161253773221347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12587927581548338364295129 9440945686161253773221347)
                ·
                  refine ⟨14161418529241880659832021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9440945686161253773221347 14161418529241880659832021)
                  ·
                    refine ⟨331908246779106577964813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14161418529241880659832021 331908246779106577964813)
                    ·
                      rfl

theorem cell23_1939167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_1939167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939167 prefixEnd_1939167 := by exact prefixLift 1939167
  have htrace : WordTrace (prefixWord ++ tailWord_1939167) baseStart_1939167 baseEnd_1939167 := by
    simpa [prefixWord, tailWord_1939167, baseEnd_1939167] using wordTrace_append hprefix tailTrace_1939167
  have hstable : (prefixWord ++ tailWord_1939167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939167).length < 2 ^ (prefixWord ++ tailWord_1939167).sum := by decide
  have hdescent : baseEnd_1939167 < baseStart_1939167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939217 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_1939217 : Nat := 118140960795 + 1939217 * 2 ^ 59
def prefixEnd_1939217 : Nat := 4983230072969 + 3 ^ 40 * 1939217 * 2
def baseEnd_1939217 : Nat := 995750414370044538269209

theorem tailTrace_1939217 : CollatzResearch.WordTrace tailWord_1939217 prefixEnd_1939217 995750414370044538269209 := by
  unfold tailWord_1939217
  simp only [CollatzResearch.WordTrace]
  refine ⟨70729054615555475741175905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47152703077036983827450603 70729054615555475741175905)
  ·
    refine ⟨53046790961666606805881929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70729054615555475741175905 53046790961666606805881929)
    ·
      refine ⟨39785093221249955104411447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53046790961666606805881929 39785093221249955104411447)
      ·
        refine ⟨59677639831874932656617171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39785093221249955104411447 59677639831874932656617171)
        ·
          refine ⟨89516459747812398984925757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59677639831874932656617171 89516459747812398984925757)
          ·
            refine ⟨33568672405429649619347159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89516459747812398984925757 33568672405429649619347159)
            ·
              refine ⟨50353008608144474429020739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33568672405429649619347159 50353008608144474429020739)
              ·
                refine ⟨75529512912216711643531109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50353008608144474429020739 75529512912216711643531109)
                ·
                  refine ⟨14161783671040633433162083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75529512912216711643531109 14161783671040633433162083)
                  ·
                    refine ⟨21242675506560950149743125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14161783671040633433162083 21242675506560950149743125)
                    ·
                      refine ⟨995750414370044538269209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21242675506560950149743125 995750414370044538269209)
                      ·
                        rfl

theorem cell23_1939217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_1939217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939217 prefixEnd_1939217 := by exact prefixLift 1939217
  have htrace : WordTrace (prefixWord ++ tailWord_1939217) baseStart_1939217 baseEnd_1939217 := by
    simpa [prefixWord, tailWord_1939217, baseEnd_1939217] using wordTrace_append hprefix tailTrace_1939217
  have hstable : (prefixWord ++ tailWord_1939217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939217).length < 2 ^ (prefixWord ++ tailWord_1939217).sum := by decide
  have hdescent : baseEnd_1939217 < baseStart_1939217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939221 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 2, 4, 2]
def baseStart_1939221 : Nat := 118140960795 + 1939221 * 2 ^ 59
def prefixEnd_1939221 : Nat := 4983230072969 + 3 ^ 40 * 1939221 * 2
def baseEnd_1939221 : Nat := 995752468292662522619191

theorem tailTrace_1939221 : CollatzResearch.WordTrace tailWord_1939221 prefixEnd_1939221 995752468292662522619191 := by
  unfold tailWord_1939221
  simp only [CollatzResearch.WordTrace]
  refine ⟨70729200507540984424321517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47152800338360656282881011 70729200507540984424321517)
  ·
    refine ⟨26523450190327869159120569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70729200507540984424321517 26523450190327869159120569)
    ·
      refine ⟨19892587642745901869340427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26523450190327869159120569 19892587642745901869340427)
      ·
        refine ⟨29838881464118852804010641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19892587642745901869340427 29838881464118852804010641)
        ·
          refine ⟨22379161098089139603007981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29838881464118852804010641 22379161098089139603007981)
          ·
            refine ⟨8392185411783427351127993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22379161098089139603007981 8392185411783427351127993)
            ·
              refine ⟨6294139058837570513345995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8392185411783427351127993 6294139058837570513345995)
              ·
                refine ⟨9441208588256355770018993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6294139058837570513345995 9441208588256355770018993)
                ·
                  refine ⟨7080906441192266827514245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9441208588256355770018993 7080906441192266827514245)
                  ·
                    refine ⟨1327669957723550030158921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7080906441192266827514245 1327669957723550030158921)
                    ·
                      refine ⟨995752468292662522619191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327669957723550030158921 995752468292662522619191)
                      ·
                        rfl

theorem cell23_1939221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_1939221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939221 prefixEnd_1939221 := by exact prefixLift 1939221
  have htrace : WordTrace (prefixWord ++ tailWord_1939221) baseStart_1939221 baseEnd_1939221 := by
    simpa [prefixWord, tailWord_1939221, baseEnd_1939221] using wordTrace_append hprefix tailTrace_1939221
  have hstable : (prefixWord ++ tailWord_1939221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939221).length < 2 ^ (prefixWord ++ tailWord_1939221).sum := by decide
  have hdescent : baseEnd_1939221 < baseStart_1939221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939224 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1939224 : Nat := 118140960795 + 1939224 * 2 ^ 59
def prefixEnd_1939224 : Nat := 4983230072969 + 3 ^ 40 * 1939224 * 2
def baseEnd_1939224 : Nat := 995754008734626010881677

theorem tailTrace_1939224 : CollatzResearch.WordTrace tailWord_1939224 prefixEnd_1939224 995754008734626010881677 := by
  unfold tailWord_1939224
  simp only [CollatzResearch.WordTrace]
  refine ⟨35364654963265057968340363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47152873284353410624453817 35364654963265057968340363)
  ·
    refine ⟨53046982444897586952510545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35364654963265057968340363 53046982444897586952510545)
    ·
      refine ⟨39785236833673190214382909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53046982444897586952510545 39785236833673190214382909)
      ·
        refine ⟨14919463812627446330393591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39785236833673190214382909 14919463812627446330393591)
        ·
          refine ⟨22379195718941169495590387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14919463812627446330393591 22379195718941169495590387)
          ·
            refine ⟨33568793578411754243385581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22379195718941169495590387 33568793578411754243385581)
            ·
              refine ⟨12588297591904407841269593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33568793578411754243385581 12588297591904407841269593)
              ·
                refine ⟨9441223193928305880952195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12588297591904407841269593 9441223193928305880952195)
                ·
                  refine ⟨14161834790892458821428293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9441223193928305880952195 14161834790892458821428293)
                  ·
                    refine ⟨2655344023292336029017805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14161834790892458821428293 2655344023292336029017805)
                    ·
                      refine ⟨995754008734626010881677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655344023292336029017805 995754008734626010881677)
                      ·
                        rfl

theorem cell23_1939224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1939224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939224 prefixEnd_1939224 := by exact prefixLift 1939224
  have htrace : WordTrace (prefixWord ++ tailWord_1939224) baseStart_1939224 baseEnd_1939224 := by
    simpa [prefixWord, tailWord_1939224, baseEnd_1939224] using wordTrace_append hprefix tailTrace_1939224
  have hstable : (prefixWord ++ tailWord_1939224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939224).length < 2 ^ (prefixWord ++ tailWord_1939224).sum := by decide
  have hdescent : baseEnd_1939224 < baseStart_1939224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939234 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_1939234 : Nat := 118140960795 + 1939234 * 2 ^ 59
def prefixEnd_1939234 : Nat := 4983230072969 + 3 ^ 40 * 1939234 * 2
def baseEnd_1939234 : Nat := 995759143541170971756631

theorem tailTrace_1939234 : CollatzResearch.WordTrace tailWord_1939234 prefixEnd_1939234 995759143541170971756631 := by
  unfold tailWord_1939234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17682418664123471911136189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47153116437662591763029837 17682418664123471911136189)
  ·
    refine ⟨6630906999046301966676071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17682418664123471911136189 6630906999046301966676071)
    ·
      refine ⟨9946360498569452950014107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6630906999046301966676071 9946360498569452950014107)
      ·
        refine ⟨14919540747854179425021161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9946360498569452950014107 14919540747854179425021161)
        ·
          refine ⟨11189655560890634568765871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14919540747854179425021161 11189655560890634568765871)
          ·
            refine ⟨16784483341335951853148807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11189655560890634568765871 16784483341335951853148807)
            ·
              refine ⟨25176725012003927779723211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16784483341335951853148807 25176725012003927779723211)
              ·
                refine ⟨37765087518005891669584817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25176725012003927779723211 37765087518005891669584817)
                ·
                  refine ⟨28323815638504418752188613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37765087518005891669584817 28323815638504418752188613)
                  ·
                    refine ⟨5310715432219578516035365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28323815638504418752188613 5310715432219578516035365)
                    ·
                      refine ⟨995759143541170971756631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5310715432219578516035365 995759143541170971756631)
                      ·
                        rfl

theorem cell23_1939234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_1939234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939234 prefixEnd_1939234 := by exact prefixLift 1939234
  have htrace : WordTrace (prefixWord ++ tailWord_1939234) baseStart_1939234 baseEnd_1939234 := by
    simpa [prefixWord, tailWord_1939234, baseEnd_1939234] using wordTrace_append hprefix tailTrace_1939234
  have hstable : (prefixWord ++ tailWord_1939234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939234).length < 2 ^ (prefixWord ++ tailWord_1939234).sum := by decide
  have hdescent : baseEnd_1939234 < baseStart_1939234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939247 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_1939247 : Nat := 118140960795 + 1939247 * 2 ^ 59
def prefixEnd_1939247 : Nat := 4983230072969 + 3 ^ 40 * 1939247 * 2
def baseEnd_1939247 : Nat := 995765818789679420894071

theorem tailTrace_1939247 : CollatzResearch.WordTrace tailWord_1939247 prefixEnd_1939247 995765818789679420894071 := by
  unfold tailWord_1939247
  simp only [CollatzResearch.WordTrace]
  refine ⟨70730148805446790864767995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47153432536964527243178663 70730148805446790864767995)
  ·
    refine ⟨106095223208170186297151993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70730148805446790864767995 106095223208170186297151993)
    ·
      refine ⟨79571417406127639722863995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106095223208170186297151993 79571417406127639722863995)
      ·
        refine ⟨119357126109191459584295993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79571417406127639722863995 119357126109191459584295993)
        ·
          refine ⟨89517844581893594688221995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119357126109191459584295993 89517844581893594688221995)
          ·
            refine ⟨134276766872840392032332993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89517844581893594688221995 134276766872840392032332993)
            ·
              refine ⟨100707575154630294024249745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134276766872840392032332993 100707575154630294024249745)
              ·
                refine ⟨75530681365972720518187309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100707575154630294024249745 75530681365972720518187309)
                ·
                  refine ⟨28324005512239770194320241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75530681365972720518187309 28324005512239770194320241)
                  ·
                    refine ⟨21243004134179827645740181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28324005512239770194320241 21243004134179827645740181)
                    ·
                      refine ⟨995765818789679420894071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21243004134179827645740181 995765818789679420894071)
                      ·
                        rfl

theorem cell23_1939247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_1939247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939247 prefixEnd_1939247 := by exact prefixLift 1939247
  have htrace : WordTrace (prefixWord ++ tailWord_1939247) baseStart_1939247 baseEnd_1939247 := by
    simpa [prefixWord, tailWord_1939247, baseEnd_1939247] using wordTrace_append hprefix tailTrace_1939247
  have hstable : (prefixWord ++ tailWord_1939247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939247).length < 2 ^ (prefixWord ++ tailWord_1939247).sum := by decide
  have hdescent : baseEnd_1939247 < baseStart_1939247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939274 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_1939274 : Nat := 118140960795 + 1939274 * 2 ^ 59
def prefixEnd_1939274 : Nat := 4983230072969 + 3 ^ 40 * 1939274 * 2
def baseEnd_1939274 : Nat := 331926560922450271752149

theorem tailTrace_1939274 : CollatzResearch.WordTrace tailWord_1939274 prefixEnd_1939274 331926560922450271752149 := by
  unfold tailWord_1939274
  simp only [CollatzResearch.WordTrace]
  refine ⟨17682783394087243619000219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47154089050899316317333917 17682783394087243619000219)
  ·
    refine ⟨26524175091130865428500329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17682783394087243619000219 26524175091130865428500329)
    ·
      refine ⟨19893131318348149071375247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26524175091130865428500329 19893131318348149071375247)
      ·
        refine ⟨29839696977522223607062871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19893131318348149071375247 29839696977522223607062871)
        ·
          refine ⟨44759545466283335410594307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29839696977522223607062871 44759545466283335410594307)
          ·
            refine ⟨67139318199425003115891461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44759545466283335410594307 67139318199425003115891461)
            ·
              refine ⟨12588622162392188084229649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67139318199425003115891461 12588622162392188084229649)
              ·
                refine ⟨9441466621794141063172237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12588622162392188084229649 9441466621794141063172237)
                ·
                  refine ⟨3540549983172802898689589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9441466621794141063172237 3540549983172802898689589)
                  ·
                    refine ⟨331926560922450271752149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3540549983172802898689589 331926560922450271752149)
                    ·
                      rfl

theorem cell23_1939274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_1939274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939274 prefixEnd_1939274 := by exact prefixLift 1939274
  have htrace : WordTrace (prefixWord ++ tailWord_1939274) baseStart_1939274 baseEnd_1939274 := by
    simpa [prefixWord, tailWord_1939274, baseEnd_1939274] using wordTrace_append hprefix tailTrace_1939274
  have hstable : (prefixWord ++ tailWord_1939274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939274).length < 2 ^ (prefixWord ++ tailWord_1939274).sum := by decide
  have hdescent : baseEnd_1939274 < baseStart_1939274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939308 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 1, 5]
def baseStart_1939308 : Nat := 118140960795 + 1939308 * 2 ^ 59
def prefixEnd_1939308 : Nat := 4983230072969 + 3 ^ 40 * 1939308 * 2
def baseEnd_1939308 : Nat := 331932380369867894077097

theorem tailTrace_1939308 : CollatzResearch.WordTrace tailWord_1939308 prefixEnd_1939308 331932380369867894077097 := by
  unfold tailWord_1939308
  simp only [CollatzResearch.WordTrace]
  refine ⟨35366186829112899141369289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47154915772150532188492385 35366186829112899141369289)
  ·
    refine ⟨26524640121834674356026967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35366186829112899141369289 26524640121834674356026967)
    ·
      refine ⟨39786960182752011534040451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26524640121834674356026967 39786960182752011534040451)
      ·
        refine ⟨59680440274128017301060677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39786960182752011534040451 59680440274128017301060677)
        ·
          refine ⟨11190082551399003243948877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59680440274128017301060677 11190082551399003243948877)
          ·
            refine ⟨4196280956774626216480829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11190082551399003243948877 4196280956774626216480829)
            ·
              refine ⟨1573605358790484831180311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4196280956774626216480829 1573605358790484831180311)
              ·
                refine ⟨2360408038185727246770467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573605358790484831180311 2360408038185727246770467)
                ·
                  refine ⟨3540612057278590870155701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360408038185727246770467 3540612057278590870155701)
                  ·
                    refine ⟨331932380369867894077097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3540612057278590870155701 331932380369867894077097)
                    ·
                      rfl

theorem cell23_1939308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_1939308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939308 prefixEnd_1939308 := by exact prefixLift 1939308
  have htrace : WordTrace (prefixWord ++ tailWord_1939308) baseStart_1939308 baseEnd_1939308 := by
    simpa [prefixWord, tailWord_1939308, baseEnd_1939308] using wordTrace_append hprefix tailTrace_1939308
  have hstable : (prefixWord ++ tailWord_1939308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939308).length < 2 ^ (prefixWord ++ tailWord_1939308).sum := by decide
  have hdescent : baseEnd_1939308 < baseStart_1939308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939328 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 3, 2, 2]
def baseStart_1939328 : Nat := 118140960795 + 1939328 * 2 ^ 59
def prefixEnd_1939328 : Nat := 4983230072969 + 3 ^ 40 * 1939328 * 2
def baseEnd_1939328 : Nat := 995807410722693603981199

theorem tailTrace_1939328 : CollatzResearch.WordTrace tailWord_1939328 prefixEnd_1939328 995807410722693603981199 := by
  unfold tailWord_1939328
  simp only [CollatzResearch.WordTrace]
  refine ⟨35366551559076670849233319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47155402078768894465644425 35366551559076670849233319)
  ·
    refine ⟨53049827338615006273849979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35366551559076670849233319 53049827338615006273849979)
    ·
      refine ⟨79574741007922509410774969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53049827338615006273849979 79574741007922509410774969)
      ·
        refine ⟨59681055755941882058081227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79574741007922509410774969 59681055755941882058081227)
        ·
          refine ⟨89521583633912823087121841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59681055755941882058081227 89521583633912823087121841)
          ·
            refine ⟨67141187725434617315341381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89521583633912823087121841 67141187725434617315341381)
            ·
              refine ⟨12588972698518990746626509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67141187725434617315341381 12588972698518990746626509)
              ·
                refine ⟨4720864761944621529984941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12588972698518990746626509 4720864761944621529984941)
                ·
                  refine ⟨1770324285729233073744353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4720864761944621529984941 1770324285729233073744353)
                  ·
                    refine ⟨1327743214296924805308265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1770324285729233073744353 1327743214296924805308265)
                    ·
                      refine ⟨995807410722693603981199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327743214296924805308265 995807410722693603981199)
                      ·
                        rfl

theorem cell23_1939328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3, 2, 2].length) (baseStart_1939328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939328 prefixEnd_1939328 := by exact prefixLift 1939328
  have htrace : WordTrace (prefixWord ++ tailWord_1939328) baseStart_1939328 baseEnd_1939328 := by
    simpa [prefixWord, tailWord_1939328, baseEnd_1939328] using wordTrace_append hprefix tailTrace_1939328
  have hstable : (prefixWord ++ tailWord_1939328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939328).length < 2 ^ (prefixWord ++ tailWord_1939328).sum := by decide
  have hdescent : baseEnd_1939328 < baseStart_1939328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939331 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 3]
def baseStart_1939331 : Nat := 118140960795 + 1939331 * 2 ^ 59
def prefixEnd_1939331 : Nat := 4983230072969 + 3 ^ 40 * 1939331 * 2
def baseEnd_1939331 : Nat := 995808951164657092243685

theorem tailTrace_1939331 : CollatzResearch.WordTrace tailWord_1939331 prefixEnd_1939331 995808951164657092243685 := by
  unfold tailWord_1939331
  simp only [CollatzResearch.WordTrace]
  refine ⟨70733212537142473210825847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47155475024761648807217231 70733212537142473210825847)
  ·
    refine ⟨106099818805713709816238771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70733212537142473210825847 106099818805713709816238771)
    ·
      refine ⟨159149728208570564724358157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106099818805713709816238771 159149728208570564724358157)
      ·
        refine ⟨59681148078213961771634309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159149728208570564724358157 59681148078213961771634309)
        ·
          refine ⟨11190215264665117832181433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59681148078213961771634309 11190215264665117832181433)
          ·
            refine ⟨8392661448498838374136075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11190215264665117832181433 8392661448498838374136075)
            ·
              refine ⟨12588992172748257561204113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8392661448498838374136075 12588992172748257561204113)
              ·
                refine ⟨9441744129561193170903085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12588992172748257561204113 9441744129561193170903085)
                ·
                  refine ⟨3540654048585447439088657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9441744129561193170903085 3540654048585447439088657)
                  ·
                    refine ⟨2655490536439085579316493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3540654048585447439088657 2655490536439085579316493)
                    ·
                      refine ⟨995808951164657092243685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655490536439085579316493 995808951164657092243685)
                      ·
                        rfl

theorem cell23_1939331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_1939331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939331 prefixEnd_1939331 := by exact prefixLift 1939331
  have htrace : WordTrace (prefixWord ++ tailWord_1939331) baseStart_1939331 baseEnd_1939331 := by
    simpa [prefixWord, tailWord_1939331, baseEnd_1939331] using wordTrace_append hprefix tailTrace_1939331
  have hstable : (prefixWord ++ tailWord_1939331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939331).length < 2 ^ (prefixWord ++ tailWord_1939331).sum := by decide
  have hdescent : baseEnd_1939331 < baseStart_1939331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939338 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 1, 6]
def baseStart_1939338 : Nat := 118140960795 + 1939338 * 2 ^ 59
def prefixEnd_1939338 : Nat := 4983230072969 + 3 ^ 40 * 1939338 * 2
def baseEnd_1939338 : Nat := 331937515176412854952051

theorem tailTrace_1939338 : CollatzResearch.WordTrace tailWord_1939338 prefixEnd_1939338 331937515176412854952051 := by
  unfold tailWord_1939338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17683366962029278351582667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47155645232078075604220445 17683366962029278351582667)
  ·
    refine ⟨26525050443043917527374001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17683366962029278351582667 26525050443043917527374001)
    ·
      refine ⟨19893787832282938145530501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26525050443043917527374001 19893787832282938145530501)
      ·
        refine ⟨3730085218553050902286969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19893787832282938145530501 3730085218553050902286969)
        ·
          refine ⟨2797563913914788176715227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3730085218553050902286969 2797563913914788176715227)
          ·
            refine ⟨4196345870872182265072841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797563913914788176715227 4196345870872182265072841)
            ·
              refine ⟨3147259403154136698804631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4196345870872182265072841 3147259403154136698804631)
              ·
                refine ⟨4720889104731205048206947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147259403154136698804631 4720889104731205048206947)
                ·
                  refine ⟨7081333657096807572310421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4720889104731205048206947 7081333657096807572310421)
                  ·
                    refine ⟨331937515176412854952051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7081333657096807572310421 331937515176412854952051)
                    ·
                      rfl

theorem cell23_1939338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_1939338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939338 prefixEnd_1939338 := by exact prefixLift 1939338
  have htrace : WordTrace (prefixWord ++ tailWord_1939338) baseStart_1939338 baseEnd_1939338 := by
    simpa [prefixWord, tailWord_1939338, baseEnd_1939338] using wordTrace_append hprefix tailTrace_1939338
  have hstable : (prefixWord ++ tailWord_1939338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939338).length < 2 ^ (prefixWord ++ tailWord_1939338).sum := by decide
  have hdescent : baseEnd_1939338 < baseStart_1939338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939348 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1939348 : Nat := 118140960795 + 1939348 * 2 ^ 59
def prefixEnd_1939348 : Nat := 4983230072969 + 3 ^ 40 * 1939348 * 2
def baseEnd_1939348 : Nat := 995817680335783525731107

theorem tailTrace_1939348 : CollatzResearch.WordTrace tailWord_1939348 prefixEnd_1939348 995817680335783525731107 := by
  unfold tailWord_1939348
  simp only [CollatzResearch.WordTrace]
  refine ⟨35366916289040442557097349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47155888385387256742796465 35366916289040442557097349)
  ·
    refine ⟨6631296804195082979455753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35366916289040442557097349 6631296804195082979455753)
    ·
      refine ⟨4973472603146312234591815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6631296804195082979455753 4973472603146312234591815)
      ·
        refine ⟨7460208904719468351887723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973472603146312234591815 7460208904719468351887723)
        ·
          refine ⟨11190313357079202527831585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460208904719468351887723 11190313357079202527831585)
          ·
            refine ⟨8392735017809401895873689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11190313357079202527831585 8392735017809401895873689)
            ·
              refine ⟨6294551263357051421905267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8392735017809401895873689 6294551263357051421905267)
              ·
                refine ⟨9441826895035577132857901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6294551263357051421905267 9441826895035577132857901)
                ·
                  refine ⟨3540685085638341424821713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9441826895035577132857901 3540685085638341424821713)
                  ·
                    refine ⟨2655513814228756068616285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3540685085638341424821713 2655513814228756068616285)
                    ·
                      refine ⟨995817680335783525731107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655513814228756068616285 995817680335783525731107)
                      ·
                        rfl

theorem cell23_1939348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1939348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939348 prefixEnd_1939348 := by exact prefixLift 1939348
  have htrace : WordTrace (prefixWord ++ tailWord_1939348) baseStart_1939348 baseEnd_1939348 := by
    simpa [prefixWord, tailWord_1939348, baseEnd_1939348] using wordTrace_append hprefix tailTrace_1939348
  have hstable : (prefixWord ++ tailWord_1939348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939348).length < 2 ^ (prefixWord ++ tailWord_1939348).sum := by decide
  have hdescent : baseEnd_1939348 < baseStart_1939348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939351 : List Nat := [1, 1, 3, 3, 1, 4, 3, 7]
def baseStart_1939351 : Nat := 118140960795 + 1939351 * 2 ^ 59
def prefixEnd_1939351 : Nat := 4983230072969 + 3 ^ 40 * 1939351 * 2
def baseEnd_1939351 : Nat := 36882193362138778296059

theorem tailTrace_1939351 : CollatzResearch.WordTrace tailWord_1939351 prefixEnd_1939351 36882193362138778296059 := by
  unfold tailWord_1939351
  simp only [CollatzResearch.WordTrace]
  refine ⟨70733941997070016626553907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47155961331380011084369271 70733941997070016626553907)
  ·
    refine ⟨106100912995605024939830861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70733941997070016626553907 106100912995605024939830861)
    ·
      refine ⟨39787842373351884352436573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106100912995605024939830861 39787842373351884352436573)
      ·
        refine ⟨14920440890006956632163715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39787842373351884352436573 14920440890006956632163715)
        ·
          refine ⟨22380661335010434948245573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14920440890006956632163715 22380661335010434948245573)
          ·
            refine ⟨4196374000314456552796045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22380661335010434948245573 4196374000314456552796045)
            ·
              refine ⟨1573640250117921207298517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4196374000314456552796045 1573640250117921207298517)
              ·
                refine ⟨36882193362138778296059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1573640250117921207298517 36882193362138778296059)
                ·
                  rfl

theorem cell23_1939351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 7].length) (baseStart_1939351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939351 prefixEnd_1939351 := by exact prefixLift 1939351
  have htrace : WordTrace (prefixWord ++ tailWord_1939351) baseStart_1939351 baseEnd_1939351 := by
    simpa [prefixWord, tailWord_1939351, baseEnd_1939351] using wordTrace_append hprefix tailTrace_1939351
  have hstable : (prefixWord ++ tailWord_1939351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939351).length < 2 ^ (prefixWord ++ tailWord_1939351).sum := by decide
  have hdescent : baseEnd_1939351 < baseStart_1939351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939362 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_1939362 : Nat := 118140960795 + 1939362 * 2 ^ 59
def prefixEnd_1939362 : Nat := 4983230072969 + 3 ^ 40 * 1939362 * 2
def baseEnd_1939362 : Nat := 995824869064946470956043

theorem tailTrace_1939362 : CollatzResearch.WordTrace tailWord_1939362 prefixEnd_1939362 995824869064946470956043 := by
  unfold tailWord_1939362
  simp only [CollatzResearch.WordTrace]
  refine ⟨17683585800007541376301085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47156228800020110336802893 17683585800007541376301085)
  ·
    refine ⟨6631344675002828016112907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17683585800007541376301085 6631344675002828016112907)
    ·
      refine ⟨9947017012504242024169361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6631344675002828016112907 9947017012504242024169361)
      ·
        refine ⟨7460262759378181518127021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9947017012504242024169361 7460262759378181518127021)
        ·
          refine ⟨2797598534766818069297633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7460262759378181518127021 2797598534766818069297633)
          ·
            refine ⟨2098198901075113551973225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2797598534766818069297633 2098198901075113551973225)
            ·
              refine ⟨1573649175806335163979919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098198901075113551973225 1573649175806335163979919)
              ·
                refine ⟨2360473763709502745969879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573649175806335163979919 2360473763709502745969879)
                ·
                  refine ⟨3540710645564254118954819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360473763709502745969879 3540710645564254118954819)
                  ·
                    refine ⟨5311065968346381178432229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3540710645564254118954819 5311065968346381178432229)
                    ·
                      refine ⟨995824869064946470956043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5311065968346381178432229 995824869064946470956043)
                      ·
                        rfl

theorem cell23_1939362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_1939362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939362 prefixEnd_1939362 := by exact prefixLift 1939362
  have htrace : WordTrace (prefixWord ++ tailWord_1939362) baseStart_1939362 baseEnd_1939362 := by
    simpa [prefixWord, tailWord_1939362, baseEnd_1939362] using wordTrace_append hprefix tailTrace_1939362
  have hstable : (prefixWord ++ tailWord_1939362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939362).length < 2 ^ (prefixWord ++ tailWord_1939362).sum := by decide
  have hdescent : baseEnd_1939362 < baseStart_1939362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939368 : List Nat := [2, 1, 6, 2, 1, 1, 10]
def baseStart_1939368 : Nat := 118140960795 + 1939368 * 2 ^ 59
def prefixEnd_1939368 : Nat := 4983230072969 + 3 ^ 40 * 1939368 * 2
def baseEnd_1939368 : Nat := 12294172221591030215815

theorem tailTrace_1939368 : CollatzResearch.WordTrace tailWord_1939368 prefixEnd_1939368 12294172221591030215815 := by
  unfold tailWord_1939368
  simp only [CollatzResearch.WordTrace]
  refine ⟨35367281019004214264961379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47156374692005619019948505 35367281019004214264961379)
  ·
    refine ⟨53050921528506321397442069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35367281019004214264961379 53050921528506321397442069)
    ·
      refine ⟨2486761946648733815505097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53050921528506321397442069 2486761946648733815505097)
      ·
        refine ⟨1865071459986550361628823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2486761946648733815505097 1865071459986550361628823)
        ·
          refine ⟨2797607189979825542443235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865071459986550361628823 2797607189979825542443235)
          ·
            refine ⟨4196410784969738313664853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797607189979825542443235 4196410784969738313664853)
            ·
              refine ⟨12294172221591030215815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4196410784969738313664853 12294172221591030215815)
              ·
                rfl

theorem cell23_1939368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 10].length) (baseStart_1939368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939368 prefixEnd_1939368 := by exact prefixLift 1939368
  have htrace : WordTrace (prefixWord ++ tailWord_1939368) baseStart_1939368 baseEnd_1939368 := by
    simpa [prefixWord, tailWord_1939368, baseEnd_1939368] using wordTrace_append hprefix tailTrace_1939368
  have hstable : (prefixWord ++ tailWord_1939368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939368).length < 2 ^ (prefixWord ++ tailWord_1939368).sum := by decide
  have hdescent : baseEnd_1939368 < baseStart_1939368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939424 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 9]
def baseStart_1939424 : Nat := 118140960795 + 1939424 * 2 ^ 59
def prefixEnd_1939424 : Nat := 4983230072969 + 3 ^ 40 * 1939424 * 2
def baseEnd_1939424 : Nat := 110650744985058358708973

theorem tailTrace_1939424 : CollatzResearch.WordTrace tailWord_1939424 prefixEnd_1939424 110650744985058358708973 := by
  unfold tailWord_1939424
  simp only [CollatzResearch.WordTrace]
  refine ⟨35368302262902775046980663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47157736350537033395974217 35368302262902775046980663)
  ·
    refine ⟨53052453394354162570470995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35368302262902775046980663 53052453394354162570470995)
    ·
      refine ⟨79578680091531243855706493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53052453394354162570470995 79578680091531243855706493)
      ·
        refine ⟨29842005034324216445889935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79578680091531243855706493 29842005034324216445889935)
        ·
          refine ⟨44763007551486324668834903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29842005034324216445889935 44763007551486324668834903)
          ·
            refine ⟨67144511327229487003252355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44763007551486324668834903 67144511327229487003252355)
            ·
              refine ⟨100716766990844230504878533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67144511327229487003252355 100716766990844230504878533)
              ·
                refine ⟨18884393810783293219664725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100716766990844230504878533 18884393810783293219664725)
                ·
                  refine ⟨110650744985058358708973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18884393810783293219664725 110650744985058358708973)
                  ·
                    rfl

theorem cell23_1939424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 9].length) (baseStart_1939424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939424 prefixEnd_1939424 := by exact prefixLift 1939424
  have htrace : WordTrace (prefixWord ++ tailWord_1939424) baseStart_1939424 baseEnd_1939424 := by
    simpa [prefixWord, tailWord_1939424, baseEnd_1939424] using wordTrace_append hprefix tailTrace_1939424
  have hstable : (prefixWord ++ tailWord_1939424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939424).length < 2 ^ (prefixWord ++ tailWord_1939424).sum := by decide
  have hdescent : baseEnd_1939424 < baseStart_1939424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939446 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_1939446 : Nat := 118140960795 + 1939446 * 2 ^ 59
def prefixEnd_1939446 : Nat := 4983230072969 + 3 ^ 40 * 1939446 * 2
def baseEnd_1939446 : Nat := 995868001439924142305657

theorem tailTrace_1939446 : CollatzResearch.WordTrace tailWord_1939446 prefixEnd_1939446 995868001439924142305657 := by
  unfold tailWord_1939446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4421087933232865490703887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47158271287817231900841461 4421087933232865490703887)
  ·
    refine ⟨6631631899849298236055831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4421087933232865490703887 6631631899849298236055831)
    ·
      refine ⟨9947447849773947354083747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6631631899849298236055831 9947447849773947354083747)
      ·
        refine ⟨14921171774660921031125621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9947447849773947354083747 14921171774660921031125621)
        ·
          refine ⟨1398859853874461346668027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14921171774660921031125621 1398859853874461346668027)
          ·
            refine ⟨2098289780811692020002041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398859853874461346668027 2098289780811692020002041)
            ·
              refine ⟨1573717335608769015001531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098289780811692020002041 1573717335608769015001531)
              ·
                refine ⟨2360576003413153522502297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573717335608769015001531 2360576003413153522502297)
                ·
                  refine ⟨1770432002559865141876723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2360576003413153522502297 1770432002559865141876723)
                  ·
                    refine ⟨2655648003839797712815085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1770432002559865141876723 2655648003839797712815085)
                    ·
                      refine ⟨995868001439924142305657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655648003839797712815085 995868001439924142305657)
                      ·
                        rfl

theorem cell23_1939446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_1939446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939446 prefixEnd_1939446 := by exact prefixLift 1939446
  have htrace : WordTrace (prefixWord ++ tailWord_1939446) baseStart_1939446 baseEnd_1939446 := by
    simpa [prefixWord, tailWord_1939446, baseEnd_1939446] using wordTrace_append hprefix tailTrace_1939446
  have hstable : (prefixWord ++ tailWord_1939446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939446).length < 2 ^ (prefixWord ++ tailWord_1939446).sum := by decide
  have hdescent : baseEnd_1939446 < baseStart_1939446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939451 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 3]
def baseStart_1939451 : Nat := 118140960795 + 1939451 * 2 ^ 59
def prefixEnd_1939451 : Nat := 4983230072969 + 3 ^ 40 * 1939451 * 2
def baseEnd_1939451 : Nat := 995870568843196622743133

theorem tailTrace_1939451 : CollatzResearch.WordTrace tailWord_1939451 prefixEnd_1939451 995870568843196622743133 := by
  unfold tailWord_1939451
  simp only [CollatzResearch.WordTrace]
  refine ⟨70737589296707733705194207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47158392864471822470129471 70737589296707733705194207)
  ·
    refine ⟨106106383945061600557791311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70737589296707733705194207 106106383945061600557791311)
    ·
      refine ⟨159159575917592400836686967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106106383945061600557791311 159159575917592400836686967)
      ·
        refine ⟨238739363876388601255030451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159159575917592400836686967 238739363876388601255030451)
        ·
          refine ⟨358109045814582901882545677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238739363876388601255030451 358109045814582901882545677)
          ·
            refine ⟨134290892180468588205954629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358109045814582901882545677 134290892180468588205954629)
            ·
              refine ⟨25179542283837860288616493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134290892180468588205954629 25179542283837860288616493)
              ·
                refine ⟨9442328356439197608231185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25179542283837860288616493 9442328356439197608231185)
                ·
                  refine ⟨7081746267329398206173389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9442328356439197608231185 7081746267329398206173389)
                  ·
                    refine ⟨2655654850248524327315021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7081746267329398206173389 2655654850248524327315021)
                    ·
                      refine ⟨995870568843196622743133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655654850248524327315021 995870568843196622743133)
                      ·
                        rfl

theorem cell23_1939451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 3].length) (baseStart_1939451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939451 prefixEnd_1939451 := by exact prefixLift 1939451
  have htrace : WordTrace (prefixWord ++ tailWord_1939451) baseStart_1939451 baseEnd_1939451 := by
    simpa [prefixWord, tailWord_1939451, baseEnd_1939451] using wordTrace_append hprefix tailTrace_1939451
  have hstable : (prefixWord ++ tailWord_1939451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939451).length < 2 ^ (prefixWord ++ tailWord_1939451).sum := by decide
  have hdescent : baseEnd_1939451 < baseStart_1939451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939498 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1939498 : Nat := 118140960795 + 1939498 * 2 ^ 59
def prefixEnd_1939498 : Nat := 4983230072969 + 3 ^ 40 * 1939498 * 2
def baseEnd_1939498 : Nat := 995894702433957938855417

theorem tailTrace_1939498 : CollatzResearch.WordTrace tailWord_1939498 prefixEnd_1939498 995894702433957938855417 := by
  unfold tailWord_1939498
  simp only [CollatzResearch.WordTrace]
  refine ⟨17684825881884365183038787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47159535685024973821436765 17684825881884365183038787)
  ·
    refine ⟨26527238822826547774558181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17684825881884365183038787 26527238822826547774558181)
    ·
      refine ⟨4973857279279977707729659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26527238822826547774558181 4973857279279977707729659)
      ·
        refine ⟨7460785918919966561594489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973857279279977707729659 7460785918919966561594489)
        ·
          refine ⟨5595589439189974921195867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7460785918919966561594489 5595589439189974921195867)
          ·
            refine ⟨8393384158784962381793801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5595589439189974921195867 8393384158784962381793801)
            ·
              refine ⟨6295038119088721786345351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8393384158784962381793801 6295038119088721786345351)
              ·
                refine ⟨9442557178633082679518027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295038119088721786345351 9442557178633082679518027)
                ·
                  refine ⟨14163835767949624019277041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9442557178633082679518027 14163835767949624019277041)
                  ·
                    refine ⟨10622876825962218014457781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14163835767949624019277041 10622876825962218014457781)
                    ·
                      refine ⟨995894702433957938855417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10622876825962218014457781 995894702433957938855417)
                      ·
                        rfl

theorem cell23_1939498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1939498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939498 prefixEnd_1939498 := by exact prefixLift 1939498
  have htrace : WordTrace (prefixWord ++ tailWord_1939498) baseStart_1939498 baseEnd_1939498 := by
    simpa [prefixWord, tailWord_1939498, baseEnd_1939498] using wordTrace_append hprefix tailTrace_1939498
  have hstable : (prefixWord ++ tailWord_1939498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939498).length < 2 ^ (prefixWord ++ tailWord_1939498).sum := by decide
  have hdescent : baseEnd_1939498 < baseStart_1939498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939528 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_1939528 : Nat := 118140960795 + 1939528 * 2 ^ 59
def prefixEnd_1939528 : Nat := 4983230072969 + 3 ^ 40 * 1939528 * 2
def baseEnd_1939528 : Nat := 995910106853592821480279

theorem tailTrace_1939528 : CollatzResearch.WordTrace tailWord_1939528 prefixEnd_1939528 995910106853592821480279 := by
  unfold tailWord_1939528
  simp only [CollatzResearch.WordTrace]
  refine ⟨35370198858714387927873619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47160265144952517237164825 35370198858714387927873619)
  ·
    refine ⟨53055298288071581891810429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35370198858714387927873619 53055298288071581891810429)
    ·
      refine ⟨19895736858026843209428911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53055298288071581891810429 19895736858026843209428911)
      ·
        refine ⟨29843605287040264814143367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19895736858026843209428911 29843605287040264814143367)
        ·
          refine ⟨44765407930560397221215051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29843605287040264814143367 44765407930560397221215051)
          ·
            refine ⟨67148111895840595831822577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44765407930560397221215051 67148111895840595831822577)
            ·
              refine ⟨50361083921880446873866933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67148111895840595831822577 50361083921880446873866933)
              ·
                refine ⟨4721351617676291894425025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50361083921880446873866933 4721351617676291894425025)
                ·
                  refine ⟨3541013713257218920818769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721351617676291894425025 3541013713257218920818769)
                  ·
                    refine ⟨2655760284942914190614077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3541013713257218920818769 2655760284942914190614077)
                    ·
                      refine ⟨995910106853592821480279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655760284942914190614077 995910106853592821480279)
                      ·
                        rfl

theorem cell23_1939528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_1939528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939528 prefixEnd_1939528 := by exact prefixLift 1939528
  have htrace : WordTrace (prefixWord ++ tailWord_1939528) baseStart_1939528 baseEnd_1939528 := by
    simpa [prefixWord, tailWord_1939528, baseEnd_1939528] using wordTrace_append hprefix tailTrace_1939528
  have hstable : (prefixWord ++ tailWord_1939528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939528).length < 2 ^ (prefixWord ++ tailWord_1939528).sum := by decide
  have hdescent : baseEnd_1939528 < baseStart_1939528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939548 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 8]
def baseStart_1939548 : Nat := 118140960795 + 1939548 * 2 ^ 59
def prefixEnd_1939548 : Nat := 4983230072969 + 3 ^ 40 * 1939548 * 2
def baseEnd_1939548 : Nat := 110657819607409193692243

theorem tailTrace_1939548 : CollatzResearch.WordTrace tailWord_1939548 prefixEnd_1939548 110657819607409193692243 := by
  unfold tailWord_1939548
  simp only [CollatzResearch.WordTrace]
  refine ⟨35370563588678159635737649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47160751451570879514316865 35370563588678159635737649)
  ·
    refine ⟨26527922691508619726803237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35370563588678159635737649 26527922691508619726803237)
    ·
      refine ⟨4973985504657866198775607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26527922691508619726803237 4973985504657866198775607)
      ·
        refine ⟨7460978256986799298163411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973985504657866198775607 7460978256986799298163411)
        ·
          refine ⟨11191467385480198947245117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460978256986799298163411 11191467385480198947245117)
          ·
            refine ⟨4196800269555074605216919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11191467385480198947245117 4196800269555074605216919)
            ·
              refine ⟨6295200404332611907825379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4196800269555074605216919 6295200404332611907825379)
              ·
                refine ⟨9442800606498917861738069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295200404332611907825379 9442800606498917861738069)
                ·
                  refine ⟨110657819607409193692243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9442800606498917861738069 110657819607409193692243)
                  ·
                    rfl

theorem cell23_1939548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_1939548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939548 prefixEnd_1939548 := by exact prefixLift 1939548
  have htrace : WordTrace (prefixWord ++ tailWord_1939548) baseStart_1939548 baseEnd_1939548 := by
    simpa [prefixWord, tailWord_1939548, baseEnd_1939548] using wordTrace_append hprefix tailTrace_1939548
  have hstable : (prefixWord ++ tailWord_1939548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939548).length < 2 ^ (prefixWord ++ tailWord_1939548).sum := by decide
  have hdescent : baseEnd_1939548 < baseStart_1939548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939565 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 6]
def baseStart_1939565 : Nat := 118140960795 + 1939565 * 2 ^ 59
def prefixEnd_1939565 : Nat := 4983230072969 + 3 ^ 40 * 1939565 * 2
def baseEnd_1939565 : Nat := 110658789515312130746401

theorem tailTrace_1939565 : CollatzResearch.WordTrace tailWord_1939565 prefixEnd_1939565 110658789515312130746401 := by
  unfold tailWord_1939565
  simp only [CollatzResearch.WordTrace]
  refine ⟨70741747218294731174844149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47161164812196487449896099 70741747218294731174844149)
  ·
    refine ⟨6632038801715131047641639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70741747218294731174844149 6632038801715131047641639)
    ·
      refine ⟨9948058202572696571462459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6632038801715131047641639 9948058202572696571462459)
      ·
        refine ⟨14922087303859044857193689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9948058202572696571462459 14922087303859044857193689)
        ·
          refine ⟨11191565477894283642895267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14922087303859044857193689 11191565477894283642895267)
          ·
            refine ⟨16787348216841425464342901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11191565477894283642895267 16787348216841425464342901)
            ·
              refine ⟨1573813895328883637282147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16787348216841425464342901 1573813895328883637282147)
              ·
                refine ⟨2360720842993325455923221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1573813895328883637282147 2360720842993325455923221)
                ·
                  refine ⟨110658789515312130746401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2360720842993325455923221 110658789515312130746401)
                  ·
                    rfl

theorem cell23_1939565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_1939565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939565 prefixEnd_1939565 := by exact prefixLift 1939565
  have htrace : WordTrace (prefixWord ++ tailWord_1939565) baseStart_1939565 baseEnd_1939565 := by
    simpa [prefixWord, tailWord_1939565, baseEnd_1939565] using wordTrace_append hprefix tailTrace_1939565
  have hstable : (prefixWord ++ tailWord_1939565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939565).length < 2 ^ (prefixWord ++ tailWord_1939565).sum := by decide
  have hdescent : baseEnd_1939565 < baseStart_1939565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939575 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 3, 1, 3]
def baseStart_1939575 : Nat := 118140960795 + 1939575 * 2 ^ 59
def prefixEnd_1939575 : Nat := 4983230072969 + 3 ^ 40 * 1939575 * 2
def baseEnd_1939575 : Nat := 995934240444354137592563

theorem tailTrace_1939575 : CollatzResearch.WordTrace tailWord_1939575 prefixEnd_1939575 995934240444354137592563 := by
  unfold tailWord_1939575
  simp only [CollatzResearch.WordTrace]
  refine ⟨70742111948258502882708179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47161407965505668588472119 70742111948258502882708179)
  ·
    refine ⟨106113167922387754324062269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70742111948258502882708179 106113167922387754324062269)
    ·
      refine ⟨39792437970895407871523351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106113167922387754324062269 39792437970895407871523351)
      ·
        refine ⟨59688656956343111807285027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39792437970895407871523351 59688656956343111807285027)
        ·
          refine ⟨89532985434514667710927541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59688656956343111807285027 89532985434514667710927541)
          ·
            refine ⟨8393717384485750097899457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89532985434514667710927541 8393717384485750097899457)
            ·
              refine ⟨6295288038364312573424593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8393717384485750097899457 6295288038364312573424593)
              ·
                refine ⟨4721466028773234430068445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295288038364312573424593 4721466028773234430068445)
                ·
                  refine ⟨1770549760789962911275667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4721466028773234430068445 1770549760789962911275667)
                  ·
                    refine ⟨2655824641184944366913501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1770549760789962911275667 2655824641184944366913501)
                    ·
                      refine ⟨995934240444354137592563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655824641184944366913501 995934240444354137592563)
                      ·
                        rfl

theorem cell23_1939575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_1939575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939575 prefixEnd_1939575 := by exact prefixLift 1939575
  have htrace : WordTrace (prefixWord ++ tailWord_1939575) baseStart_1939575 baseEnd_1939575 := by
    simpa [prefixWord, tailWord_1939575, baseEnd_1939575] using wordTrace_append hprefix tailTrace_1939575
  have hstable : (prefixWord ++ tailWord_1939575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939575).length < 2 ^ (prefixWord ++ tailWord_1939575).sum := by decide
  have hdescent : baseEnd_1939575 < baseStart_1939575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939602 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_1939602 : Nat := 118140960795 + 1939602 * 2 ^ 59
def prefixEnd_1939602 : Nat := 4983230072969 + 3 ^ 40 * 1939602 * 2
def baseEnd_1939602 : Nat := 995948104422025531954939

theorem tailTrace_1939602 : CollatzResearch.WordTrace tailWord_1939602 prefixEnd_1939602 995948104422025531954939 := by
  unfold tailWord_1939602
  simp only [CollatzResearch.WordTrace]
  refine ⟨17685774179790171623485265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47162064479440457662627373 17685774179790171623485265)
  ·
    refine ⟨13264330634842628717613949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17685774179790171623485265 13264330634842628717613949)
    ·
      refine ⟨4974123988065985769105231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13264330634842628717613949 4974123988065985769105231)
      ·
        refine ⟨7461185982098978653657847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4974123988065985769105231 7461185982098978653657847)
        ·
          refine ⟨11191778973148467980486771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7461185982098978653657847 11191778973148467980486771)
          ·
            refine ⟨16787668459722701970730157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11191778973148467980486771 16787668459722701970730157)
            ·
              refine ⟨6295375672396013239023809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16787668459722701970730157 6295375672396013239023809)
              ·
                refine ⟨4721531754297009929267857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295375672396013239023809 4721531754297009929267857)
                ·
                  refine ⟨3541148815722757446950893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721531754297009929267857 3541148815722757446950893)
                  ·
                    refine ⟨1327930805896034042606585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541148815722757446950893 1327930805896034042606585)
                    ·
                      refine ⟨995948104422025531954939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327930805896034042606585 995948104422025531954939)
                      ·
                        rfl

theorem cell23_1939602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_1939602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939602 prefixEnd_1939602 := by exact prefixLift 1939602
  have htrace : WordTrace (prefixWord ++ tailWord_1939602) baseStart_1939602 baseEnd_1939602 := by
    simpa [prefixWord, tailWord_1939602, baseEnd_1939602] using wordTrace_append hprefix tailTrace_1939602
  have hstable : (prefixWord ++ tailWord_1939602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939602).length < 2 ^ (prefixWord ++ tailWord_1939602).sum := by decide
  have hdescent : baseEnd_1939602 < baseStart_1939602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939611 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 6]
def baseStart_1939611 : Nat := 118140960795 + 1939611 * 2 ^ 59
def prefixEnd_1939611 : Nat := 4983230072969 + 3 ^ 40 * 1939611 * 2
def baseEnd_1939611 : Nat := 995952725747915996742397

theorem tailTrace_1939611 : CollatzResearch.WordTrace tailWord_1939611 prefixEnd_1939611 995952725747915996742397 := by
  unfold tailWord_1939611
  simp only [CollatzResearch.WordTrace]
  refine ⟨70743424976128081031018687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47162283317418720687345791 70743424976128081031018687)
  ·
    refine ⟨106115137464192121546528031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70743424976128081031018687 106115137464192121546528031)
    ·
      refine ⟨159172706196288182319792047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106115137464192121546528031 159172706196288182319792047)
      ·
        refine ⟨238759059294432273479688071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159172706196288182319792047 238759059294432273479688071)
        ·
          refine ⟨358138588941648410219532107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238759059294432273479688071 358138588941648410219532107)
          ·
            refine ⟨537207883412472615329298161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358138588941648410219532107 537207883412472615329298161)
            ·
              refine ⟨402905912559354461496973621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537207883412472615329298161 402905912559354461496973621)
              ·
                refine ⟨37772429302439480765341277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 402905912559354461496973621 37772429302439480765341277)
                ·
                  refine ⟨14164660988414805287002979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37772429302439480765341277 14164660988414805287002979)
                  ·
                    refine ⟨21246991482622207930504469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14164660988414805287002979 21246991482622207930504469)
                    ·
                      refine ⟨995952725747915996742397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21246991482622207930504469 995952725747915996742397)
                      ·
                        rfl

theorem cell23_1939611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_1939611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939611 prefixEnd_1939611 := by exact prefixLift 1939611
  have htrace : WordTrace (prefixWord ++ tailWord_1939611) baseStart_1939611 baseEnd_1939611 := by
    simpa [prefixWord, tailWord_1939611, baseEnd_1939611] using wordTrace_append hprefix tailTrace_1939611
  have hstable : (prefixWord ++ tailWord_1939611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939611).length < 2 ^ (prefixWord ++ tailWord_1939611).sum := by decide
  have hdescent : baseEnd_1939611 < baseStart_1939611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939652 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1939652 : Nat := 118140960795 + 1939652 * 2 ^ 59
def prefixEnd_1939652 : Nat := 4983230072969 + 3 ^ 40 * 1939652 * 2
def baseEnd_1939652 : Nat := 995973778454750336329709

theorem tailTrace_1939652 : CollatzResearch.WordTrace tailWord_1939652 prefixEnd_1939652 995973778454750336329709 := by
  unfold tailWord_1939652
  simp only [CollatzResearch.WordTrace]
  refine ⟨35372460184489772516630605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47163280245986363355507473 35372460184489772516630605)
  ·
    refine ⟨13264672569183664693736477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35372460184489772516630605 13264672569183664693736477)
    ·
      refine ⟨4974252213443874260151179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13264672569183664693736477 4974252213443874260151179)
      ·
        refine ⟨7461378320165811390226769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4974252213443874260151179 7461378320165811390226769)
        ·
          refine ⟨5596033740124358542670077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7461378320165811390226769 5596033740124358542670077)
          ·
            refine ⟨2098512652546634453501279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5596033740124358542670077 2098512652546634453501279)
            ·
              refine ⟨3147768978819951680251919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098512652546634453501279 3147768978819951680251919)
              ·
                refine ⟨4721653468229927520377879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3147768978819951680251919 4721653468229927520377879)
                ·
                  refine ⟨7082480202344891280566819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721653468229927520377879 7082480202344891280566819)
                  ·
                    refine ⟨10623720303517336920850229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7082480202344891280566819 10623720303517336920850229)
                    ·
                      refine ⟨995973778454750336329709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10623720303517336920850229 995973778454750336329709)
                      ·
                        rfl

theorem cell23_1939652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1939652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939652 prefixEnd_1939652 := by exact prefixLift 1939652
  have htrace : WordTrace (prefixWord ++ tailWord_1939652) baseStart_1939652 baseEnd_1939652 := by
    simpa [prefixWord, tailWord_1939652, baseEnd_1939652] using wordTrace_append hprefix tailTrace_1939652
  have hstable : (prefixWord ++ tailWord_1939652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939652).length < 2 ^ (prefixWord ++ tailWord_1939652).sum := by decide
  have hdescent : baseEnd_1939652 < baseStart_1939652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939660 : List Nat := [2, 2, 1, 6, 2, 1, 2, 2, 1, 1, 3]
def baseStart_1939660 : Nat := 118140960795 + 1939660 * 2 ^ 59
def prefixEnd_1939660 : Nat := 4983230072969 + 3 ^ 40 * 1939660 * 2
def baseEnd_1939660 : Nat := 995977886299986305029673

theorem tailTrace_1939660 : CollatzResearch.WordTrace tailWord_1939660 prefixEnd_1939660 995977886299986305029673 := by
  unfold tailWord_1939660
  simp only [CollatzResearch.WordTrace]
  refine ⟨35372606076475281199776217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47163474768633708266368289 35372606076475281199776217)
  ·
    refine ⟨26529454557356460899832163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35372606076475281199776217 26529454557356460899832163)
    ·
      refine ⟨39794181836034691349748245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26529454557356460899832163 39794181836034691349748245)
      ·
        refine ⟨1865352273564126157019449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39794181836034691349748245 1865352273564126157019449)
        ·
          refine ⟨1399014205173094617764587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1865352273564126157019449 1399014205173094617764587)
          ·
            refine ⟨2098521307759641926646881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399014205173094617764587 2098521307759641926646881)
            ·
              refine ⟨1573890980819731444985161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098521307759641926646881 1573890980819731444985161)
              ·
                refine ⟨1180418235614798583738871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573890980819731444985161 1180418235614798583738871)
                ·
                  refine ⟨1770627353422197875608307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180418235614798583738871 1770627353422197875608307)
                  ·
                    refine ⟨2655941030133296813412461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1770627353422197875608307 2655941030133296813412461)
                    ·
                      refine ⟨995977886299986305029673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655941030133296813412461 995977886299986305029673)
                      ·
                        rfl

theorem cell23_1939660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_1939660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939660 prefixEnd_1939660 := by exact prefixLift 1939660
  have htrace : WordTrace (prefixWord ++ tailWord_1939660) baseStart_1939660 baseEnd_1939660 := by
    simpa [prefixWord, tailWord_1939660, baseEnd_1939660] using wordTrace_append hprefix tailTrace_1939660
  have hstable : (prefixWord ++ tailWord_1939660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939660).length < 2 ^ (prefixWord ++ tailWord_1939660).sum := by decide
  have hdescent : baseEnd_1939660 < baseStart_1939660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939665 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 4, 1, 3]
def baseStart_1939665 : Nat := 118140960795 + 1939665 * 2 ^ 59
def prefixEnd_1939665 : Nat := 4983230072969 + 3 ^ 40 * 1939665 * 2
def baseEnd_1939665 : Nat := 995980453703258785467149

theorem tailTrace_1939665 : CollatzResearch.WordTrace tailWord_1939665 prefixEnd_1939665 995980453703258785467149 := by
  unfold tailWord_1939665
  simp only [CollatzResearch.WordTrace]
  refine ⟨70745394517932448253484449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47163596345288298835656299 70745394517932448253484449)
  ·
    refine ⟨53059045888449336190113337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70745394517932448253484449 53059045888449336190113337)
    ·
      refine ⟨39794284416337002142585003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53059045888449336190113337 39794284416337002142585003)
      ·
        refine ⟨59691426624505503213877505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39794284416337002142585003 59691426624505503213877505)
        ·
          refine ⟨44768569968379127410408129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59691426624505503213877505 44768569968379127410408129)
          ·
            refine ⟨33576427476284345557806097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44768569968379127410408129 33576427476284345557806097)
            ·
              refine ⟨25182320607213259168354573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33576427476284345557806097 25182320607213259168354573)
              ·
                refine ⟨9443370227704972188132965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25182320607213259168354573 9443370227704972188132965)
                ·
                  refine ⟨1770631917694682285274931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9443370227704972188132965 1770631917694682285274931)
                  ·
                    refine ⟨2655947876542023427912397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1770631917694682285274931 2655947876542023427912397)
                    ·
                      refine ⟨995980453703258785467149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2655947876542023427912397 995980453703258785467149)
                      ·
                        rfl

theorem cell23_1939665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_1939665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939665 prefixEnd_1939665 := by exact prefixLift 1939665
  have htrace : WordTrace (prefixWord ++ tailWord_1939665) baseStart_1939665 baseEnd_1939665 := by
    simpa [prefixWord, tailWord_1939665, baseEnd_1939665] using wordTrace_append hprefix tailTrace_1939665
  have hstable : (prefixWord ++ tailWord_1939665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939665).length < 2 ^ (prefixWord ++ tailWord_1939665).sum := by decide
  have hdescent : baseEnd_1939665 < baseStart_1939665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939666 : List Nat := [3, 2, 2, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_1939666 : Nat := 118140960795 + 1939666 * 2 ^ 59
def prefixEnd_1939666 : Nat := 4983230072969 + 3 ^ 40 * 1939666 * 2
def baseEnd_1939666 : Nat := 995980967183913281554645

theorem tailTrace_1939666 : CollatzResearch.WordTrace tailWord_1939666 prefixEnd_1939666 995980967183913281554645 := by
  unfold tailWord_1939666
  simp only [CollatzResearch.WordTrace]
  refine ⟨17686357747732206356067713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47163620660619216949513901 17686357747732206356067713)
  ·
    refine ⟨13264768310799154767050785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17686357747732206356067713 13264768310799154767050785)
    ·
      refine ⟨9948576233099366075288089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13264768310799154767050785 9948576233099366075288089)
      ·
        refine ⟨7461432174824524556466067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9948576233099366075288089 7461432174824524556466067)
        ·
          refine ⟨11192148262236786834699101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7461432174824524556466067 11192148262236786834699101)
          ·
            refine ⟨4197055598338795063012163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11192148262236786834699101 4197055598338795063012163)
            ·
              refine ⟨6295583397508192594518245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4197055598338795063012163 6295583397508192594518245)
              ·
                refine ⟨1180421887032786111472171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6295583397508192594518245 1180421887032786111472171)
                ·
                  refine ⟨1770632830549179167208257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180421887032786111472171 1770632830549179167208257)
                  ·
                    refine ⟨1327974622911884375406193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1770632830549179167208257 1327974622911884375406193)
                    ·
                      refine ⟨995980967183913281554645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327974622911884375406193 995980967183913281554645)
                      ·
                        rfl

theorem cell23_1939666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_1939666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939666 prefixEnd_1939666 := by exact prefixLift 1939666
  have htrace : WordTrace (prefixWord ++ tailWord_1939666) baseStart_1939666 baseEnd_1939666 := by
    simpa [prefixWord, tailWord_1939666, baseEnd_1939666] using wordTrace_append hprefix tailTrace_1939666
  have hstable : (prefixWord ++ tailWord_1939666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939666).length < 2 ^ (prefixWord ++ tailWord_1939666).sum := by decide
  have hdescent : baseEnd_1939666 < baseStart_1939666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939675 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 3, 3, 2]
def baseStart_1939675 : Nat := 118140960795 + 1939675 * 2 ^ 59
def prefixEnd_1939675 : Nat := 4983230072969 + 3 ^ 40 * 1939675 * 2
def baseEnd_1939675 : Nat := 995985588509803746342103

theorem tailTrace_1939675 : CollatzResearch.WordTrace tailWord_1939675 prefixEnd_1939675 995985588509803746342103 := by
  unfold tailWord_1939675
  simp only [CollatzResearch.WordTrace]
  refine ⟨70745759247896219961348479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47163839498597479974232319 70745759247896219961348479)
  ·
    refine ⟨106118638871844329942022719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70745759247896219961348479 106118638871844329942022719)
    ·
      refine ⟨159177958307766494913034079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106118638871844329942022719 159177958307766494913034079)
      ·
        refine ⟨238766937461649742369551119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159177958307766494913034079 238766937461649742369551119)
        ·
          refine ⟨358150406192474613554326679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238766937461649742369551119 358150406192474613554326679)
          ·
            refine ⟨537225609288711920331490019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358150406192474613554326679 537225609288711920331490019)
            ·
              refine ⟨805838413933067880497235029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537225609288711920331490019 805838413933067880497235029)
              ·
                refine ⟨9443418913278139224576973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 805838413933067880497235029 9443418913278139224576973)
                ·
                  refine ⟨3541282092479302209216365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9443418913278139224576973 3541282092479302209216365)
                  ·
                    refine ⟨1327980784679738328456137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541282092479302209216365 1327980784679738328456137)
                    ·
                      refine ⟨995985588509803746342103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327980784679738328456137 995985588509803746342103)
                      ·
                        rfl

theorem cell23_1939675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 3, 2].length) (baseStart_1939675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939675 prefixEnd_1939675 := by exact prefixLift 1939675
  have htrace : WordTrace (prefixWord ++ tailWord_1939675) baseStart_1939675 baseEnd_1939675 := by
    simpa [prefixWord, tailWord_1939675, baseEnd_1939675] using wordTrace_append hprefix tailTrace_1939675
  have hstable : (prefixWord ++ tailWord_1939675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939675).length < 2 ^ (prefixWord ++ tailWord_1939675).sum := by decide
  have hdescent : baseEnd_1939675 < baseStart_1939675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939692 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 1, 3, 2]
def baseStart_1939692 : Nat := 118140960795 + 1939692 * 2 ^ 59
def prefixEnd_1939692 : Nat := 4983230072969 + 3 ^ 40 * 1939692 * 2
def baseEnd_1939692 : Nat := 995994317680930179829525

theorem tailTrace_1939692 : CollatzResearch.WordTrace tailWord_1939692 prefixEnd_1939692 995994317680930179829525 := by
  unfold tailWord_1939692
  simp only [CollatzResearch.WordTrace]
  refine ⟨35373189644417315932358665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47164252859223087909811553 35373189644417315932358665)
  ·
    refine ⟨26529892233312986949268999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35373189644417315932358665 26529892233312986949268999)
    ·
      refine ⟨39794838349969480423903499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26529892233312986949268999 39794838349969480423903499)
      ·
        refine ⟨59692257524954220635855249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39794838349969480423903499 59692257524954220635855249)
        ·
          refine ⟨44769193143715665476891437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59692257524954220635855249 44769193143715665476891437)
          ·
            refine ⟨16788447428893374553834289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44769193143715665476891437 16788447428893374553834289)
            ·
              refine ⟨12591335571670030915375717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16788447428893374553834289 12591335571670030915375717)
              ·
                refine ⟨2360875419688130796632947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12591335571670030915375717 2360875419688130796632947)
                ·
                  refine ⟨3541313129532196194949421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360875419688130796632947 3541313129532196194949421)
                  ·
                    refine ⟨1327992423574573573106033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3541313129532196194949421 1327992423574573573106033)
                    ·
                      refine ⟨995994317680930179829525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327992423574573573106033 995994317680930179829525)
                      ·
                        rfl

theorem cell23_1939692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 3, 2].length) (baseStart_1939692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939692 prefixEnd_1939692 := by exact prefixLift 1939692
  have htrace : WordTrace (prefixWord ++ tailWord_1939692) baseStart_1939692 baseEnd_1939692 := by
    simpa [prefixWord, tailWord_1939692, baseEnd_1939692] using wordTrace_append hprefix tailTrace_1939692
  have hstable : (prefixWord ++ tailWord_1939692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939692).length < 2 ^ (prefixWord ++ tailWord_1939692).sum := by decide
  have hdescent : baseEnd_1939692 < baseStart_1939692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939705 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 3, 4, 2]
def baseStart_1939705 : Nat := 118140960795 + 1939705 * 2 ^ 59
def prefixEnd_1939705 : Nat := 4983230072969 + 3 ^ 40 * 1939705 * 2
def baseEnd_1939705 : Nat := 996000992929438628966965

theorem tailTrace_1939705 : CollatzResearch.WordTrace tailWord_1939705 prefixEnd_1939705 996000992929438628966965 := by
  unfold tailWord_1939705
  simp only [CollatzResearch.WordTrace]
  refine ⟨70746853437787535084940569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47164568958525023389960379 70746853437787535084940569)
  ·
    refine ⟨53060140078340651313705427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70746853437787535084940569 53060140078340651313705427)
    ·
      refine ⟨79590210117510976970558141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53060140078340651313705427 79590210117510976970558141)
      ·
        refine ⟨29846328794066616363959303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79590210117510976970558141 29846328794066616363959303)
        ·
          refine ⟨44769493191099924545938955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29846328794066616363959303 44769493191099924545938955)
          ·
            refine ⟨67154239786649886818908433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44769493191099924545938955 67154239786649886818908433)
            ·
              refine ⟨50365679839987415114181325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67154239786649886818908433 50365679839987415114181325)
              ·
                refine ⟨18887129939995280667817997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50365679839987415114181325 18887129939995280667817997)
                ·
                  refine ⟨7082673727498230250431749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18887129939995280667817997 7082673727498230250431749)
                  ·
                    refine ⟨1328001323905918171955953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7082673727498230250431749 1328001323905918171955953)
                    ·
                      refine ⟨996000992929438628966965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1328001323905918171955953 996000992929438628966965)
                      ·
                        rfl

theorem cell23_1939705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_1939705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939705 prefixEnd_1939705 := by exact prefixLift 1939705
  have htrace : WordTrace (prefixWord ++ tailWord_1939705) baseStart_1939705 baseEnd_1939705 := by
    simpa [prefixWord, tailWord_1939705, baseEnd_1939705] using wordTrace_append hprefix tailTrace_1939705
  have hstable : (prefixWord ++ tailWord_1939705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939705).length < 2 ^ (prefixWord ++ tailWord_1939705).sum := by decide
  have hdescent : baseEnd_1939705 < baseStart_1939705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939716 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1939716 : Nat := 118140960795 + 1939716 * 2 ^ 59
def prefixEnd_1939716 : Nat := 4983230072969 + 3 ^ 40 * 1939716 * 2
def baseEnd_1939716 : Nat := 996006641216638085929415

theorem tailTrace_1939716 : CollatzResearch.WordTrace tailWord_1939716 prefixEnd_1939716 996006641216638085929415 := by
  unfold tailWord_1939716
  simp only [CollatzResearch.WordTrace]
  refine ⟨35373627320373841981795501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47164836427165122642394001 35373627320373841981795501)
  ·
    refine ⟨13265110245140190743173313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35373627320373841981795501 13265110245140190743173313)
    ·
      refine ⟨9948832683855143057379985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13265110245140190743173313 9948832683855143057379985)
      ·
        refine ⟨7461624512891357293034989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9948832683855143057379985 7461624512891357293034989)
        ·
          refine ⟨2798109192334258984888121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7461624512891357293034989 2798109192334258984888121)
          ·
            refine ⟨2098581894250694238666091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2798109192334258984888121 2098581894250694238666091)
            ·
              refine ⟨3147872841376041357999137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098581894250694238666091 3147872841376041357999137)
              ·
                refine ⟨2360904631032031018499353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3147872841376041357999137 2360904631032031018499353)
                ·
                  refine ⟨1770678473274023263874515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2360904631032031018499353 1770678473274023263874515)
                  ·
                    refine ⟨2656017709911034895811773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1770678473274023263874515 2656017709911034895811773)
                    ·
                      refine ⟨996006641216638085929415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2656017709911034895811773 996006641216638085929415)
                      ·
                        rfl

theorem cell23_1939716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1939716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939716 prefixEnd_1939716 := by exact prefixLift 1939716
  have htrace : WordTrace (prefixWord ++ tailWord_1939716) baseStart_1939716 baseEnd_1939716 := by
    simpa [prefixWord, tailWord_1939716, baseEnd_1939716] using wordTrace_append hprefix tailTrace_1939716
  have hstable : (prefixWord ++ tailWord_1939716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939716).length < 2 ^ (prefixWord ++ tailWord_1939716).sum := by decide
  have hdescent : baseEnd_1939716 < baseStart_1939716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939735 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1939735 : Nat := 118140960795 + 1939735 * 2 ^ 59
def prefixEnd_1939735 : Nat := 4983230072969 + 3 ^ 40 * 1939735 * 2
def baseEnd_1939735 : Nat := 996016397349073511591827

theorem tailTrace_1939735 : CollatzResearch.WordTrace tailWord_1939735 prefixEnd_1939735 996016397349073511591827 := by
  unfold tailWord_1939735
  simp only [CollatzResearch.WordTrace]
  refine ⟨70747947627678850208532659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47165298418452566805688439 70747947627678850208532659)
  ·
    refine ⟨106121921441518275312798989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70747947627678850208532659 106121921441518275312798989)
    ·
      refine ⟨39795720540569353242299621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106121921441518275312798989 39795720540569353242299621)
      ·
        refine ⟨7461697601356753732931179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39795720540569353242299621 7461697601356753732931179)
        ·
          refine ⟨11192546402035130599396769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7461697601356753732931179 11192546402035130599396769)
          ·
            refine ⟨8394409801526347949547577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11192546402035130599396769 8394409801526347949547577)
            ·
              refine ⟨6295807351144760962160683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8394409801526347949547577 6295807351144760962160683)
              ·
                refine ⟨9443711026717141443241025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295807351144760962160683 9443711026717141443241025)
                ·
                  refine ⟨7082783270037856082430769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9443711026717141443241025 7082783270037856082430769)
                  ·
                    refine ⟨5312087452528392061823077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7082783270037856082430769 5312087452528392061823077)
                    ·
                      refine ⟨996016397349073511591827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5312087452528392061823077 996016397349073511591827)
                      ·
                        rfl

theorem cell23_1939735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1939735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939735 prefixEnd_1939735 := by exact prefixLift 1939735
  have htrace : WordTrace (prefixWord ++ tailWord_1939735) baseStart_1939735 baseEnd_1939735 := by
    simpa [prefixWord, tailWord_1939735, baseEnd_1939735] using wordTrace_append hprefix tailTrace_1939735
  have hstable : (prefixWord ++ tailWord_1939735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939735).length < 2 ^ (prefixWord ++ tailWord_1939735).sum := by decide
  have hdescent : baseEnd_1939735 < baseStart_1939735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939775 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 2, 5]
def baseStart_1939775 : Nat := 118140960795 + 1939775 * 2 ^ 59
def prefixEnd_1939775 : Nat := 4983230072969 + 3 ^ 40 * 1939775 * 2
def baseEnd_1939775 : Nat := 332012312191751118363881

theorem tailTrace_1939775 : CollatzResearch.WordTrace tailWord_1939775 prefixEnd_1939775 332012312191751118363881 := by
  unfold tailWord_1939775
  simp only [CollatzResearch.WordTrace]
  refine ⟨70749406547533937039988779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47166271031689291359992519 70749406547533937039988779)
  ·
    refine ⟨106124109821300905559983169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70749406547533937039988779 106124109821300905559983169)
    ·
      refine ⟨79593082365975679169987377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106124109821300905559983169 79593082365975679169987377)
      ·
        refine ⟨59694811774481759377490533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79593082365975679169987377 59694811774481759377490533)
        ·
          refine ⟨11192777207715329883279475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59694811774481759377490533 11192777207715329883279475)
          ·
            refine ⟨16789165811572994824919213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11192777207715329883279475 16789165811572994824919213)
            ·
              refine ⟨6295937179339873059344705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16789165811572994824919213 6295937179339873059344705)
              ·
                refine ⟨4721952884504904794508529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295937179339873059344705 4721952884504904794508529)
                ·
                  refine ⟨3541464663378678595881397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4721952884504904794508529 3541464663378678595881397)
                  ·
                    refine ⟨332012312191751118363881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3541464663378678595881397 332012312191751118363881)
                    ·
                      rfl

theorem cell23_1939775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_1939775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939775 prefixEnd_1939775 := by exact prefixLift 1939775
  have htrace : WordTrace (prefixWord ++ tailWord_1939775) baseStart_1939775 baseEnd_1939775 := by
    simpa [prefixWord, tailWord_1939775, baseEnd_1939775] using wordTrace_append hprefix tailTrace_1939775
  have hstable : (prefixWord ++ tailWord_1939775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939775).length < 2 ^ (prefixWord ++ tailWord_1939775).sum := by decide
  have hdescent : baseEnd_1939775 < baseStart_1939775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939812 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_1939812 : Nat := 118140960795 + 1939812 * 2 ^ 59
def prefixEnd_1939812 : Nat := 4983230072969 + 3 ^ 40 * 1939812 * 2
def baseEnd_1939812 : Nat := 996055935359469710328973

theorem tailTrace_1939812 : CollatzResearch.WordTrace tailWord_1939812 prefixEnd_1939812 996055935359469710328973 := by
  unfold tailWord_1939812
  simp only [CollatzResearch.WordTrace]
  refine ⟨35375378024199946179542845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47167170698933261572723793 35375378024199946179542845)
  ·
    refine ⟨13265766759074979817328567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35375378024199946179542845 13265766759074979817328567)
    ·
      refine ⟨19898650138612469725992851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13265766759074979817328567 19898650138612469725992851)
      ·
        refine ⟨29847975207918704588989277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19898650138612469725992851 29847975207918704588989277)
        ·
          refine ⟨11192990702969514220870979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29847975207918704588989277 11192990702969514220870979)
          ·
            refine ⟨16789486054454271331306469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11192990702969514220870979 16789486054454271331306469)
            ·
              refine ⟨3148028635210175874619963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16789486054454271331306469 3148028635210175874619963)
              ·
                refine ⟨4722042952815263811929945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148028635210175874619963 4722042952815263811929945)
                ·
                  refine ⟨3541532214611447858947459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4722042952815263811929945 3541532214611447858947459)
                  ·
                    refine ⟨5312298321917171788421189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3541532214611447858947459 5312298321917171788421189)
                    ·
                      refine ⟨996055935359469710328973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5312298321917171788421189 996055935359469710328973)
                      ·
                        rfl

theorem cell23_1939812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_1939812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939812 prefixEnd_1939812 := by exact prefixLift 1939812
  have htrace : WordTrace (prefixWord ++ tailWord_1939812) baseStart_1939812 baseEnd_1939812 := by
    simpa [prefixWord, tailWord_1939812, baseEnd_1939812] using wordTrace_append hprefix tailTrace_1939812
  have hstable : (prefixWord ++ tailWord_1939812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939812).length < 2 ^ (prefixWord ++ tailWord_1939812).sum := by decide
  have hdescent : baseEnd_1939812 < baseStart_1939812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939830 : List Nat := [5, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_1939830 : Nat := 118140960795 + 1939830 * 2 ^ 59
def prefixEnd_1939830 : Nat := 4983230072969 + 3 ^ 40 * 1939830 * 2
def baseEnd_1939830 : Nat := 110673908667916737767099

theorem tailTrace_1939830 : CollatzResearch.WordTrace tailWord_1939830 prefixEnd_1939830 110673908667916737767099 := by
  unfold tailWord_1939830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4421963285145917589577559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47167608374889787622160629 4421963285145917589577559)
  ·
    refine ⟨6632944927718876384366339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4421963285145917589577559 6632944927718876384366339)
    ·
      refine ⟨9949417391578314576549509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6632944927718876384366339 9949417391578314576549509)
      ·
        refine ⟨1865515760920933983103033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9949417391578314576549509 1865515760920933983103033)
        ·
          refine ⟨1399136820690700487327275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1865515760920933983103033 1399136820690700487327275)
          ·
            refine ⟨2098705231036050730990913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399136820690700487327275 2098705231036050730990913)
            ·
              refine ⟨1574028923277038048243185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098705231036050730990913 1574028923277038048243185)
              ·
                refine ⟨1180521692457778536182389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574028923277038048243185 1180521692457778536182389)
                ·
                  refine ⟨110673908667916737767099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1180521692457778536182389 110673908667916737767099)
                  ·
                    rfl

theorem cell23_1939830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_1939830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939830 prefixEnd_1939830 := by exact prefixLift 1939830
  have htrace : WordTrace (prefixWord ++ tailWord_1939830) baseStart_1939830 baseEnd_1939830 := by
    simpa [prefixWord, tailWord_1939830, baseEnd_1939830] using wordTrace_append hprefix tailTrace_1939830
  have hstable : (prefixWord ++ tailWord_1939830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939830).length < 2 ^ (prefixWord ++ tailWord_1939830).sum := by decide
  have hdescent : baseEnd_1939830 < baseStart_1939830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939835 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 6]
def baseStart_1939835 : Nat := 118140960795 + 1939835 * 2 ^ 59
def prefixEnd_1939835 : Nat := 4983230072969 + 3 ^ 40 * 1939835 * 2
def baseEnd_1939835 : Nat := 110674193934947013371263

theorem tailTrace_1939835 : CollatzResearch.WordTrace tailWord_1939835 prefixEnd_1939835 110674193934947013371263 := by
  unfold tailWord_1939835
  simp only [CollatzResearch.WordTrace]
  refine ⟨70751594927316567287172959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47167729951544378191448639 70751594927316567287172959)
  ·
    refine ⟨106127392390974850930759439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70751594927316567287172959 106127392390974850930759439)
    ·
      refine ⟨159191088586462276396139159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106127392390974850930759439 159191088586462276396139159)
      ·
        refine ⟨238786632879693414594208739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159191088586462276396139159 238786632879693414594208739)
        ·
          refine ⟨358179949319540121891313109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238786632879693414594208739 358179949319540121891313109)
          ·
            refine ⟨8394842562176721606827651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 358179949319540121891313109 8394842562176721606827651)
            ·
              refine ⟨12592263843265082410241477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8394842562176721606827651 12592263843265082410241477)
              ·
                refine ⟨2361049470612202951920277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12592263843265082410241477 2361049470612202951920277)
                ·
                  refine ⟨110674193934947013371263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2361049470612202951920277 110674193934947013371263)
                  ·
                    rfl

theorem cell23_1939835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 6].length) (baseStart_1939835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939835 prefixEnd_1939835 := by exact prefixLift 1939835
  have htrace : WordTrace (prefixWord ++ tailWord_1939835) baseStart_1939835 baseEnd_1939835 := by
    simpa [prefixWord, tailWord_1939835, baseEnd_1939835] using wordTrace_append hprefix tailTrace_1939835
  have hstable : (prefixWord ++ tailWord_1939835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939835).length < 2 ^ (prefixWord ++ tailWord_1939835).sum := by decide
  have hdescent : baseEnd_1939835 < baseStart_1939835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939845 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 2, 5, 3]
def baseStart_1939845 : Nat := 118140960795 + 1939845 * 2 ^ 59
def prefixEnd_1939845 : Nat := 4983230072969 + 3 ^ 40 * 1939845 * 2
def baseEnd_1939845 : Nat := 996072880221068081216321

theorem tailTrace_1939845 : CollatzResearch.WordTrace tailWord_1939845 prefixEnd_1939845 996072880221068081216321 := by
  unfold tailWord_1939845
  simp only [CollatzResearch.WordTrace]
  refine ⟨70751959657280338995036989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47167973104853559330024659 70751959657280338995036989)
  ·
    refine ⟨26531984871480127123138871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70751959657280338995036989 26531984871480127123138871)
    ·
      refine ⟨39797977307220190684708307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26531984871480127123138871 39797977307220190684708307)
      ·
        refine ⟨59696965960830286027062461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39797977307220190684708307 59696965960830286027062461)
        ·
          refine ⟨22386362235311357260148423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59696965960830286027062461 22386362235311357260148423)
          ·
            refine ⟨33579543352967035890222635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22386362235311357260148423 33579543352967035890222635)
            ·
              refine ⟨50369315029450553835333953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33579543352967035890222635 50369315029450553835333953)
              ·
                refine ⟨37776986272087915376500465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50369315029450553835333953 37776986272087915376500465)
                ·
                  refine ⟨28332739704065936532375349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37776986272087915376500465 28332739704065936532375349)
                  ·
                    refine ⟨2656194347256181549910189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28332739704065936532375349 2656194347256181549910189)
                    ·
                      refine ⟨996072880221068081216321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2656194347256181549910189 996072880221068081216321)
                      ·
                        rfl

theorem cell23_1939845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_1939845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939845 prefixEnd_1939845 := by exact prefixLift 1939845
  have htrace : WordTrace (prefixWord ++ tailWord_1939845) baseStart_1939845 baseEnd_1939845 := by
    simpa [prefixWord, tailWord_1939845, baseEnd_1939845] using wordTrace_append hprefix tailTrace_1939845
  have hstable : (prefixWord ++ tailWord_1939845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939845).length < 2 ^ (prefixWord ++ tailWord_1939845).sum := by decide
  have hdescent : baseEnd_1939845 < baseStart_1939845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939865 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 3, 5]
def baseStart_1939865 : Nat := 118140960795 + 1939865 * 2 ^ 59
def prefixEnd_1939865 : Nat := 4983230072969 + 3 ^ 40 * 1939865 * 2
def baseEnd_1939865 : Nat := 332027716611386000988743

theorem tailTrace_1939865 : CollatzResearch.WordTrace tailWord_1939865 prefixEnd_1939865 332027716611386000988743 := by
  unfold tailWord_1939865
  simp only [CollatzResearch.WordTrace]
  refine ⟨70752689117207882410765049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47168459411471921607176699 70752689117207882410765049)
  ·
    refine ⟨53064516837905911808073787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70752689117207882410765049 53064516837905911808073787)
    ·
      refine ⟨79596775256858867712110681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53064516837905911808073787 79596775256858867712110681)
      ·
        refine ⟨59697581442644150784083011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79596775256858867712110681 59697581442644150784083011)
        ·
          refine ⟨89546372163966226176124517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59697581442644150784083011 89546372163966226176124517)
          ·
            refine ⟨16789944780743667408023347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89546372163966226176124517 16789944780743667408023347)
            ·
              refine ⟨25184917171115501112035021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16789944780743667408023347 25184917171115501112035021)
              ·
                refine ⟨9444343939168312917013133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25184917171115501112035021 9444343939168312917013133)
                ·
                  refine ⟨3541628977188117343879925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9444343939168312917013133 3541628977188117343879925)
                  ·
                    refine ⟨332027716611386000988743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3541628977188117343879925 332027716611386000988743)
                    ·
                      rfl

theorem cell23_1939865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_1939865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939865 prefixEnd_1939865 := by exact prefixLift 1939865
  have htrace : WordTrace (prefixWord ++ tailWord_1939865) baseStart_1939865 baseEnd_1939865 := by
    simpa [prefixWord, tailWord_1939865, baseEnd_1939865] using wordTrace_append hprefix tailTrace_1939865
  have hstable : (prefixWord ++ tailWord_1939865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939865).length < 2 ^ (prefixWord ++ tailWord_1939865).sum := by decide
  have hdescent : baseEnd_1939865 < baseStart_1939865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939873 : List Nat := [1, 2, 3, 5, 1, 1, 2, 3, 1, 4]
def baseStart_1939873 : Nat := 118140960795 + 1939873 * 2 ^ 59
def prefixEnd_1939873 : Nat := 4983230072969 + 3 ^ 40 * 1939873 * 2
def baseEnd_1939873 : Nat := 332029085893131323888731

theorem tailTrace_1939873 : CollatzResearch.WordTrace tailWord_1939873 prefixEnd_1939873 332029085893131323888731 := by
  unfold tailWord_1939873
  simp only [CollatzResearch.WordTrace]
  refine ⟨70752980901178899777056273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47168653934119266518037515 70752980901178899777056273)
  ·
    refine ⟨53064735675884174832792205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70752980901178899777056273 53064735675884174832792205)
    ·
      refine ⟨19899275878456565562297077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53064735675884174832792205 19899275878456565562297077)
      ·
        refine ⟨1865557113605303021465351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19899275878456565562297077 1865557113605303021465351)
        ·
          refine ⟨2798335670407954532198027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865557113605303021465351 2798335670407954532198027)
          ·
            refine ⟨4197503505611931798297041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798335670407954532198027 4197503505611931798297041)
            ·
              refine ⟨3148127629208948848722781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4197503505611931798297041 3148127629208948848722781)
              ·
                refine ⟨1180547860953355818271043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3148127629208948848722781 1180547860953355818271043)
                ·
                  refine ⟨1770821791430033727406565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180547860953355818271043 1770821791430033727406565)
                  ·
                    refine ⟨332029085893131323888731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1770821791430033727406565 332029085893131323888731)
                    ·
                      rfl

theorem cell23_1939873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_1939873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939873 prefixEnd_1939873 := by exact prefixLift 1939873
  have htrace : WordTrace (prefixWord ++ tailWord_1939873) baseStart_1939873 baseEnd_1939873 := by
    simpa [prefixWord, tailWord_1939873, baseEnd_1939873] using wordTrace_append hprefix tailTrace_1939873
  have hstable : (prefixWord ++ tailWord_1939873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939873).length < 2 ^ (prefixWord ++ tailWord_1939873).sum := by decide
  have hdescent : baseEnd_1939873 < baseStart_1939873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939902 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1939902 : Nat := 118140960795 + 1939902 * 2 ^ 59
def prefixEnd_1939902 : Nat := 4983230072969 + 3 ^ 40 * 1939902 * 2
def baseEnd_1939902 : Nat := 996102148618374358203559

theorem tailTrace_1939902 : CollatzResearch.WordTrace tailWord_1939902 prefixEnd_1939902 996102148618374358203559 := by
  unfold tailWord_1939902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844254827259229716232745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47169359078715891819907973 8844254827259229716232745)
  ·
    refine ⟨6633191120444422287174559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8844254827259229716232745 6633191120444422287174559)
    ·
      refine ⟨9949786680666633430761839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6633191120444422287174559 9949786680666633430761839)
      ·
        refine ⟨14924680020999950146142759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9949786680666633430761839 14924680020999950146142759)
        ·
          refine ⟨22387020031499925219214139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14924680020999950146142759 22387020031499925219214139)
          ·
            refine ⟨33580530047249887828821209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22387020031499925219214139 33580530047249887828821209)
            ·
              refine ⟨25185397535437415871615907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33580530047249887828821209 25185397535437415871615907)
              ·
                refine ⟨37778096303156123807423861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25185397535437415871615907 37778096303156123807423861)
                ·
                  refine ⟨3541696528420886606945987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37778096303156123807423861 3541696528420886606945987)
                  ·
                    refine ⟨5312544792631329910418981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3541696528420886606945987 5312544792631329910418981)
                    ·
                      refine ⟨996102148618374358203559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5312544792631329910418981 996102148618374358203559)
                      ·
                        rfl

theorem cell23_1939902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1939902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939902 prefixEnd_1939902 := by exact prefixLift 1939902
  have htrace : WordTrace (prefixWord ++ tailWord_1939902) baseStart_1939902 baseEnd_1939902 := by
    simpa [prefixWord, tailWord_1939902, baseEnd_1939902] using wordTrace_append hprefix tailTrace_1939902
  have hstable : (prefixWord ++ tailWord_1939902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939902).length < 2 ^ (prefixWord ++ tailWord_1939902).sum := by decide
  have hdescent : baseEnd_1939902 < baseStart_1939902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939912 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 1, 6]
def baseStart_1939912 : Nat := 118140960795 + 1939912 * 2 ^ 59
def prefixEnd_1939912 : Nat := 4983230072969 + 3 ^ 40 * 1939912 * 2
def baseEnd_1939912 : Nat := 332035761141639773026171

theorem tailTrace_1939912 : CollatzResearch.WordTrace tailWord_1939912 prefixEnd_1939912 332035761141639773026171 := by
  unfold tailWord_1939912
  simp only [CollatzResearch.WordTrace]
  refine ⟨35377201674018804718862995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47169602232025072958483993 35377201674018804718862995)
  ·
    refine ⟨53065802511028207078294493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35377201674018804718862995 53065802511028207078294493)
    ·
      refine ⟨19899675941635577654360435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53065802511028207078294493 19899675941635577654360435)
      ·
        refine ⟨29849513912453366481540653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19899675941635577654360435 29849513912453366481540653)
        ·
          refine ⟨11193567717170012430577745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29849513912453366481540653 11193567717170012430577745)
          ·
            refine ⟨8395175787877509322933309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11193567717170012430577745 8395175787877509322933309)
            ·
              refine ⟨3148190920454065996099991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8395175787877509322933309 3148190920454065996099991)
              ·
                refine ⟨4722286380681098994149987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148190920454065996099991 4722286380681098994149987)
                ·
                  refine ⟨7083429571021648491224981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722286380681098994149987 7083429571021648491224981)
                  ·
                    refine ⟨332035761141639773026171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7083429571021648491224981 332035761141639773026171)
                    ·
                      rfl

theorem cell23_1939912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_1939912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939912 prefixEnd_1939912 := by exact prefixLift 1939912
  have htrace : WordTrace (prefixWord ++ tailWord_1939912) baseStart_1939912 baseEnd_1939912 := by
    simpa [prefixWord, tailWord_1939912, baseEnd_1939912] using wordTrace_append hprefix tailTrace_1939912
  have hstable : (prefixWord ++ tailWord_1939912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939912).length < 2 ^ (prefixWord ++ tailWord_1939912).sum := by decide
  have hdescent : baseEnd_1939912 < baseStart_1939912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939939 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1939939 : Nat := 118140960795 + 1939939 * 2 ^ 59
def prefixEnd_1939939 : Nat := 4983230072969 + 3 ^ 40 * 1939939 * 2
def baseEnd_1939939 : Nat := 996121147402590713440889

theorem tailTrace_1939939 : CollatzResearch.WordTrace tailWord_1939939 prefixEnd_1939939 996121147402590713440889 := by
  unfold tailWord_1939939
  simp only [CollatzResearch.WordTrace]
  refine ⟨70755388118939793048958871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47170258745959862032639247 70755388118939793048958871)
  ·
    refine ⟨106133082178409689573438307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70755388118939793048958871 106133082178409689573438307)
    ·
      refine ⟨159199623267614534360157461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106133082178409689573438307 159199623267614534360157461)
      ·
        refine ⟨7462482340669431298132381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159199623267614534360157461 7462482340669431298132381)
        ·
          refine ⟨2798430877751036736799643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7462482340669431298132381 2798430877751036736799643)
          ·
            refine ⟨4197646316626555105199465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798430877751036736799643 4197646316626555105199465)
            ·
              refine ⟨3148234737469916328899599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4197646316626555105199465 3148234737469916328899599)
              ·
                refine ⟨4722352106204874493349399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148234737469916328899599 4722352106204874493349399)
                ·
                  refine ⟨7083528159307311740024099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722352106204874493349399 7083528159307311740024099)
                  ·
                    refine ⟨10625292238960967610036149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7083528159307311740024099 10625292238960967610036149)
                    ·
                      refine ⟨996121147402590713440889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10625292238960967610036149 996121147402590713440889)
                      ·
                        rfl

theorem cell23_1939939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1939939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939939 prefixEnd_1939939 := by exact prefixLift 1939939
  have htrace : WordTrace (prefixWord ++ tailWord_1939939) baseStart_1939939 baseEnd_1939939 := by
    simpa [prefixWord, tailWord_1939939, baseEnd_1939939] using wordTrace_append hprefix tailTrace_1939939
  have hstable : (prefixWord ++ tailWord_1939939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939939).length < 2 ^ (prefixWord ++ tailWord_1939939).sum := by decide
  have hdescent : baseEnd_1939939 < baseStart_1939939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939955 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 2, 7]
def baseStart_1939955 : Nat := 118140960795 + 1939955 * 2 ^ 59
def prefixEnd_1939955 : Nat := 4983230072969 + 3 ^ 40 * 1939955 * 2
def baseEnd_1939955 : Nat := 332043121031020883613605

theorem tailTrace_1939955 : CollatzResearch.WordTrace tailWord_1939955 prefixEnd_1939955 332043121031020883613605 := by
  unfold tailWord_1939955
  simp only [CollatzResearch.WordTrace]
  refine ⟨70755971686881827781541319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47170647791254551854360879 70755971686881827781541319)
  ·
    refine ⟨106133957530322741672311979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70755971686881827781541319 106133957530322741672311979)
    ·
      refine ⟨159200936295484112508467969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106133957530322741672311979 159200936295484112508467969)
      ·
        refine ⟨119400702221613084381350977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159200936295484112508467969 119400702221613084381350977)
        ·
          refine ⟨89550526666209813286013233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119400702221613084381350977 89550526666209813286013233)
          ·
            refine ⟨67162894999657359964509925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89550526666209813286013233 67162894999657359964509925)
            ·
              refine ⟨12593042812435754993345611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67162894999657359964509925 12593042812435754993345611)
              ·
                refine ⟨18889564218653632490018417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12593042812435754993345611 18889564218653632490018417)
                ·
                  refine ⟨14167173163990224367513813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18889564218653632490018417 14167173163990224367513813)
                  ·
                    refine ⟨332043121031020883613605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14167173163990224367513813 332043121031020883613605)
                    ·
                      rfl

theorem cell23_1939955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 7].length) (baseStart_1939955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939955 prefixEnd_1939955 := by exact prefixLift 1939955
  have htrace : WordTrace (prefixWord ++ tailWord_1939955) baseStart_1939955 baseEnd_1939955 := by
    simpa [prefixWord, tailWord_1939955, baseEnd_1939955] using wordTrace_append hprefix tailTrace_1939955
  have hstable : (prefixWord ++ tailWord_1939955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939955).length < 2 ^ (prefixWord ++ tailWord_1939955).sum := by decide
  have hdescent : baseEnd_1939955 < baseStart_1939955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939970 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_1939970 : Nat := 118140960795 + 1939970 * 2 ^ 59
def prefixEnd_1939970 : Nat := 4983230072969 + 3 ^ 40 * 1939970 * 2
def baseEnd_1939970 : Nat := 996137065302880092153247

theorem tailTrace_1939970 : CollatzResearch.WordTrace tailWord_1939970 prefixEnd_1939970 996137065302880092153247 := by
  unfold tailWord_1939970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17689129695456871335834341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47171012521218323562224909 17689129695456871335834341)
  ·
    refine ⟨3316711817898163375468939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17689129695456871335834341 3316711817898163375468939)
    ·
      refine ⟨4975067726847245063203409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3316711817898163375468939 4975067726847245063203409)
      ·
        refine ⟨3731300795135433797402557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4975067726847245063203409 3731300795135433797402557)
        ·
          refine ⟨1399237798175787674025959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3731300795135433797402557 1399237798175787674025959)
          ·
            refine ⟨2098856697263681511038939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399237798175787674025959 2098856697263681511038939)
            ·
              refine ⟨3148285045895522266558409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098856697263681511038939 3148285045895522266558409)
              ·
                refine ⟨2361213784421641699918807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148285045895522266558409 2361213784421641699918807)
                ·
                  refine ⟨3541820676632462549878211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361213784421641699918807 3541820676632462549878211)
                  ·
                    refine ⟨5312731014948693824817317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3541820676632462549878211 5312731014948693824817317)
                    ·
                      refine ⟨996137065302880092153247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5312731014948693824817317 996137065302880092153247)
                      ·
                        rfl

theorem cell23_1939970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_1939970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939970 prefixEnd_1939970 := by exact prefixLift 1939970
  have htrace : WordTrace (prefixWord ++ tailWord_1939970) baseStart_1939970 baseEnd_1939970 := by
    simpa [prefixWord, tailWord_1939970, baseEnd_1939970] using wordTrace_append hprefix tailTrace_1939970
  have hstable : (prefixWord ++ tailWord_1939970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939970).length < 2 ^ (prefixWord ++ tailWord_1939970).sum := by decide
  have hdescent : baseEnd_1939970 < baseStart_1939970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1939985 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 3, 8]
def baseStart_1939985 : Nat := 118140960795 + 1939985 * 2 ^ 59
def prefixEnd_1939985 : Nat := 4983230072969 + 3 ^ 40 * 1939985 * 2
def baseEnd_1939985 : Nat := 332048255837565844488559

theorem tailTrace_1939985 : CollatzResearch.WordTrace tailWord_1939985 prefixEnd_1939985 332048255837565844488559 := by
  unfold tailWord_1939985
  simp only [CollatzResearch.WordTrace]
  refine ⟨70757065876773142905133409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47171377251182095270088939 70757065876773142905133409)
  ·
    refine ⟨53067799407579857178850057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70757065876773142905133409 53067799407579857178850057)
    ·
      refine ⟨39800849555684892884137543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53067799407579857178850057 39800849555684892884137543)
      ·
        refine ⟨59701274333527339326206315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39800849555684892884137543 59701274333527339326206315)
        ·
          refine ⟨89551911500291008989309473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59701274333527339326206315 89551911500291008989309473)
          ·
            refine ⟨67163933625218256741982105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89551911500291008989309473 67163933625218256741982105)
            ·
              refine ⟨50372950218913692556486579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67163933625218256741982105 50372950218913692556486579)
              ·
                refine ⟨75559425328370538834729869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50372950218913692556486579 75559425328370538834729869)
                ·
                  refine ⟨28334784498138952063023701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75559425328370538834729869 28334784498138952063023701)
                  ·
                    refine ⟨332048255837565844488559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28334784498138952063023701 332048255837565844488559)
                    ·
                      rfl

theorem cell23_1939985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_1939985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1939985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1939985 prefixEnd_1939985 := by exact prefixLift 1939985
  have htrace : WordTrace (prefixWord ++ tailWord_1939985) baseStart_1939985 baseEnd_1939985 := by
    simpa [prefixWord, tailWord_1939985, baseEnd_1939985] using wordTrace_append hprefix tailTrace_1939985
  have hstable : (prefixWord ++ tailWord_1939985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1939985).length < 2 ^ (prefixWord ++ tailWord_1939985).sum := by decide
  have hdescent : baseEnd_1939985 < baseStart_1939985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1939985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940002 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_1940002 : Nat := 118140960795 + 1940002 * 2 ^ 59
def prefixEnd_1940002 : Nat := 4983230072969 + 3 ^ 40 * 1940002 * 2
def baseEnd_1940002 : Nat := 332051165561274655651033

theorem tailTrace_1940002 : CollatzResearch.WordTrace tailWord_1940002 prefixEnd_1940002 332051165561274655651033 := by
  unfold tailWord_1940002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17689421479427888702125565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47171790611807703205668173 17689421479427888702125565)
  ·
    refine ⟨6633533054785458263297087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17689421479427888702125565 6633533054785458263297087)
    ·
      refine ⟨9950299582178187394945631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6633533054785458263297087 9950299582178187394945631)
      ·
        refine ⟨14925449373267281092418447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9950299582178187394945631 14925449373267281092418447)
        ·
          refine ⟨22388174059900921638627671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14925449373267281092418447 22388174059900921638627671)
          ·
            refine ⟨33582261089851382457941507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22388174059900921638627671 33582261089851382457941507)
            ·
              refine ⟨50373391634777073686912261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33582261089851382457941507 50373391634777073686912261)
              ·
                refine ⟨9445010931520701316296049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50373391634777073686912261 9445010931520701316296049)
                ·
                  refine ⟨7083758198640525987222037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9445010931520701316296049 7083758198640525987222037)
                  ·
                    refine ⟨332051165561274655651033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7083758198640525987222037 332051165561274655651033)
                    ·
                      rfl

theorem cell23_1940002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_1940002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940002 prefixEnd_1940002 := by exact prefixLift 1940002
  have htrace : WordTrace (prefixWord ++ tailWord_1940002) baseStart_1940002 baseEnd_1940002 := by
    simpa [prefixWord, tailWord_1940002, baseEnd_1940002] using wordTrace_append hprefix tailTrace_1940002
  have hstable : (prefixWord ++ tailWord_1940002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940002).length < 2 ^ (prefixWord ++ tailWord_1940002).sum := by decide
  have hdescent : baseEnd_1940002 < baseStart_1940002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940004 : List Nat := [2, 3, 1, 5, 1, 2, 2, 2, 1, 2, 2]
def baseStart_1940004 : Nat := 118140960795 + 1940004 * 2 ^ 59
def prefixEnd_1940004 : Nat := 4983230072969 + 3 ^ 40 * 1940004 * 2
def baseEnd_1940004 : Nat := 996154523645132959128091

theorem tailTrace_1940004 : CollatzResearch.WordTrace tailWord_1940004 prefixEnd_1940004 996154523645132959128091 := by
  unfold tailWord_1940004
  simp only [CollatzResearch.WordTrace]
  refine ⟨35378879431852154575037533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47171839242469539433383377 35378879431852154575037533)
  ·
    refine ⟨13267079786944557965639075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35378879431852154575037533 13267079786944557965639075)
    ·
      refine ⟨19900619680416836948458613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13267079786944557965639075 19900619680416836948458613)
      ·
        refine ⟨1865683095039078463917995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19900619680416836948458613 1865683095039078463917995)
        ·
          refine ⟨2798524642558617695876993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865683095039078463917995 2798524642558617695876993)
          ·
            refine ⟨2098893481918963271907745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2798524642558617695876993 2098893481918963271907745)
            ·
              refine ⟨1574170111439222453930809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2098893481918963271907745 1574170111439222453930809)
              ·
                refine ⟨1180627583579416840448107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574170111439222453930809 1180627583579416840448107)
                ·
                  refine ⟨1770941375369125260672161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180627583579416840448107 1770941375369125260672161)
                  ·
                    refine ⟨1328206031526843945504121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1770941375369125260672161 1328206031526843945504121)
                    ·
                      refine ⟨996154523645132959128091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1328206031526843945504121 996154523645132959128091)
                      ·
                        rfl

theorem cell23_1940004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_1940004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940004 prefixEnd_1940004 := by exact prefixLift 1940004
  have htrace : WordTrace (prefixWord ++ tailWord_1940004) baseStart_1940004 baseEnd_1940004 := by
    simpa [prefixWord, tailWord_1940004, baseEnd_1940004] using wordTrace_append hprefix tailTrace_1940004
  have hstable : (prefixWord ++ tailWord_1940004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940004).length < 2 ^ (prefixWord ++ tailWord_1940004).sum := by decide
  have hdescent : baseEnd_1940004 < baseStart_1940004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940015 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 13]
def baseStart_1940015 : Nat := 118140960795 + 1940015 * 2 ^ 59
def prefixEnd_1940015 : Nat := 4983230072969 + 3 ^ 40 * 1940015 * 2
def baseEnd_1940015 : Nat := 110684463548036935121171

theorem tailTrace_1940015 : CollatzResearch.WordTrace tailWord_1940015 prefixEnd_1940015 110684463548036935121171 := by
  unfold tailWord_1940015
  simp only [CollatzResearch.WordTrace]
  refine ⟨70758160066664458028725499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47172106711109638685816999 70758160066664458028725499)
  ·
    refine ⟨106137240099996687043088249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70758160066664458028725499 106137240099996687043088249)
    ·
      refine ⟨79602930074997515282316187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106137240099996687043088249 79602930074997515282316187)
      ·
        refine ⟨119404395112496272923474281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79602930074997515282316187 119404395112496272923474281)
        ·
          refine ⟨89553296334372204692605711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119404395112496272923474281 89553296334372204692605711)
          ·
            refine ⟨134329944501558307038908567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89553296334372204692605711 134329944501558307038908567)
            ·
              refine ⟨201494916752337460558362851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134329944501558307038908567 201494916752337460558362851)
              ·
                refine ⟨302242375128506190837544277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201494916752337460558362851 302242375128506190837544277)
                ·
                  refine ⟨110684463548036935121171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 302242375128506190837544277 110684463548036935121171)
                  ·
                    rfl

theorem cell23_1940015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 13].length) (baseStart_1940015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940015 prefixEnd_1940015 := by exact prefixLift 1940015
  have htrace : WordTrace (prefixWord ++ tailWord_1940015) baseStart_1940015 baseEnd_1940015 := by
    simpa [prefixWord, tailWord_1940015, baseEnd_1940015] using wordTrace_append hprefix tailTrace_1940015
  have hstable : (prefixWord ++ tailWord_1940015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940015).length < 2 ^ (prefixWord ++ tailWord_1940015).sum := by decide
  have hdescent : baseEnd_1940015 < baseStart_1940015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940026 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2]
def baseStart_1940026 : Nat := 118140960795 + 1940026 * 2 ^ 59
def prefixEnd_1940026 : Nat := 4983230072969 + 3 ^ 40 * 1940026 * 2
def baseEnd_1940026 : Nat := 996165820219531873052989

theorem tailTrace_1940026 : CollatzResearch.WordTrace tailWord_1940026 prefixEnd_1940026 996165820219531873052989 := by
  unfold tailWord_1940026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17689640317406151726843983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47172374179749737938250621 17689640317406151726843983)
  ·
    refine ⟨26534460476109227590265975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17689640317406151726843983 26534460476109227590265975)
    ·
      refine ⟨39801690714163841385398963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26534460476109227590265975 39801690714163841385398963)
      ·
        refine ⟨59702536071245762078098445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39801690714163841385398963 59702536071245762078098445)
        ·
          refine ⟨22388451026717160779286917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59702536071245762078098445 22388451026717160779286917)
          ·
            refine ⟨4197834567509467646116297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22388451026717160779286917 4197834567509467646116297)
            ·
              refine ⟨3148375925632100734587223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4197834567509467646116297 3148375925632100734587223)
              ·
                refine ⟨4722563888448151101880835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148375925632100734587223 4722563888448151101880835)
                ·
                  refine ⟨7083845832672226652821253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4722563888448151101880835 7083845832672226652821253)
                  ·
                    refine ⟨1328221093626042497403985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7083845832672226652821253 1328221093626042497403985)
                    ·
                      refine ⟨996165820219531873052989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1328221093626042497403985 996165820219531873052989)
                      ·
                        rfl

theorem cell23_1940026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2].length) (baseStart_1940026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940026 prefixEnd_1940026 := by exact prefixLift 1940026
  have htrace : WordTrace (prefixWord ++ tailWord_1940026) baseStart_1940026 baseEnd_1940026 := by
    simpa [prefixWord, tailWord_1940026, baseEnd_1940026] using wordTrace_append hprefix tailTrace_1940026
  have hstable : (prefixWord ++ tailWord_1940026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940026).length < 2 ^ (prefixWord ++ tailWord_1940026).sum := by decide
  have hdescent : baseEnd_1940026 < baseStart_1940026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940049 : List Nat := [1, 2, 2, 1, 3, 3, 1, 5, 5]
def baseStart_1940049 : Nat := 118140960795 + 1940049 * 2 ^ 59
def prefixEnd_1940049 : Nat := 4983230072969 + 3 ^ 40 * 1940049 * 2
def baseEnd_1940049 : Nat := 110686403363842809229487

theorem tailTrace_1940049 : CollatzResearch.WordTrace tailWord_1940049 prefixEnd_1940049 110686403363842809229487 := by
  unfold tailWord_1940049
  simp only [CollatzResearch.WordTrace]
  refine ⟨70759400148541281835463201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47172933432360854556975467 70759400148541281835463201)
  ·
    refine ⟨53069550111405961376597401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70759400148541281835463201 53069550111405961376597401)
    ·
      refine ⟨39802162583554471032448051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53069550111405961376597401 39802162583554471032448051)
      ·
        refine ⟨59703243875331706548672077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39802162583554471032448051 59703243875331706548672077)
        ·
          refine ⟨22388716453249389955752029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59703243875331706548672077 22388716453249389955752029)
          ·
            refine ⟨8395768669968521233407011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22388716453249389955752029 8395768669968521233407011)
            ·
              refine ⟨12593653004952781850110517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8395768669968521233407011 12593653004952781850110517)
              ·
                refine ⟨1180654969214323298447861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12593653004952781850110517 1180654969214323298447861)
                ·
                  refine ⟨110686403363842809229487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1180654969214323298447861 110686403363842809229487)
                  ·
                    rfl

theorem cell23_1940049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 5].length) (baseStart_1940049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940049 prefixEnd_1940049 := by exact prefixLift 1940049
  have htrace : WordTrace (prefixWord ++ tailWord_1940049) baseStart_1940049 baseEnd_1940049 := by
    simpa [prefixWord, tailWord_1940049, baseEnd_1940049] using wordTrace_append hprefix tailTrace_1940049
  have hstable : (prefixWord ++ tailWord_1940049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940049).length < 2 ^ (prefixWord ++ tailWord_1940049).sum := by decide
  have hdescent : baseEnd_1940049 < baseStart_1940049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940099 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 1, 6, 2]
def baseStart_1940099 : Nat := 118140960795 + 1940099 * 2 ^ 59
def prefixEnd_1940099 : Nat := 4983230072969 + 3 ^ 40 * 1940099 * 2
def baseEnd_1940099 : Nat := 996203304307310087440153

theorem tailTrace_1940099 : CollatzResearch.WordTrace tailWord_1940099 prefixEnd_1940099 996203304307310087440153 := by
  unfold tailWord_1940099
  simp only [CollatzResearch.WordTrace]
  refine ⟨70761223798360140374783351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47174149198906760249855567 70761223798360140374783351)
  ·
    refine ⟨106141835697540210562175027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70761223798360140374783351 106141835697540210562175027)
    ·
      refine ⟨159212753546310315843262541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106141835697540210562175027 159212753546310315843262541)
      ·
        refine ⟨59704782579866368441223453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159212753546310315843262541 59704782579866368441223453)
        ·
          refine ⟨22389293467449888165458795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59704782579866368441223453 22389293467449888165458795)
          ·
            refine ⟨33583940201174832248188193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22389293467449888165458795 33583940201174832248188193)
            ·
              refine ⟨25187955150881124186141145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33583940201174832248188193 25187955150881124186141145)
              ·
                refine ⟨18890966363160843139605859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25187955150881124186141145 18890966363160843139605859)
                ·
                  refine ⟨28336449544741264709408789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18890966363160843139605859 28336449544741264709408789)
                  ·
                    refine ⟨1328271072409746783253537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28336449544741264709408789 1328271072409746783253537)
                    ·
                      refine ⟨996203304307310087440153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1328271072409746783253537 996203304307310087440153)
                      ·
                        rfl

theorem cell23_1940099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 6, 2].length) (baseStart_1940099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940099 prefixEnd_1940099 := by exact prefixLift 1940099
  have htrace : WordTrace (prefixWord ++ tailWord_1940099) baseStart_1940099 baseEnd_1940099 := by
    simpa [prefixWord, tailWord_1940099, baseEnd_1940099] using wordTrace_append hprefix tailTrace_1940099
  have hstable : (prefixWord ++ tailWord_1940099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940099).length < 2 ^ (prefixWord ++ tailWord_1940099).sum := by decide
  have hdescent : baseEnd_1940099 < baseStart_1940099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940116 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1940116 : Nat := 118140960795 + 1940116 * 2 ^ 59
def prefixEnd_1940116 : Nat := 4983230072969 + 3 ^ 40 * 1940116 * 2
def baseEnd_1940116 : Nat := 996212033478436520927575

theorem tailTrace_1940116 : CollatzResearch.WordTrace tailWord_1940116 prefixEnd_1940116 996212033478436520927575 := by
  unfold tailWord_1940116
  simp only [CollatzResearch.WordTrace]
  refine ⟨35380921919649276139076101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47174562559532368185434801 35380921919649276139076101)
  ·
    refine ⟨6633922859934239276076769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35380921919649276139076101 6633922859934239276076769)
    ·
      refine ⟨4975442144950679457057577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6633922859934239276076769 4975442144950679457057577)
      ·
        refine ⟨3731581608713009592793183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4975442144950679457057577 3731581608713009592793183)
        ·
          refine ⟨5597372413069514389189775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3731581608713009592793183 5597372413069514389189775)
          ·
            refine ⟨8396058619604271583784663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5597372413069514389189775 8396058619604271583784663)
            ·
              refine ⟨12594087929406407375676995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8396058619604271583784663 12594087929406407375676995)
              ·
                refine ⟨18891131894109611063515493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12594087929406407375676995 18891131894109611063515493)
                ·
                  refine ⟨3542087230145552074409155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18891131894109611063515493 3542087230145552074409155)
                  ·
                    refine ⟨5313130845218328111613733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3542087230145552074409155 5313130845218328111613733)
                    ·
                      refine ⟨996212033478436520927575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5313130845218328111613733 996212033478436520927575)
                      ·
                        rfl

theorem cell23_1940116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1940116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940116 prefixEnd_1940116 := by exact prefixLift 1940116
  have htrace : WordTrace (prefixWord ++ tailWord_1940116) baseStart_1940116 baseEnd_1940116 := by
    simpa [prefixWord, tailWord_1940116, baseEnd_1940116] using wordTrace_append hprefix tailTrace_1940116
  have hstable : (prefixWord ++ tailWord_1940116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940116).length < 2 ^ (prefixWord ++ tailWord_1940116).sum := by decide
  have hdescent : baseEnd_1940116 < baseStart_1940116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940150 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1940150 : Nat := 118140960795 + 1940150 * 2 ^ 59
def prefixEnd_1940150 : Nat := 4983230072969 + 3 ^ 40 * 1940150 * 2
def baseEnd_1940150 : Nat := 996229491820689387902419

theorem tailTrace_1940150 : CollatzResearch.WordTrace tailWord_1940150 prefixEnd_1940150 996229491820689387902419 := by
  unfold tailWord_1940150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4422692745073461005305619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47175389280783584056593269 4422692745073461005305619)
  ·
    refine ⟨6634039117610191507958429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4422692745073461005305619 6634039117610191507958429)
    ·
      refine ⟨2487764669103821815484411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6634039117610191507958429 2487764669103821815484411)
      ·
        refine ⟨3731647003655732723226617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2487764669103821815484411 3731647003655732723226617)
        ·
          refine ⟨2798735252741799542419963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3731647003655732723226617 2798735252741799542419963)
          ·
            refine ⟨4198102879112699313629945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798735252741799542419963 4198102879112699313629945)
            ·
              refine ⟨3148577159334524485222459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198102879112699313629945 3148577159334524485222459)
              ·
                refine ⟨4722865739001786727833689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148577159334524485222459 4722865739001786727833689)
                ·
                  refine ⟨3542149304251340045875267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4722865739001786727833689 3542149304251340045875267)
                  ·
                    refine ⟨5313223956377010068812901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3542149304251340045875267 5313223956377010068812901)
                    ·
                      refine ⟨996229491820689387902419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5313223956377010068812901 996229491820689387902419)
                      ·
                        rfl

theorem cell23_1940150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1940150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940150 prefixEnd_1940150 := by exact prefixLift 1940150
  have htrace : WordTrace (prefixWord ++ tailWord_1940150) baseStart_1940150 baseEnd_1940150 := by
    simpa [prefixWord, tailWord_1940150, baseEnd_1940150] using wordTrace_append hprefix tailTrace_1940150
  have hstable : (prefixWord ++ tailWord_1940150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940150).length < 2 ^ (prefixWord ++ tailWord_1940150).sum := by decide
  have hdescent : baseEnd_1940150 < baseStart_1940150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940206 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_1940206 : Nat := 118140960795 + 1940206 * 2 ^ 59
def prefixEnd_1940206 : Nat := 4983230072969 + 3 ^ 40 * 1940206 * 2
def baseEnd_1940206 : Nat := 996258246737341168802161

theorem tailTrace_1940206 : CollatzResearch.WordTrace tailWord_1940206 prefixEnd_1940206 996258246737341168802161 := by
  unfold tailWord_1940206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8845640801121562206116059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47176750939314998432618981 8845640801121562206116059)
  ·
    refine ⟨13268461201682343309174089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8845640801121562206116059 13268461201682343309174089)
    ·
      refine ⟨9951345901261757481880567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13268461201682343309174089 9951345901261757481880567)
      ·
        refine ⟨14927018851892636222820851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9951345901261757481880567 14927018851892636222820851)
        ·
          refine ⟨22390528277838954334231277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14927018851892636222820851 22390528277838954334231277)
          ·
            refine ⟨8396448104189607875336729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22390528277838954334231277 8396448104189607875336729)
            ·
              refine ⟨6297336078142205906502547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8396448104189607875336729 6297336078142205906502547)
              ·
                refine ⟨9446004117213308859753821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6297336078142205906502547 9446004117213308859753821)
                ·
                  refine ⟨3542251543954990822407683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9446004117213308859753821 3542251543954990822407683)
                  ·
                    refine ⟨5313377315932486233611525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3542251543954990822407683 5313377315932486233611525)
                    ·
                      refine ⟨996258246737341168802161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5313377315932486233611525 996258246737341168802161)
                      ·
                        rfl

theorem cell23_1940206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_1940206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940206 prefixEnd_1940206 := by exact prefixLift 1940206
  have htrace : WordTrace (prefixWord ++ tailWord_1940206) baseStart_1940206 baseEnd_1940206 := by
    simpa [prefixWord, tailWord_1940206, baseEnd_1940206] using wordTrace_append hprefix tailTrace_1940206
  have hstable : (prefixWord ++ tailWord_1940206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940206).length < 2 ^ (prefixWord ++ tailWord_1940206).sum := by decide
  have hdescent : baseEnd_1940206 < baseStart_1940206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940210 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 2, 3, 2]
def baseStart_1940210 : Nat := 118140960795 + 1940210 * 2 ^ 59
def prefixEnd_1940210 : Nat := 4983230072969 + 3 ^ 40 * 1940210 * 2
def baseEnd_1940210 : Nat := 996260300659959153152143

theorem tailTrace_1940210 : CollatzResearch.WordTrace tailWord_1940210 prefixEnd_1940210 996260300659959153152143 := by
  unfold tailWord_1940210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17691318075239501583018521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47176848200638670888049389 17691318075239501583018521)
  ·
    refine ⟨13268488556429626187263891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17691318075239501583018521 13268488556429626187263891)
    ·
      refine ⟨19902732834644439280895837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13268488556429626187263891 19902732834644439280895837)
      ·
        refine ⟨7463524812991664730335939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19902732834644439280895837 7463524812991664730335939)
        ·
          refine ⟨11195287219487497095503909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7463524812991664730335939 11195287219487497095503909)
          ·
            refine ⟨2099116353653905705406983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11195287219487497095503909 2099116353653905705406983)
            ·
              refine ⟨3148674530480858558110475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099116353653905705406983 3148674530480858558110475)
              ·
                refine ⟨4723011795721287837165713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148674530480858558110475 4723011795721287837165713)
                ·
                  refine ⟨3542258846790965877874285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4723011795721287837165713 3542258846790965877874285)
                  ·
                    refine ⟨1328347067546612204202857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3542258846790965877874285 1328347067546612204202857)
                    ·
                      refine ⟨996260300659959153152143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1328347067546612204202857 996260300659959153152143)
                      ·
                        rfl

theorem cell23_1940210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_1940210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940210 prefixEnd_1940210 := by exact prefixLift 1940210
  have htrace : WordTrace (prefixWord ++ tailWord_1940210) baseStart_1940210 baseEnd_1940210 := by
    simpa [prefixWord, tailWord_1940210, baseEnd_1940210] using wordTrace_append hprefix tailTrace_1940210
  have hstable : (prefixWord ++ tailWord_1940210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940210).length < 2 ^ (prefixWord ++ tailWord_1940210).sum := by decide
  have hdescent : baseEnd_1940210 < baseStart_1940210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940253 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1940253 : Nat := 118140960795 + 1940253 * 2 ^ 59
def prefixEnd_1940253 : Nat := 4983230072969 + 3 ^ 40 * 1940253 * 2
def baseEnd_1940253 : Nat := 996282380328102484914445

theorem tailTrace_1940253 : CollatzResearch.WordTrace tailWord_1940253 prefixEnd_1940253 996282380328102484914445 := by
  unfold tailWord_1940253
  simp only [CollatzResearch.WordTrace]
  refine ⟨70766840639802224675889413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47177893759868149783926275 70766840639802224675889413)
  ·
    refine ⟨13268782619962917126729265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70766840639802224675889413 13268782619962917126729265)
    ·
      refine ⟨9951586964972187845046949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13268782619962917126729265 9951586964972187845046949)
      ·
        refine ⟨1865922555932285220946303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9951586964972187845046949 1865922555932285220946303)
        ·
          refine ⟨2798883833898427831419455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865922555932285220946303 2798883833898427831419455)
          ·
            refine ⟨4198325750847641747129183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798883833898427831419455 4198325750847641747129183)
            ·
              refine ⟨6297488626271462620693775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4198325750847641747129183 6297488626271462620693775)
              ·
                refine ⟨9446232939407193931040663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6297488626271462620693775 9446232939407193931040663)
                ·
                  refine ⟨14169349409110790896560995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9446232939407193931040663 14169349409110790896560995)
                  ·
                    refine ⟨21254024113666186344841493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14169349409110790896560995 21254024113666186344841493)
                    ·
                      refine ⟨996282380328102484914445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21254024113666186344841493 996282380328102484914445)
                      ·
                        rfl

theorem cell23_1940253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1940253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940253 prefixEnd_1940253 := by exact prefixLift 1940253
  have htrace : WordTrace (prefixWord ++ tailWord_1940253) baseStart_1940253 baseEnd_1940253 := by
    simpa [prefixWord, tailWord_1940253, baseEnd_1940253] using wordTrace_append hprefix tailTrace_1940253
  have hstable : (prefixWord ++ tailWord_1940253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940253).length < 2 ^ (prefixWord ++ tailWord_1940253).sum := by decide
  have hdescent : baseEnd_1940253 < baseStart_1940253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940260 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_1940260 : Nat := 118140960795 + 1940260 * 2 ^ 59
def prefixEnd_1940260 : Nat := 4983230072969 + 3 ^ 40 * 1940260 * 2
def baseEnd_1940260 : Nat := 996285974692683957526913

theorem tailTrace_1940260 : CollatzResearch.WordTrace tailWord_1940260 prefixEnd_1940260 996285974692683957526913 := by
  unfold tailWord_1940260
  simp only [CollatzResearch.WordTrace]
  refine ⟨35383547975388432435697117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47178063967184576580929489 35383547975388432435697117)
  ·
    refine ⟨13268830490770662163386419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35383547975388432435697117 13268830490770662163386419)
    ·
      refine ⟨19903245736155993245079629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13268830490770662163386419 19903245736155993245079629)
      ·
        refine ⟨7463717151058497466904861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19903245736155993245079629 7463717151058497466904861)
        ·
          refine ⟨2798893931646936550089323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7463717151058497466904861 2798893931646936550089323)
          ·
            refine ⟨4198340897470404825133985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798893931646936550089323 4198340897470404825133985)
            ·
              refine ⟨3148755673102803618850489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198340897470404825133985 3148755673102803618850489)
              ·
                refine ⟨2361566754827102714137867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3148755673102803618850489 2361566754827102714137867)
                ·
                  refine ⟨3542350132240654071206801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361566754827102714137867 3542350132240654071206801)
                  ·
                    refine ⟨2656762599180490553405101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3542350132240654071206801 2656762599180490553405101)
                    ·
                      refine ⟨996285974692683957526913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2656762599180490553405101 996285974692683957526913)
                      ·
                        rfl

theorem cell23_1940260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_1940260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940260 prefixEnd_1940260 := by exact prefixLift 1940260
  have htrace : WordTrace (prefixWord ++ tailWord_1940260) baseStart_1940260 baseEnd_1940260 := by
    simpa [prefixWord, tailWord_1940260, baseEnd_1940260] using wordTrace_append hprefix tailTrace_1940260
  have hstable : (prefixWord ++ tailWord_1940260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940260).length < 2 ^ (prefixWord ++ tailWord_1940260).sum := by decide
  have hdescent : baseEnd_1940260 < baseStart_1940260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940319 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 9]
def baseStart_1940319 : Nat := 118140960795 + 1940319 * 2 ^ 59
def prefixEnd_1940319 : Nat := 4983230072969 + 3 ^ 40 * 1940319 * 2
def baseEnd_1940319 : Nat := 110701807783477691854349

theorem tailTrace_1940319 : CollatzResearch.WordTrace tailWord_1940319 prefixEnd_1940319 110701807783477691854349 := by
  unfold tailWord_1940319
  simp only [CollatzResearch.WordTrace]
  refine ⟨70769247857563117947792011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47179498571708745298528007 70769247857563117947792011)
  ·
    refine ⟨106153871786344676921688017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70769247857563117947792011 106153871786344676921688017)
    ·
      refine ⟨79615403839758507691266013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106153871786344676921688017 79615403839758507691266013)
      ·
        refine ⟨29855776439909440384224755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79615403839758507691266013 29855776439909440384224755)
        ·
          refine ⟨44783664659864160576337133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29855776439909440384224755 44783664659864160576337133)
          ·
            refine ⟨16793874247449060216126425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44783664659864160576337133 16793874247449060216126425)
            ·
              refine ⟨12595405685586795162094819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16793874247449060216126425 12595405685586795162094819)
              ·
                refine ⟨18893108528380192743142229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12595405685586795162094819 18893108528380192743142229)
                ·
                  refine ⟨110701807783477691854349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18893108528380192743142229 110701807783477691854349)
                  ·
                    rfl

theorem cell23_1940319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 9].length) (baseStart_1940319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940319 prefixEnd_1940319 := by exact prefixLift 1940319
  have htrace : WordTrace (prefixWord ++ tailWord_1940319) baseStart_1940319 baseEnd_1940319 := by
    simpa [prefixWord, tailWord_1940319, baseEnd_1940319] using wordTrace_append hprefix tailTrace_1940319
  have hstable : (prefixWord ++ tailWord_1940319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940319).length < 2 ^ (prefixWord ++ tailWord_1940319).sum := by decide
  have hdescent : baseEnd_1940319 < baseStart_1940319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940334 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_1940334 : Nat := 118140960795 + 1940334 * 2 ^ 59
def prefixEnd_1940334 : Nat := 4983230072969 + 3 ^ 40 * 1940334 * 2
def baseEnd_1940334 : Nat := 996323972261116668001573

theorem tailTrace_1940334 : CollatzResearch.WordTrace tailWord_1940334 prefixEnd_1940334 996323972261116668001573 := by
  unfold tailWord_1940334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8846224369063596938698507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47179863301672517006392037 8846224369063596938698507)
  ·
    refine ⟨13269336553595395408047761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8846224369063596938698507 13269336553595395408047761)
    ·
      refine ⟨9952002415196546556035821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13269336553595395408047761 9952002415196546556035821)
      ·
        refine ⟨3732000905698704958513433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9952002415196546556035821 3732000905698704958513433)
        ·
          refine ⟨2799000679274028718885075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3732000905698704958513433 2799000679274028718885075)
          ·
            refine ⟨4198501018911043078327613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799000679274028718885075 4198501018911043078327613)
            ·
              refine ⟨1574437882091641154372855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4198501018911043078327613 1574437882091641154372855)
              ·
                refine ⟨2361656823137461731559283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574437882091641154372855 2361656823137461731559283)
                ·
                  refine ⟨3542485234706192597338925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361656823137461731559283 3542485234706192597338925)
                  ·
                    refine ⟨1328431963014822224002097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3542485234706192597338925 1328431963014822224002097)
                    ·
                      refine ⟨996323972261116668001573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1328431963014822224002097 996323972261116668001573)
                      ·
                        rfl

theorem cell23_1940334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_1940334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940334 prefixEnd_1940334 := by exact prefixLift 1940334
  have htrace : WordTrace (prefixWord ++ tailWord_1940334) baseStart_1940334 baseEnd_1940334 := by
    simpa [prefixWord, tailWord_1940334, baseEnd_1940334] using wordTrace_append hprefix tailTrace_1940334
  have hstable : (prefixWord ++ tailWord_1940334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940334).length < 2 ^ (prefixWord ++ tailWord_1940334).sum := by decide
  have hdescent : baseEnd_1940334 < baseStart_1940334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940346 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3]
def baseStart_1940346 : Nat := 118140960795 + 1940346 * 2 ^ 59
def prefixEnd_1940346 : Nat := 4983230072969 + 3 ^ 40 * 1940346 * 2
def baseEnd_1940346 : Nat := 996330134028970621051517

theorem tailTrace_1940346 : CollatzResearch.WordTrace tailWord_1940346 prefixEnd_1940346 996330134028970621051517 := by
  unfold tailWord_1940346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17692558157116325389756223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47180155085643534372683261 17692558157116325389756223)
  ·
    refine ⟨26538837235674488084634335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17692558157116325389756223 26538837235674488084634335)
    ·
      refine ⟨39808255853511732126951503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26538837235674488084634335 39808255853511732126951503)
      ·
        refine ⟨59712383780267598190427255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39808255853511732126951503 59712383780267598190427255)
        ·
          refine ⟨89568575670401397285640883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59712383780267598190427255 89568575670401397285640883)
          ·
            refine ⟨134352863505602095928461325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89568575670401397285640883 134352863505602095928461325)
            ·
              refine ⟨50382323814600785973172997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134352863505602095928461325 50382323814600785973172997)
              ·
                refine ⟨9446685715237647369969937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50382323814600785973172997 9446685715237647369969937)
                ·
                  refine ⟨7085014286428235527477453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9446685715237647369969937 7085014286428235527477453)
                  ·
                    refine ⟨2656880357410588322804045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7085014286428235527477453 2656880357410588322804045)
                    ·
                      refine ⟨996330134028970621051517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2656880357410588322804045 996330134028970621051517)
                      ·
                        rfl

theorem cell23_1940346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_1940346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940346 prefixEnd_1940346 := by exact prefixLift 1940346
  have htrace : WordTrace (prefixWord ++ tailWord_1940346) baseStart_1940346 baseEnd_1940346 := by
    simpa [prefixWord, tailWord_1940346, baseEnd_1940346] using wordTrace_append hprefix tailTrace_1940346
  have hstable : (prefixWord ++ tailWord_1940346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940346).length < 2 ^ (prefixWord ++ tailWord_1940346).sum := by decide
  have hdescent : baseEnd_1940346 < baseStart_1940346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940383 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 2, 5]
def baseStart_1940383 : Nat := 118140960795 + 1940383 * 2 ^ 59
def prefixEnd_1940383 : Nat := 4983230072969 + 3 ^ 40 * 1940383 * 2
def baseEnd_1940383 : Nat := 332116377604395658762949

theorem tailTrace_1940383 : CollatzResearch.WordTrace tailWord_1940383 prefixEnd_1940383 332116377604395658762949 := by
  unfold tailWord_1940383
  simp only [CollatzResearch.WordTrace]
  refine ⟨70771582129331256878121803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47181054752887504585414535 70771582129331256878121803)
  ·
    refine ⟨106157373193996885317182705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70771582129331256878121803 106157373193996885317182705)
    ·
      refine ⟨79618029895497663987887029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106157373193996885317182705 79618029895497663987887029)
      ·
        refine ⟨7464190302702905998864409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79618029895497663987887029 7464190302702905998864409)
        ·
          refine ⟨5598142727027179499148307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7464190302702905998864409 5598142727027179499148307)
          ·
            refine ⟨8397214090540769248722461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598142727027179499148307 8397214090540769248722461)
            ·
              refine ⟨3148955283952788468270923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8397214090540769248722461 3148955283952788468270923)
              ·
                refine ⟨4723432925929182702406385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3148955283952788468270923 4723432925929182702406385)
                ·
                  refine ⟨3542574694446887026804789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4723432925929182702406385 3542574694446887026804789)
                  ·
                    refine ⟨332116377604395658762949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3542574694446887026804789 332116377604395658762949)
                    ·
                      rfl

theorem cell23_1940383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 5].length) (baseStart_1940383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940383 prefixEnd_1940383 := by exact prefixLift 1940383
  have htrace : WordTrace (prefixWord ++ tailWord_1940383) baseStart_1940383 baseEnd_1940383 := by
    simpa [prefixWord, tailWord_1940383, baseEnd_1940383] using wordTrace_append hprefix tailTrace_1940383
  have hstable : (prefixWord ++ tailWord_1940383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940383).length < 2 ^ (prefixWord ++ tailWord_1940383).sum := by decide
  have hdescent : baseEnd_1940383 < baseStart_1940383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940490 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 1, 5]
def baseStart_1940490 : Nat := 118140960795 + 1940490 * 2 ^ 59
def prefixEnd_1940490 : Nat := 4983230072969 + 3 ^ 40 * 1940490 * 2
def baseEnd_1940490 : Nat := 332134691747739352550285

theorem tailTrace_1940490 : CollatzResearch.WordTrace tailWord_1940490 prefixEnd_1940490 332134691747739352550285 := by
  unfold tailWord_1940490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17693871184985903538066731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47183656493295742768177949 17693871184985903538066731)
  ·
    refine ⟨26540806777478855307100097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17693871184985903538066731 26540806777478855307100097)
    ·
      refine ⟨19905605083109141480325073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26540806777478855307100097 19905605083109141480325073)
      ·
        refine ⟨14929203812331856110243805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19905605083109141480325073 14929203812331856110243805)
        ·
          refine ⟨5598451429624446041341427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14929203812331856110243805 5598451429624446041341427)
          ·
            refine ⟨8397677144436669062012141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598451429624446041341427 8397677144436669062012141)
            ·
              refine ⟨3149128929163750898254553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8397677144436669062012141 3149128929163750898254553)
              ·
                refine ⟨2361846696872813173690915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149128929163750898254553 2361846696872813173690915)
                ·
                  refine ⟨3542770045309219760536373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2361846696872813173690915 3542770045309219760536373)
                  ·
                    refine ⟨332134691747739352550285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3542770045309219760536373 332134691747739352550285)
                    ·
                      rfl

theorem cell23_1940490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_1940490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940490 prefixEnd_1940490 := by exact prefixLift 1940490
  have htrace : WordTrace (prefixWord ++ tailWord_1940490) baseStart_1940490 baseEnd_1940490 := by
    simpa [prefixWord, tailWord_1940490, baseEnd_1940490] using wordTrace_append hprefix tailTrace_1940490
  have hstable : (prefixWord ++ tailWord_1940490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940490).length < 2 ^ (prefixWord ++ tailWord_1940490).sum := by decide
  have hdescent : baseEnd_1940490 < baseStart_1940490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940503 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 3, 6]
def baseStart_1940503 : Nat := 118140960795 + 1940503 * 2 ^ 59
def prefixEnd_1940503 : Nat := 4983230072969 + 3 ^ 40 * 1940503 * 2
def baseEnd_1940503 : Nat := 332136916830575502262765

theorem tailTrace_1940503 : CollatzResearch.WordTrace tailWord_1940503 prefixEnd_1940503 332136916830575502262765 := by
  unfold tailWord_1940503
  simp only [CollatzResearch.WordTrace]
  refine ⟨70775958888896517372490163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47183972592597678248326775 70775958888896517372490163)
  ·
    refine ⟨106163938333344776058735245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70775958888896517372490163 106163938333344776058735245)
    ·
      refine ⟨39811476875004291022025717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106163938333344776058735245 39811476875004291022025717)
      ·
        refine ⟨3732325957031652283314911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39811476875004291022025717 3732325957031652283314911)
        ·
          refine ⟨5598488935547478424972367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732325957031652283314911 5598488935547478424972367)
          ·
            refine ⟨8397733403321217637458551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598488935547478424972367 8397733403321217637458551)
            ·
              refine ⟨12596600104981826456187827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8397733403321217637458551 12596600104981826456187827)
              ·
                refine ⟨18894900157472739684281741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12596600104981826456187827 18894900157472739684281741)
                ·
                  refine ⟨7085587559052277381605653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18894900157472739684281741 7085587559052277381605653)
                  ·
                    refine ⟨332136916830575502262765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7085587559052277381605653 332136916830575502262765)
                    ·
                      rfl

theorem cell23_1940503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_1940503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940503 prefixEnd_1940503 := by exact prefixLift 1940503
  have htrace : WordTrace (prefixWord ++ tailWord_1940503) baseStart_1940503 baseEnd_1940503 := by
    simpa [prefixWord, tailWord_1940503, baseEnd_1940503] using wordTrace_append hprefix tailTrace_1940503
  have hstable : (prefixWord ++ tailWord_1940503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940503).length < 2 ^ (prefixWord ++ tailWord_1940503).sum := by decide
  have hdescent : baseEnd_1940503 < baseStart_1940503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940540 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_1940540 : Nat := 118140960795 + 1940540 * 2 ^ 59
def prefixEnd_1940540 : Nat := 4983230072969 + 3 ^ 40 * 1940540 * 2
def baseEnd_1940540 : Nat := 996429749275942862025625

theorem tailTrace_1940540 : CollatzResearch.WordTrace tailWord_1940540 prefixEnd_1940540 996429749275942862025625 := by
  unfold tailWord_1940540
  simp only [CollatzResearch.WordTrace]
  refine ⟨35388654194881236345793537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47184872259841648461058049 35388654194881236345793537)
  ·
    refine ⟨26541490646160927259345153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35388654194881236345793537 26541490646160927259345153)
    ·
      refine ⟨19906117984620695444508865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26541490646160927259345153 19906117984620695444508865)
      ·
        refine ⟨14929588488465521583381649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19906117984620695444508865 14929588488465521583381649)
        ·
          refine ⟨11197191366349141187536237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14929588488465521583381649 11197191366349141187536237)
          ·
            refine ⟨4198946762380927945326089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11197191366349141187536237 4198946762380927945326089)
            ·
              refine ⟨3149210071785695958994567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198946762380927945326089 3149210071785695958994567)
              ·
                refine ⟨4723815107678543938491851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3149210071785695958994567 4723815107678543938491851)
                ·
                  refine ⟨7085722661517815907737777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4723815107678543938491851 7085722661517815907737777)
                  ·
                    refine ⟨5314291996138361930803333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7085722661517815907737777 5314291996138361930803333)
                    ·
                      refine ⟨996429749275942862025625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5314291996138361930803333 996429749275942862025625)
                      ·
                        rfl

theorem cell23_1940540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_1940540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940540 prefixEnd_1940540 := by exact prefixLift 1940540
  have htrace : WordTrace (prefixWord ++ tailWord_1940540) baseStart_1940540 baseEnd_1940540 := by
    simpa [prefixWord, tailWord_1940540, baseEnd_1940540] using wordTrace_append hprefix tailTrace_1940540
  have hstable : (prefixWord ++ tailWord_1940540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940540).length < 2 ^ (prefixWord ++ tailWord_1940540).sum := by decide
  have hdescent : baseEnd_1940540 < baseStart_1940540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940570 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2]
def baseStart_1940570 : Nat := 118140960795 + 1940570 * 2 ^ 59
def prefixEnd_1940570 : Nat := 4983230072969 + 3 ^ 40 * 1940570 * 2
def baseEnd_1940570 : Nat := 996445153695577744650487

theorem tailTrace_1940570 : CollatzResearch.WordTrace tailWord_1940570 prefixEnd_1940570 996445153695577744650487 := by
  unfold tailWord_1940570
  simp only [CollatzResearch.WordTrace]
  refine ⟨17694600644913446953794791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47185601719769191876786109 17694600644913446953794791)
  ·
    refine ⟨26541900967370170430692187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17694600644913446953794791 26541900967370170430692187)
    ·
      refine ⟨39812851451055255646038281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26541900967370170430692187 39812851451055255646038281)
      ·
        refine ⟨29859638588291441734528711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39812851451055255646038281 29859638588291441734528711)
        ·
          refine ⟨44789457882437162601793067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29859638588291441734528711 44789457882437162601793067)
          ·
            refine ⟨67184186823655743902689601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44789457882437162601793067 67184186823655743902689601)
            ·
              refine ⟨50388140117741807927017201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67184186823655743902689601 50388140117741807927017201)
              ·
                refine ⟨37791105088306355945262901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50388140117741807927017201 37791105088306355945262901)
                ·
                  refine ⟨3542916102028720869868397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37791105088306355945262901 3542916102028720869868397)
                  ·
                    refine ⟨1328593538260770326200649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3542916102028720869868397 1328593538260770326200649)
                    ·
                      refine ⟨996445153695577744650487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1328593538260770326200649 996445153695577744650487)
                      ·
                        rfl

theorem cell23_1940570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_1940570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940570 prefixEnd_1940570 := by exact prefixLift 1940570
  have htrace : WordTrace (prefixWord ++ tailWord_1940570) baseStart_1940570 baseEnd_1940570 := by
    simpa [prefixWord, tailWord_1940570, baseEnd_1940570] using wordTrace_append hprefix tailTrace_1940570
  have hstable : (prefixWord ++ tailWord_1940570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940570).length < 2 ^ (prefixWord ++ tailWord_1940570).sum := by decide
  have hdescent : baseEnd_1940570 < baseStart_1940570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940577 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_1940577 : Nat := 118140960795 + 1940577 * 2 ^ 59
def prefixEnd_1940577 : Nat := 4983230072969 + 3 ^ 40 * 1940577 * 2
def baseEnd_1940577 : Nat := 996448748060159217262955

theorem tailTrace_1940577 : CollatzResearch.WordTrace tailWord_1940577 prefixEnd_1940577 996448748060159217262955 := by
  unfold tailWord_1940577
  simp only [CollatzResearch.WordTrace]
  refine ⟨70778657890628428010683985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47185771927085618673789323 70778657890628428010683985)
  ·
    refine ⟨53083993417971321008012989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70778657890628428010683985 53083993417971321008012989)
    ·
      refine ⟨19906497531739245378004871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53083993417971321008012989 19906497531739245378004871)
      ·
        refine ⟨29859746297608868067007307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19906497531739245378004871 29859746297608868067007307)
        ·
          refine ⟨44789619446413302100510961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29859746297608868067007307 44789619446413302100510961)
          ·
            refine ⟨33592214584809976575383221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44789619446413302100510961 33592214584809976575383221)
            ·
              refine ⟨3149270117325935303942177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33592214584809976575383221 3149270117325935303942177)
              ·
                refine ⟨2361952587994451477956633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149270117325935303942177 2361952587994451477956633)
                ·
                  refine ⟨1771464440995838608467475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2361952587994451477956633 1771464440995838608467475)
                  ·
                    refine ⟨2657196661493757912701213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1771464440995838608467475 2657196661493757912701213)
                    ·
                      refine ⟨996448748060159217262955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2657196661493757912701213 996448748060159217262955)
                      ·
                        rfl

theorem cell23_1940577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_1940577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940577 prefixEnd_1940577 := by exact prefixLift 1940577
  have htrace : WordTrace (prefixWord ++ tailWord_1940577) baseStart_1940577 baseEnd_1940577 := by
    simpa [prefixWord, tailWord_1940577, baseEnd_1940577] using wordTrace_append hprefix tailTrace_1940577
  have hstable : (prefixWord ++ tailWord_1940577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940577).length < 2 ^ (prefixWord ++ tailWord_1940577).sum := by decide
  have hdescent : baseEnd_1940577 < baseStart_1940577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940594 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 2, 1, 3]
def baseStart_1940594 : Nat := 118140960795 + 1940594 * 2 ^ 59
def prefixEnd_1940594 : Nat := 4983230072969 + 3 ^ 40 * 1940594 * 2
def baseEnd_1940594 : Nat := 996457477231285650750377

theorem tailTrace_1940594 : CollatzResearch.WordTrace tailWord_1940594 prefixEnd_1940594 996457477231285650750377 := by
  unfold tailWord_1940594
  simp only [CollatzResearch.WordTrace]
  refine ⟨17694819482891709978513209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47186185287711226609368557 17694819482891709978513209)
  ·
    refine ⟨13271114612168782483884907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17694819482891709978513209 13271114612168782483884907)
    ·
      refine ⟨19906671918253173725827361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13271114612168782483884907 19906671918253173725827361)
      ·
        refine ⟨14930003938689880294370521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19906671918253173725827361 14930003938689880294370521)
        ·
          refine ⟨11197502954017410220777891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14930003938689880294370521 11197502954017410220777891)
          ·
            refine ⟨16796254431026115331166837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11197502954017410220777891 16796254431026115331166837)
            ·
              refine ⟨1574648852908698312296891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16796254431026115331166837 1574648852908698312296891)
              ·
                refine ⟨2361973279363047468445337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574648852908698312296891 2361973279363047468445337)
                ·
                  refine ⟨1771479959522285601334003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2361973279363047468445337 1771479959522285601334003)
                  ·
                    refine ⟨2657219939283428402001005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1771479959522285601334003 2657219939283428402001005)
                    ·
                      refine ⟨996457477231285650750377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2657219939283428402001005 996457477231285650750377)
                      ·
                        rfl

theorem cell23_1940594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_1940594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940594 prefixEnd_1940594 := by exact prefixLift 1940594
  have htrace : WordTrace (prefixWord ++ tailWord_1940594) baseStart_1940594 baseEnd_1940594 := by
    simpa [prefixWord, tailWord_1940594, baseEnd_1940594] using wordTrace_append hprefix tailTrace_1940594
  have hstable : (prefixWord ++ tailWord_1940594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940594).length < 2 ^ (prefixWord ++ tailWord_1940594).sum := by decide
  have hdescent : baseEnd_1940594 < baseStart_1940594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940603 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 3]
def baseStart_1940603 : Nat := 118140960795 + 1940603 * 2 ^ 59
def prefixEnd_1940603 : Nat := 4983230072969 + 3 ^ 40 * 1940603 * 2
def baseEnd_1940603 : Nat := 996462098557176115537835

theorem tailTrace_1940603 : CollatzResearch.WordTrace tailWord_1940603 prefixEnd_1940603 996462098557176115537835 := by
  unfold tailWord_1940603
  simp only [CollatzResearch.WordTrace]
  refine ⟨70779606188534234451130463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47186404125689489634086975 70779606188534234451130463)
  ·
    refine ⟨106169409282801351676695695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70779606188534234451130463 106169409282801351676695695)
    ·
      refine ⟨159254113924202027515043543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106169409282801351676695695 159254113924202027515043543)
      ·
        refine ⟨238881170886303041272565315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159254113924202027515043543 238881170886303041272565315)
        ·
          refine ⟨358321756329454561908847973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238881170886303041272565315 358321756329454561908847973)
          ·
            refine ⟨67185329311772730357908995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358321756329454561908847973 67185329311772730357908995)
            ·
              refine ⟨100777993967659095536863493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67185329311772730357908995 100777993967659095536863493)
              ·
                refine ⟨18895873868936080413161905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100777993967659095536863493 18895873868936080413161905)
                ·
                  refine ⟨14171905401702060309871429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18895873868936080413161905 14171905401702060309871429)
                  ·
                    refine ⟨2657232262819136308100893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14171905401702060309871429 2657232262819136308100893)
                    ·
                      refine ⟨996462098557176115537835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2657232262819136308100893 996462098557176115537835)
                      ·
                        rfl

theorem cell23_1940603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 3].length) (baseStart_1940603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940603 prefixEnd_1940603 := by exact prefixLift 1940603
  have htrace : WordTrace (prefixWord ++ tailWord_1940603) baseStart_1940603 baseEnd_1940603 := by
    simpa [prefixWord, tailWord_1940603, baseEnd_1940603] using wordTrace_append hprefix tailTrace_1940603
  have hstable : (prefixWord ++ tailWord_1940603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940603).length < 2 ^ (prefixWord ++ tailWord_1940603).sum := by decide
  have hdescent : baseEnd_1940603 < baseStart_1940603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940617 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 4, 2, 2]
def baseStart_1940617 : Nat := 118140960795 + 1940617 * 2 ^ 59
def prefixEnd_1940617 : Nat := 4983230072969 + 3 ^ 40 * 1940617 * 2
def baseEnd_1940617 : Nat := 996469287286339060762771

theorem tailTrace_1940617 : CollatzResearch.WordTrace tailWord_1940617 prefixEnd_1940617 996469287286339060762771 := by
  unfold tailWord_1940617
  simp only [CollatzResearch.WordTrace]
  refine ⟨70780116810483514842140105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47186744540322343228093403 70780116810483514842140105)
  ·
    refine ⟨53085087607862636131605079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70780116810483514842140105 53085087607862636131605079)
    ·
      refine ⟨79627631411793954197407619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53085087607862636131605079 79627631411793954197407619)
      ·
        refine ⟨119441447117690931296111429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79627631411793954197407619 119441447117690931296111429)
        ·
          refine ⟨22395271334567049618020893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119441447117690931296111429 22395271334567049618020893)
          ·
            refine ⟨8398226750462643606757835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22395271334567049618020893 8398226750462643606757835)
            ·
              refine ⟨12597340125693965410136753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8398226750462643606757835 12597340125693965410136753)
              ·
                refine ⟨9448005094270474057602565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12597340125693965410136753 9448005094270474057602565)
                ·
                  refine ⟨1771500955175713885800481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9448005094270474057602565 1771500955175713885800481)
                  ·
                    refine ⟨1328625716381785414350361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1771500955175713885800481 1328625716381785414350361)
                    ·
                      refine ⟨996469287286339060762771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1328625716381785414350361 996469287286339060762771)
                      ·
                        rfl

theorem cell23_1940617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 2, 2].length) (baseStart_1940617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940617 prefixEnd_1940617 := by exact prefixLift 1940617
  have htrace : WordTrace (prefixWord ++ tailWord_1940617) baseStart_1940617 baseEnd_1940617 := by
    simpa [prefixWord, tailWord_1940617, baseEnd_1940617] using wordTrace_append hprefix tailTrace_1940617
  have hstable : (prefixWord ++ tailWord_1940617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940617).length < 2 ^ (prefixWord ++ tailWord_1940617).sum := by decide
  have hdescent : baseEnd_1940617 < baseStart_1940617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940634 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2]
def baseStart_1940634 : Nat := 118140960795 + 1940634 * 2 ^ 59
def prefixEnd_1940634 : Nat := 4983230072969 + 3 ^ 40 * 1940634 * 2
def baseEnd_1940634 : Nat := 996478016457465494250193

theorem tailTrace_1940634 : CollatzResearch.WordTrace tailWord_1940634 prefixEnd_1940634 996478016457465494250193 := by
  unfold tailWord_1940634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17695184212855481686377239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47187157900947951163672637 17695184212855481686377239)
  ·
    refine ⟨26542776319283222529565859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17695184212855481686377239 26542776319283222529565859)
    ·
      refine ⟨39814164478924833794348789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26542776319283222529565859 39814164478924833794348789)
      ·
        refine ⟨3732577919899203168220199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39814164478924833794348789 3732577919899203168220199)
        ·
          refine ⟨5598866879848804752330299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732577919899203168220199 5598866879848804752330299)
          ·
            refine ⟨8398300319773207128495449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5598866879848804752330299 8398300319773207128495449)
            ·
              refine ⟨6298725239829905346371587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8398300319773207128495449 6298725239829905346371587)
              ·
                refine ⟨9448087859744858019557381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6298725239829905346371587 9448087859744858019557381)
                ·
                  refine ⟨1771516473702160878667009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9448087859744858019557381 1771516473702160878667009)
                  ·
                    refine ⟨1328637355276620659000257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1771516473702160878667009 1328637355276620659000257)
                    ·
                      refine ⟨996478016457465494250193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1328637355276620659000257 996478016457465494250193)
                      ·
                        rfl

theorem cell23_1940634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_1940634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940634 prefixEnd_1940634 := by exact prefixLift 1940634
  have htrace : WordTrace (prefixWord ++ tailWord_1940634) baseStart_1940634 baseEnd_1940634 := by
    simpa [prefixWord, tailWord_1940634, baseEnd_1940634] using wordTrace_append hprefix tailTrace_1940634
  have hstable : (prefixWord ++ tailWord_1940634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940634).length < 2 ^ (prefixWord ++ tailWord_1940634).sum := by decide
  have hdescent : baseEnd_1940634 < baseStart_1940634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940663 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_1940663 : Nat := 118140960795 + 1940663 * 2 ^ 59
def prefixEnd_1940663 : Nat := 4983230072969 + 3 ^ 40 * 1940663 * 2
def baseEnd_1940663 : Nat := 996492907396445880787559

theorem tailTrace_1940663 : CollatzResearch.WordTrace tailWord_1940663 prefixEnd_1940663 996492907396445880787559 := by
  unfold tailWord_1940663
  simp only [CollatzResearch.WordTrace]
  refine ⟨70781794568316864698314643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47187863045544576465543095 70781794568316864698314643)
  ·
    refine ⟨106172691852475297047471965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70781794568316864698314643 106172691852475297047471965)
    ·
      refine ⟨39814759444678236392801987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106172691852475297047471965 39814759444678236392801987)
      ·
        refine ⟨59722139167017354589202981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39814759444678236392801987 59722139167017354589202981)
        ·
          refine ⟨11197901093815753985475559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59722139167017354589202981 11197901093815753985475559)
          ·
            refine ⟨16796851640723630978213339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11197901093815753985475559 16796851640723630978213339)
            ·
              refine ⟨25195277461085446467320009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16796851640723630978213339 25195277461085446467320009)
              ·
                refine ⟨18896458095814084850490007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25195277461085446467320009 18896458095814084850490007)
                ·
                  refine ⟨28344687143721127275735011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18896458095814084850490007 28344687143721127275735011)
                  ·
                    refine ⟨42517030715581690913602517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28344687143721127275735011 42517030715581690913602517)
                    ·
                      refine ⟨996492907396445880787559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42517030715581690913602517 996492907396445880787559)
                      ·
                        rfl

theorem cell23_1940663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_1940663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940663 prefixEnd_1940663 := by exact prefixLift 1940663
  have htrace : WordTrace (prefixWord ++ tailWord_1940663) baseStart_1940663 baseEnd_1940663 := by
    simpa [prefixWord, tailWord_1940663, baseEnd_1940663] using wordTrace_append hprefix tailTrace_1940663
  have hstable : (prefixWord ++ tailWord_1940663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940663).length < 2 ^ (prefixWord ++ tailWord_1940663).sum := by decide
  have hdescent : baseEnd_1940663 < baseStart_1940663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940685 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1940685 : Nat := 118140960795 + 1940685 * 2 ^ 59
def prefixEnd_1940685 : Nat := 4983230072969 + 3 ^ 40 * 1940685 * 2
def baseEnd_1940685 : Nat := 996504203970844794712459

theorem tailTrace_1940685 : CollatzResearch.WordTrace tailWord_1940685 prefixEnd_1940685 996504203970844794712459 := by
  unfold tailWord_1940685
  simp only [CollatzResearch.WordTrace]
  refine ⟨70782596974237162455615509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47188397982824774970410339 70782596974237162455615509)
  ·
    refine ⟨3317934233167366990106977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70782596974237162455615509 3317934233167366990106977)
    ·
      refine ⟨2488450674875525242580233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3317934233167366990106977 2488450674875525242580233)
      ·
        refine ⟨1866338006156643931935175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2488450674875525242580233 1866338006156643931935175)
        ·
          refine ⟨2799507009234965897902763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866338006156643931935175 2799507009234965897902763)
          ·
            refine ⟨4199260513852448846854145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799507009234965897902763 4199260513852448846854145)
            ·
              refine ⟨3149445385389336635140609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4199260513852448846854145 3149445385389336635140609)
              ·
                refine ⟨2362084039042002476355457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149445385389336635140609 2362084039042002476355457)
                ·
                  refine ⟨1771563029281501857266593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2362084039042002476355457 1771563029281501857266593)
                  ·
                    refine ⟨1328672271961126392949945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1771563029281501857266593 1328672271961126392949945)
                    ·
                      refine ⟨996504203970844794712459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1328672271961126392949945 996504203970844794712459)
                      ·
                        rfl

theorem cell23_1940685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1940685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940685 prefixEnd_1940685 := by exact prefixLift 1940685
  have htrace : WordTrace (prefixWord ++ tailWord_1940685) baseStart_1940685 baseEnd_1940685 := by
    simpa [prefixWord, tailWord_1940685, baseEnd_1940685] using wordTrace_append hprefix tailTrace_1940685
  have hstable : (prefixWord ++ tailWord_1940685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940685).length < 2 ^ (prefixWord ++ tailWord_1940685).sum := by decide
  have hdescent : baseEnd_1940685 < baseStart_1940685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940717 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_1940717 : Nat := 118140960795 + 1940717 * 2 ^ 59
def prefixEnd_1940717 : Nat := 4983230072969 + 3 ^ 40 * 1940717 * 2
def baseEnd_1940717 : Nat := 332173545117262889837437

theorem tailTrace_1940717 : CollatzResearch.WordTrace tailWord_1940717 prefixEnd_1940717 332173545117262889837437 := by
  unfold tailWord_1940717
  simp only [CollatzResearch.WordTrace]
  refine ⟨70783764110121231920780405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47189176073414154613853603 70783764110121231920780405)
  ·
    refine ⟨6635977885323865492573163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70783764110121231920780405 6635977885323865492573163)
    ·
      refine ⟨9953966827985798238859745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6635977885323865492573163 9953966827985798238859745)
      ·
        refine ⟨7465475120989348679144809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9953966827985798238859745 7465475120989348679144809)
        ·
          refine ⟨5599106340742011509358607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7465475120989348679144809 5599106340742011509358607)
          ·
            refine ⟨8398659511113017264037911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5599106340742011509358607 8398659511113017264037911)
            ·
              refine ⟨12597989266669525896056867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8398659511113017264037911 12597989266669525896056867)
              ·
                refine ⟨18896983900004288844085301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12597989266669525896056867 18896983900004288844085301)
                ·
                  refine ⟨1771592240625402079132997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18896983900004288844085301 1771592240625402079132997)
                  ·
                    refine ⟨332173545117262889837437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1771592240625402079132997 332173545117262889837437)
                    ·
                      rfl

theorem cell23_1940717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_1940717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940717 prefixEnd_1940717 := by exact prefixLift 1940717
  have htrace : WordTrace (prefixWord ++ tailWord_1940717) baseStart_1940717 baseEnd_1940717 := by
    simpa [prefixWord, tailWord_1940717, baseEnd_1940717] using wordTrace_append hprefix tailTrace_1940717
  have hstable : (prefixWord ++ tailWord_1940717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940717).length < 2 ^ (prefixWord ++ tailWord_1940717).sum := by decide
  have hdescent : baseEnd_1940717 < baseStart_1940717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940747 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 6]
def baseStart_1940747 : Nat := 118140960795 + 1940747 * 2 ^ 59
def prefixEnd_1940747 : Nat := 4983230072969 + 3 ^ 40 * 1940747 * 2
def baseEnd_1940747 : Nat := 110726226641269283570797

theorem tailTrace_1940747 : CollatzResearch.WordTrace tailWord_1940747 prefixEnd_1940747 110726226641269283570797 := by
  unfold tailWord_1940747
  simp only [CollatzResearch.WordTrace]
  refine ⟨70784858300012547044372495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47189905533341698029581663 70784858300012547044372495)
  ·
    refine ⟨106177287450018820566558743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70784858300012547044372495 106177287450018820566558743)
    ·
      refine ⟨159265931175028230849838115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106177287450018820566558743 159265931175028230849838115)
      ·
        refine ⟨238898896762542346274757173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159265931175028230849838115 238898896762542346274757173)
        ·
          refine ⟨22396771571488344963258485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238898896762542346274757173 22396771571488344963258485)
          ·
            refine ⟨2099697334827032340305483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22396771571488344963258485 2099697334827032340305483)
            ·
              refine ⟨3149546002240548510458225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099697334827032340305483 3149546002240548510458225)
              ·
                refine ⟨2362159501680411382843669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3149546002240548510458225 2362159501680411382843669)
                ·
                  refine ⟨110726226641269283570797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2362159501680411382843669 110726226641269283570797)
                  ·
                    rfl

theorem cell23_1940747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 6].length) (baseStart_1940747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940747 prefixEnd_1940747 := by exact prefixLift 1940747
  have htrace : WordTrace (prefixWord ++ tailWord_1940747) baseStart_1940747 baseEnd_1940747 := by
    simpa [prefixWord, tailWord_1940747, baseEnd_1940747] using wordTrace_append hprefix tailTrace_1940747
  have hstable : (prefixWord ++ tailWord_1940747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940747).length < 2 ^ (prefixWord ++ tailWord_1940747).sum := by decide
  have hdescent : baseEnd_1940747 < baseStart_1940747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940750 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1940750 : Nat := 118140960795 + 1940750 * 2 ^ 59
def prefixEnd_1940750 : Nat := 4983230072969 + 3 ^ 40 * 1940750 * 2
def baseEnd_1940750 : Nat := 996537580213387040399659

theorem tailTrace_1940750 : CollatzResearch.WordTrace tailWord_1940750 prefixEnd_1940750 996537580213387040399659 := by
  unfold tailWord_1940750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8848120964875209819591463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47189978479334452371154469 8848120964875209819591463)
  ·
    refine ⟨13272181447312814729387195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8848120964875209819591463 13272181447312814729387195)
    ·
      refine ⟨19908272170969222094080793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13272181447312814729387195 19908272170969222094080793)
      ·
        refine ⟨14931204128226916570560595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19908272170969222094080793 14931204128226916570560595)
        ·
          refine ⟨22396806192340374855840893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14931204128226916570560595 22396806192340374855840893)
          ·
            refine ⟨8398802322127640570940335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22396806192340374855840893 8398802322127640570940335)
            ·
              refine ⟨12598203483191460856410503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8398802322127640570940335 12598203483191460856410503)
              ·
                refine ⟨18897305224787191284615755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12598203483191460856410503 18897305224787191284615755)
                ·
                  refine ⟨28345957837180786926923633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18897305224787191284615755 28345957837180786926923633)
                  ·
                    refine ⟨21259468377885590195192725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28345957837180786926923633 21259468377885590195192725)
                    ·
                      refine ⟨996537580213387040399659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21259468377885590195192725 996537580213387040399659)
                      ·
                        rfl

theorem cell23_1940750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1940750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940750 prefixEnd_1940750 := by exact prefixLift 1940750
  have htrace : WordTrace (prefixWord ++ tailWord_1940750) baseStart_1940750 baseEnd_1940750 := by
    simpa [prefixWord, tailWord_1940750, baseEnd_1940750] using wordTrace_append hprefix tailTrace_1940750
  have hstable : (prefixWord ++ tailWord_1940750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940750).length < 2 ^ (prefixWord ++ tailWord_1940750).sum := by decide
  have hdescent : baseEnd_1940750 < baseStart_1940750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940801 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_1940801 : Nat := 118140960795 + 1940801 * 2 ^ 59
def prefixEnd_1940801 : Nat := 4983230072969 + 3 ^ 40 * 1940801 * 2
def baseEnd_1940801 : Nat := 996563767726766340861925

theorem tailTrace_1940801 : CollatzResearch.WordTrace tailWord_1940801 prefixEnd_1940801 996563767726766340861925 := by
  unfold tailWord_1940801
  simp only [CollatzResearch.WordTrace]
  refine ⟨70786827841816914266838257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47191218561211276177892171 70786827841816914266838257)
  ·
    refine ⟨53090120881362685700128693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70786827841816914266838257 53090120881362685700128693)
    ·
      refine ⟨4977198832627751784387065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53090120881362685700128693 4977198832627751784387065)
      ·
        refine ⟨3732899124470813838290299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4977198832627751784387065 3732899124470813838290299)
        ·
          refine ⟨5599348686706220757435449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3732899124470813838290299 5599348686706220757435449)
          ·
            refine ⟨4199511515029665568076587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5599348686706220757435449 4199511515029665568076587)
            ·
              refine ⟨6299267272544498352114881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199511515029665568076587 6299267272544498352114881)
              ·
                refine ⟨4724450454408373764086161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6299267272544498352114881 4724450454408373764086161)
                ·
                  refine ⟨3543337840806280323064621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4724450454408373764086161 3543337840806280323064621)
                  ·
                    refine ⟨1328751690302355121149233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3543337840806280323064621 1328751690302355121149233)
                    ·
                      refine ⟨996563767726766340861925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1328751690302355121149233 996563767726766340861925)
                      ·
                        rfl

theorem cell23_1940801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_1940801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940801 prefixEnd_1940801 := by exact prefixLift 1940801
  have htrace : WordTrace (prefixWord ++ tailWord_1940801) baseStart_1940801 baseEnd_1940801 := by
    simpa [prefixWord, tailWord_1940801, baseEnd_1940801] using wordTrace_append hprefix tailTrace_1940801
  have hstable : (prefixWord ++ tailWord_1940801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940801).length < 2 ^ (prefixWord ++ tailWord_1940801).sum := by decide
  have hdescent : baseEnd_1940801 < baseStart_1940801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940807 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 4, 4]
def baseStart_1940807 : Nat := 118140960795 + 1940807 * 2 ^ 59
def prefixEnd_1940807 : Nat := 4983230072969 + 3 ^ 40 * 1940807 * 2
def baseEnd_1940807 : Nat := 332188949536897772462299

theorem tailTrace_1940807 : CollatzResearch.WordTrace tailWord_1940807 prefixEnd_1940807 332188949536897772462299 := by
  unfold tailWord_1940807
  simp only [CollatzResearch.WordTrace]
  refine ⟨70787046679795177291556675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47191364453196784861037783 70787046679795177291556675)
  ·
    refine ⟨106180570019692765937335013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70787046679795177291556675 106180570019692765937335013)
    ·
      refine ⟨19908856878692393613250315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106180570019692765937335013 19908856878692393613250315)
      ·
        refine ⟨29863285318038590419875473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19908856878692393613250315 29863285318038590419875473)
        ·
          refine ⟨22397463988528942814906605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29863285318038590419875473 22397463988528942814906605)
          ·
            refine ⟨8399048995698353555589977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22397463988528942814906605 8399048995698353555589977)
            ·
              refine ⟨6299286746773765166692483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8399048995698353555589977 6299286746773765166692483)
              ·
                refine ⟨9448930120160647750038725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299286746773765166692483 9448930120160647750038725)
                ·
                  refine ⟨1771674397530121453132261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9448930120160647750038725 1771674397530121453132261)
                  ·
                    refine ⟨332188949536897772462299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1771674397530121453132261 332188949536897772462299)
                    ·
                      rfl

theorem cell23_1940807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_1940807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940807 prefixEnd_1940807 := by exact prefixLift 1940807
  have htrace : WordTrace (prefixWord ++ tailWord_1940807) baseStart_1940807 baseEnd_1940807 := by
    simpa [prefixWord, tailWord_1940807, baseEnd_1940807] using wordTrace_append hprefix tailTrace_1940807
  have hstable : (prefixWord ++ tailWord_1940807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940807).length < 2 ^ (prefixWord ++ tailWord_1940807).sum := by decide
  have hdescent : baseEnd_1940807 < baseStart_1940807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940817 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 3, 2, 3]
def baseStart_1940817 : Nat := 118140960795 + 1940817 * 2 ^ 59
def prefixEnd_1940817 : Nat := 4983230072969 + 3 ^ 40 * 1940817 * 2
def baseEnd_1940817 : Nat := 996571983417238278261851

theorem tailTrace_1940817 : CollatzResearch.WordTrace tailWord_1940817 prefixEnd_1940817 996571983417238278261851 := by
  unfold tailWord_1940817
  simp only [CollatzResearch.WordTrace]
  refine ⟨70787411409758948999420705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47191607606505965999613803 70787411409758948999420705)
  ·
    refine ⟨53090558557319211749565529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70787411409758948999420705 53090558557319211749565529)
    ·
      refine ⟨39817918917989408812174147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53090558557319211749565529 39817918917989408812174147)
      ·
        refine ⟨59726878376984113218261221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39817918917989408812174147 59726878376984113218261221)
        ·
          refine ⟨11198789695684521228423979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59726878376984113218261221 11198789695684521228423979)
          ·
            refine ⟨16798184543526781842635969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11198789695684521228423979 16798184543526781842635969)
            ·
              refine ⟨12598638407645086381976977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16798184543526781842635969 12598638407645086381976977)
              ·
                refine ⟨9448978805733814786482733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12598638407645086381976977 9448978805733814786482733)
                ·
                  refine ⟨3543367052150180544931025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9448978805733814786482733 3543367052150180544931025)
                  ·
                    refine ⟨2657525289112635408698269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3543367052150180544931025 2657525289112635408698269)
                    ·
                      refine ⟨996571983417238278261851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2657525289112635408698269 996571983417238278261851)
                      ·
                        rfl

theorem cell23_1940817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_1940817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940817 prefixEnd_1940817 := by exact prefixLift 1940817
  have htrace : WordTrace (prefixWord ++ tailWord_1940817) baseStart_1940817 baseEnd_1940817 := by
    simpa [prefixWord, tailWord_1940817, baseEnd_1940817] using wordTrace_append hprefix tailTrace_1940817
  have hstable : (prefixWord ++ tailWord_1940817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940817).length < 2 ^ (prefixWord ++ tailWord_1940817).sum := by decide
  have hdescent : baseEnd_1940817 < baseStart_1940817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940834 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_1940834 : Nat := 118140960795 + 1940834 * 2 ^ 59
def prefixEnd_1940834 : Nat := 4983230072969 + 3 ^ 40 * 1940834 * 2
def baseEnd_1940834 : Nat := 996580712588364711749273

theorem tailTrace_1940834 : CollatzResearch.WordTrace tailWord_1940834 prefixEnd_1940834 996580712588364711749273 := by
  unfold tailWord_1940834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17697007862674340225697389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47192020967131573935193037 17697007862674340225697389)
  ·
    refine ⟨6636377948502877584636521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17697007862674340225697389 6636377948502877584636521)
    ·
      refine ⟨4977283461377158188477391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6636377948502877584636521 4977283461377158188477391)
      ·
        refine ⟨7465925192065737282716087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977283461377158188477391 7465925192065737282716087)
        ·
          refine ⟨11198887788098605924074131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7465925192065737282716087 11198887788098605924074131)
          ·
            refine ⟨16798331682147908886111197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11198887788098605924074131 16798331682147908886111197)
            ·
              refine ⟨6299374380805465832291699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16798331682147908886111197 6299374380805465832291699)
              ·
                refine ⟨9449061571208198748437549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6299374380805465832291699 9449061571208198748437549)
                ·
                  refine ⟨3543398089203074530664081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9449061571208198748437549 3543398089203074530664081)
                  ·
                    refine ⟨2657548566902305897998061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3543398089203074530664081 2657548566902305897998061)
                    ·
                      refine ⟨996580712588364711749273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2657548566902305897998061 996580712588364711749273)
                      ·
                        rfl

theorem cell23_1940834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_1940834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940834 prefixEnd_1940834 := by exact prefixLift 1940834
  have htrace : WordTrace (prefixWord ++ tailWord_1940834) baseStart_1940834 baseEnd_1940834 := by
    simpa [prefixWord, tailWord_1940834, baseEnd_1940834] using wordTrace_append hprefix tailTrace_1940834
  have hstable : (prefixWord ++ tailWord_1940834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940834).length < 2 ^ (prefixWord ++ tailWord_1940834).sum := by decide
  have hdescent : baseEnd_1940834 < baseStart_1940834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940847 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 3]
def baseStart_1940847 : Nat := 118140960795 + 1940847 * 2 ^ 59
def prefixEnd_1940847 : Nat := 4983230072969 + 3 ^ 40 * 1940847 * 2
def baseEnd_1940847 : Nat := 996587387836873160886713

theorem tailTrace_1940847 : CollatzResearch.WordTrace tailWord_1940847 prefixEnd_1940847 996587387836873160886713 := by
  unfold tailWord_1940847
  simp only [CollatzResearch.WordTrace]
  refine ⟨70788505599650264123012795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47192337066433509415341863 70788505599650264123012795)
  ·
    refine ⟨106182758399475396184519193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70788505599650264123012795 106182758399475396184519193)
    ·
      refine ⟨79637068799606547138389395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106182758399475396184519193 79637068799606547138389395)
      ·
        refine ⟨119455603199409820707584093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79637068799606547138389395 119455603199409820707584093)
        ·
          refine ⟨44795851199778682765344035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119455603199409820707584093 44795851199778682765344035)
          ·
            refine ⟨67193776799668024148016053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44795851199778682765344035 67193776799668024148016053)
            ·
              refine ⟨6299416574968877263876505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67193776799668024148016053 6299416574968877263876505)
              ·
                refine ⟨4724562431226657947907379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6299416574968877263876505 4724562431226657947907379)
                ·
                  refine ⟨7086843646839986921861069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4724562431226657947907379 7086843646839986921861069)
                  ·
                    refine ⟨2657566367564995095697901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7086843646839986921861069 2657566367564995095697901)
                    ·
                      refine ⟨996587387836873160886713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2657566367564995095697901 996587387836873160886713)
                      ·
                        rfl

theorem cell23_1940847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 3].length) (baseStart_1940847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940847 prefixEnd_1940847 := by exact prefixLift 1940847
  have htrace : WordTrace (prefixWord ++ tailWord_1940847) baseStart_1940847 baseEnd_1940847 := by
    simpa [prefixWord, tailWord_1940847, baseEnd_1940847] using wordTrace_append hprefix tailTrace_1940847
  have hstable : (prefixWord ++ tailWord_1940847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940847).length < 2 ^ (prefixWord ++ tailWord_1940847).sum := by decide
  have hdescent : baseEnd_1940847 < baseStart_1940847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940865 : List Nat := [1, 2, 4, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_1940865 : Nat := 118140960795 + 1940865 * 2 ^ 59
def prefixEnd_1940865 : Nat := 4983230072969 + 3 ^ 40 * 1940865 * 2
def baseEnd_1940865 : Nat := 996596630488654090461631

theorem tailTrace_1940865 : CollatzResearch.WordTrace tailWord_1940865 prefixEnd_1940865 996596630488654090461631 := by
  unfold tailWord_1940865
  simp only [CollatzResearch.WordTrace]
  refine ⟨70789162113585053197168049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47192774742390035464778699 70789162113585053197168049)
  ·
    refine ⟨53091871585188789897876037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70789162113585053197168049 53091871585188789897876037)
    ·
      refine ⟨9954725922222898105851757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53091871585188789897876037 9954725922222898105851757)
      ·
        refine ⟨3733022220833586789694409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9954725922222898105851757 3733022220833586789694409)
        ·
          refine ⟨2799766665625190092270807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3733022220833586789694409 2799766665625190092270807)
          ·
            refine ⟨4199649998437785138406211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2799766665625190092270807 4199649998437785138406211)
            ·
              refine ⟨6299474997656677707609317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4199649998437785138406211 6299474997656677707609317)
              ·
                refine ⟨1181151562060627070176747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6299474997656677707609317 1181151562060627070176747)
                ·
                  refine ⟨1771727343090940605265121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1181151562060627070176747 1771727343090940605265121)
                  ·
                    refine ⟨1328795507318205453948841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1771727343090940605265121 1328795507318205453948841)
                    ·
                      refine ⟨996596630488654090461631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1328795507318205453948841 996596630488654090461631)
                      ·
                        rfl

theorem cell23_1940865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_1940865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940865 prefixEnd_1940865 := by exact prefixLift 1940865
  have htrace : WordTrace (prefixWord ++ tailWord_1940865) baseStart_1940865 baseEnd_1940865 := by
    simpa [prefixWord, tailWord_1940865, baseEnd_1940865] using wordTrace_append hprefix tailTrace_1940865
  have hstable : (prefixWord ++ tailWord_1940865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940865).length < 2 ^ (prefixWord ++ tailWord_1940865).sum := by decide
  have hdescent : baseEnd_1940865 < baseStart_1940865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940961 : List Nat := [1, 2, 3, 1, 2, 5, 1, 3, 5]
def baseStart_1940961 : Nat := 118140960795 + 1940961 * 2 ^ 59
def prefixEnd_1940961 : Nat := 4983230072969 + 3 ^ 40 * 1940961 * 2
def baseEnd_1940961 : Nat := 110738436070165079429021

theorem tailTrace_1940961 : CollatzResearch.WordTrace tailWord_1940961 prefixEnd_1940961 110738436070165079429021 := by
  unfold tailWord_1940961
  simp only [CollatzResearch.WordTrace]
  refine ⟨70792663521237261592662737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47195109014158174395108491 70792663521237261592662737)
  ·
    refine ⟨53094497640927946194497053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70792663521237261592662737 53094497640927946194497053)
    ·
      refine ⟨19910436615347979822936395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53094497640927946194497053 19910436615347979822936395)
      ·
        refine ⟨29865654923021969734404593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19910436615347979822936395 29865654923021969734404593)
        ·
          refine ⟨22399241192266477300803445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29865654923021969734404593 22399241192266477300803445)
          ·
            refine ⟨2099928861774982246950323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22399241192266477300803445 2099928861774982246950323)
            ·
              refine ⟨3149893292662473370425485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099928861774982246950323 3149893292662473370425485)
              ·
                refine ⟨1181209984748427513909557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3149893292662473370425485 1181209984748427513909557)
                ·
                  refine ⟨110738436070165079429021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1181209984748427513909557 110738436070165079429021)
                  ·
                    rfl

theorem cell23_1940961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 5].length) (baseStart_1940961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940961 prefixEnd_1940961 := by exact prefixLift 1940961
  have htrace : WordTrace (prefixWord ++ tailWord_1940961) baseStart_1940961 baseEnd_1940961 := by
    simpa [prefixWord, tailWord_1940961, baseEnd_1940961] using wordTrace_append hprefix tailTrace_1940961
  have hstable : (prefixWord ++ tailWord_1940961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940961).length < 2 ^ (prefixWord ++ tailWord_1940961).sum := by decide
  have hdescent : baseEnd_1940961 < baseStart_1940961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940974 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_1940974 : Nat := 118140960795 + 1940974 * 2 ^ 59
def prefixEnd_1940974 : Nat := 4983230072969 + 3 ^ 40 * 1940974 * 2
def baseEnd_1940974 : Nat := 332217533293331387999543

theorem tailTrace_1940974 : CollatzResearch.WordTrace tailWord_1940974 prefixEnd_1940974 332217533293331387999543 := by
  unfold tailWord_1940974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8849142208773770601610747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47195425113460109875257317 8849142208773770601610747)
  ·
    refine ⟨13273713313160655902416121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8849142208773770601610747 13273713313160655902416121)
    ·
      refine ⟨9955284984870491926812091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13273713313160655902416121 9955284984870491926812091)
      ·
        refine ⟨14932927477305737890218137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9955284984870491926812091 14932927477305737890218137)
        ·
          refine ⟨11199695607979303417663603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14932927477305737890218137 11199695607979303417663603)
          ·
            refine ⟨16799543411968955126495405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11199695607979303417663603 16799543411968955126495405)
            ·
              refine ⟨6299828779488358172435777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16799543411968955126495405 6299828779488358172435777)
              ·
                refine ⟨4724871584616268629326833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6299828779488358172435777 4724871584616268629326833)
                ·
                  refine ⟨3543653688462201471995125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4724871584616268629326833 3543653688462201471995125)
                  ·
                    refine ⟨332217533293331387999543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3543653688462201471995125 332217533293331387999543)
                    ·
                      rfl

theorem cell23_1940974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_1940974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940974 prefixEnd_1940974 := by exact prefixLift 1940974
  have htrace : WordTrace (prefixWord ++ tailWord_1940974) baseStart_1940974 baseEnd_1940974 := by
    simpa [prefixWord, tailWord_1940974, baseEnd_1940974] using wordTrace_append hprefix tailTrace_1940974
  have hstable : (prefixWord ++ tailWord_1940974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940974).length < 2 ^ (prefixWord ++ tailWord_1940974).sum := by decide
  have hdescent : baseEnd_1940974 < baseStart_1940974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1940978 : List Nat := [3, 2, 1, 4, 1, 2, 3, 2, 5]
def baseStart_1940978 : Nat := 118140960795 + 1940978 * 2 ^ 59
def prefixEnd_1940978 : Nat := 4983230072969 + 3 ^ 40 * 1940978 * 2
def baseEnd_1940978 : Nat := 110739405978068016483179

theorem tailTrace_1940978 : CollatzResearch.WordTrace tailWord_1940978 prefixEnd_1940978 110739405978068016483179 := by
  unfold tailWord_1940978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17698320890543918374007897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47195522374783782330687725 17698320890543918374007897)
  ·
    refine ⟨13273740667907938780505923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17698320890543918374007897 13273740667907938780505923)
    ·
      refine ⟨19910611001861908170758885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13273740667907938780505923 19910611001861908170758885)
      ·
        refine ⟨3733239562849107782017291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19910611001861908170758885 3733239562849107782017291)
        ·
          refine ⟨5599859344273661673025937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3733239562849107782017291 5599859344273661673025937)
          ·
            refine ⟨4199894508205246254769453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5599859344273661673025937 4199894508205246254769453)
            ·
              refine ⟨1574960440576967345538545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4199894508205246254769453 1574960440576967345538545)
              ·
                refine ⟨1181220330432725509153909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1574960440576967345538545 1181220330432725509153909)
                ·
                  refine ⟨110739405978068016483179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1181220330432725509153909 110739405978068016483179)
                  ·
                    rfl

theorem cell23_1940978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_1940978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1940978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1940978 prefixEnd_1940978 := by exact prefixLift 1940978
  have htrace : WordTrace (prefixWord ++ tailWord_1940978) baseStart_1940978 baseEnd_1940978 := by
    simpa [prefixWord, tailWord_1940978, baseEnd_1940978] using wordTrace_append hprefix tailTrace_1940978
  have hstable : (prefixWord ++ tailWord_1940978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1940978).length < 2 ^ (prefixWord ++ tailWord_1940978).sum := by decide
  have hdescent : baseEnd_1940978 < baseStart_1940978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1940978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941061 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 3, 1, 3]
def baseStart_1941061 : Nat := 118140960795 + 1941061 * 2 ^ 59
def prefixEnd_1941061 : Nat := 4983230072969 + 3 ^ 40 * 1941061 * 2
def baseEnd_1941061 : Nat := 996697272696935323610729

theorem tailTrace_1941061 : CollatzResearch.WordTrace tailWord_1941061 prefixEnd_1941061 996697272696935323610729 := by
  unfold tailWord_1941061
  simp only [CollatzResearch.WordTrace]
  refine ⟨70796310820874978671303037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47197540547249985780868691 70796310820874978671303037)
  ·
    refine ⟨26548616557828117001738639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70796310820874978671303037 26548616557828117001738639)
    ·
      refine ⟨39822924836742175502607959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26548616557828117001738639 39822924836742175502607959)
      ·
        refine ⟨59734387255113263253911939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39822924836742175502607959 59734387255113263253911939)
        ·
          refine ⟨89601580882669894880867909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59734387255113263253911939 89601580882669894880867909)
          ·
            refine ⟨16800296415500605290162733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89601580882669894880867909 16800296415500605290162733)
            ·
              refine ⟨6300111155812726983811025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16800296415500605290162733 6300111155812726983811025)
              ·
                refine ⟨4725083366859545237858269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6300111155812726983811025 4725083366859545237858269)
                ·
                  refine ⟨1771906262572329464196851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4725083366859545237858269 1771906262572329464196851)
                  ·
                    refine ⟨2657859393858494196295277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1771906262572329464196851 2657859393858494196295277)
                    ·
                      refine ⟨996697272696935323610729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2657859393858494196295277 996697272696935323610729)
                      ·
                        rfl

theorem cell23_1941061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_1941061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941061 prefixEnd_1941061 := by exact prefixLift 1941061
  have htrace : WordTrace (prefixWord ++ tailWord_1941061) baseStart_1941061 baseEnd_1941061 := by
    simpa [prefixWord, tailWord_1941061, baseEnd_1941061] using wordTrace_append hprefix tailTrace_1941061
  have hstable : (prefixWord ++ tailWord_1941061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941061).length < 2 ^ (prefixWord ++ tailWord_1941061).sum := by decide
  have hdescent : baseEnd_1941061 < baseStart_1941061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941062 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_1941062 : Nat := 118140960795 + 1941062 * 2 ^ 59
def prefixEnd_1941062 : Nat := 4983230072969 + 3 ^ 40 * 1941062 * 2
def baseEnd_1941062 : Nat := 996697786177589819698225

theorem tailTrace_1941062 : CollatzResearch.WordTrace tailWord_1941062 prefixEnd_1941062 996697786177589819698225 := by
  unfold tailWord_1941062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212385852933479870065295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47197564862580903894726293 2212385852933479870065295)
  ·
    refine ⟨3318578779400219805097943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2212385852933479870065295 3318578779400219805097943)
    ·
      refine ⟨4977868169100329707646915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3318578779400219805097943 4977868169100329707646915)
      ·
        refine ⟨7466802253650494561470373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977868169100329707646915 7466802253650494561470373)
        ·
          refine ⟨1400025422559467730275695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7466802253650494561470373 1400025422559467730275695)
          ·
            refine ⟨2100038133839201595413543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400025422559467730275695 2100038133839201595413543)
            ·
              refine ⟨3150057200758802393120315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100038133839201595413543 3150057200758802393120315)
              ·
                refine ⟨4725085801138203589680473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150057200758802393120315 4725085801138203589680473)
                ·
                  refine ⟨3543814350853652692260355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4725085801138203589680473 3543814350853652692260355)
                  ·
                    refine ⟨5315721526280479038390533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3543814350853652692260355 5315721526280479038390533)
                    ·
                      refine ⟨996697786177589819698225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5315721526280479038390533 996697786177589819698225)
                      ·
                        rfl

theorem cell23_1941062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_1941062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941062 prefixEnd_1941062 := by exact prefixLift 1941062
  have htrace : WordTrace (prefixWord ++ tailWord_1941062) baseStart_1941062 baseEnd_1941062 := by
    simpa [prefixWord, tailWord_1941062, baseEnd_1941062] using wordTrace_append hprefix tailTrace_1941062
  have hstable : (prefixWord ++ tailWord_1941062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941062).length < 2 ^ (prefixWord ++ tailWord_1941062).sum := by decide
  have hdescent : baseEnd_1941062 < baseStart_1941062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941085 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 6]
def baseStart_1941085 : Nat := 118140960795 + 1941085 * 2 ^ 59
def prefixEnd_1941085 : Nat := 4983230072969 + 3 ^ 40 * 1941085 * 2
def baseEnd_1941085 : Nat := 110745510692515914412291

theorem tailTrace_1941085 : CollatzResearch.WordTrace tailWord_1941085 prefixEnd_1941085 110745510692515914412291 := by
  unfold tailWord_1941085
  simp only [CollatzResearch.WordTrace]
  refine ⟨70797186172788030770176709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47198124115192020513451139 70797186172788030770176709)
  ·
    refine ⟨13274472407397755769408133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70797186172788030770176709 13274472407397755769408133)
    ·
      refine ⟨2488963576387079206764025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13274472407397755769408133 2488963576387079206764025)
      ·
        refine ⟨1866722682290309405073019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2488963576387079206764025 1866722682290309405073019)
        ·
          refine ⟨2800084023435464107609529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1866722682290309405073019 2800084023435464107609529)
          ·
            refine ⟨2100063017576598080707147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2800084023435464107609529 2100063017576598080707147)
            ·
              refine ⟨3150094526364897121060721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100063017576598080707147 3150094526364897121060721)
              ·
                refine ⟨2362570894773672840795541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3150094526364897121060721 2362570894773672840795541)
                ·
                  refine ⟨110745510692515914412291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2362570894773672840795541 110745510692515914412291)
                  ·
                    rfl

theorem cell23_1941085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_1941085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941085 prefixEnd_1941085 := by exact prefixLift 1941085
  have htrace : WordTrace (prefixWord ++ tailWord_1941085) baseStart_1941085 baseEnd_1941085 := by
    simpa [prefixWord, tailWord_1941085, baseEnd_1941085] using wordTrace_append hprefix tailTrace_1941085
  have hstable : (prefixWord ++ tailWord_1941085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941085).length < 2 ^ (prefixWord ++ tailWord_1941085).sum := by decide
  have hdescent : baseEnd_1941085 < baseStart_1941085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941104 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 5]
def baseStart_1941104 : Nat := 118140960795 + 1941104 * 2 ^ 59
def prefixEnd_1941104 : Nat := 4983230072969 + 3 ^ 40 * 1941104 * 2
def baseEnd_1941104 : Nat := 996719352365078655373031

theorem tailTrace_1941104 : CollatzResearch.WordTrace tailWord_1941104 prefixEnd_1941104 996719352365078655373031 := by
  unfold tailWord_1941104
  simp only [CollatzResearch.WordTrace]
  refine ⟨35398939579859598507559183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47198586106479464676745577 35398939579859598507559183)
  ·
    refine ⟨53098409369789397761338775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35398939579859598507559183 53098409369789397761338775)
    ·
      refine ⟨79647614054684096642008163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53098409369789397761338775 79647614054684096642008163)
      ·
        refine ⟨119471421082026144963012245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79647614054684096642008163 119471421082026144963012245)
        ·
          refine ⟨5600222863219975545141199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119471421082026144963012245 5600222863219975545141199)
          ·
            refine ⟨8400334294829963317711799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5600222863219975545141199 8400334294829963317711799)
            ·
              refine ⟨12600501442244944976567699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8400334294829963317711799 12600501442244944976567699)
              ·
                refine ⟨18900752163367417464851549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12600501442244944976567699 18900752163367417464851549)
                ·
                  refine ⟨7087782061262781549319331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18900752163367417464851549 7087782061262781549319331)
                  ·
                    refine ⟨10631673091894172323978997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7087782061262781549319331 10631673091894172323978997)
                    ·
                      refine ⟨996719352365078655373031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10631673091894172323978997 996719352365078655373031)
                      ·
                        rfl

theorem cell23_1941104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_1941104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941104 prefixEnd_1941104 := by exact prefixLift 1941104
  have htrace : WordTrace (prefixWord ++ tailWord_1941104) baseStart_1941104 baseEnd_1941104 := by
    simpa [prefixWord, tailWord_1941104, baseEnd_1941104] using wordTrace_append hprefix tailTrace_1941104
  have hstable : (prefixWord ++ tailWord_1941104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941104).length < 2 ^ (prefixWord ++ tailWord_1941104).sum := by decide
  have hdescent : baseEnd_1941104 < baseStart_1941104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941114 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_1941114 : Nat := 118140960795 + 1941114 * 2 ^ 59
def prefixEnd_1941114 : Nat := 4983230072969 + 3 ^ 40 * 1941114 * 2
def baseEnd_1941114 : Nat := 996724487171623616247985

theorem tailTrace_1941114 : CollatzResearch.WordTrace tailWord_1941114 prefixEnd_1941114 996724487171623616247985 := by
  unfold tailWord_1941114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17699560972420742180745599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47198829259788645815321597 17699560972420742180745599)
  ·
    refine ⟨26549341458631113271118399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17699560972420742180745599 26549341458631113271118399)
    ·
      refine ⟨39824012187946669906677599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26549341458631113271118399 39824012187946669906677599)
      ·
        refine ⟨59736018281920004860016399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39824012187946669906677599 59736018281920004860016399)
        ·
          refine ⟨89604027422880007290024599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59736018281920004860016399 89604027422880007290024599)
          ·
            refine ⟨134406041134320010935036899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89604027422880007290024599 134406041134320010935036899)
            ·
              refine ⟨201609061701480016402555349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134406041134320010935036899 201609061701480016402555349)
              ·
                refine ⟨4725212383628437884434891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 201609061701480016402555349 4725212383628437884434891)
                ·
                  refine ⟨7087818575442656826652337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4725212383628437884434891 7087818575442656826652337)
                  ·
                    refine ⟨5315863931581992619989253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7087818575442656826652337 5315863931581992619989253)
                    ·
                      refine ⟨996724487171623616247985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5315863931581992619989253 996724487171623616247985)
                      ·
                        rfl

theorem cell23_1941114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_1941114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941114 prefixEnd_1941114 := by exact prefixLift 1941114
  have htrace : WordTrace (prefixWord ++ tailWord_1941114) baseStart_1941114 baseEnd_1941114 := by
    simpa [prefixWord, tailWord_1941114, baseEnd_1941114] using wordTrace_append hprefix tailTrace_1941114
  have hstable : (prefixWord ++ tailWord_1941114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941114).length < 2 ^ (prefixWord ++ tailWord_1941114).sum := by decide
  have hdescent : baseEnd_1941114 < baseStart_1941114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941138 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1941138 : Nat := 118140960795 + 1941138 * 2 ^ 59
def prefixEnd_1941138 : Nat := 4983230072969 + 3 ^ 40 * 1941138 * 2
def baseEnd_1941138 : Nat := 996736810707331522347875

theorem tailTrace_1941138 : CollatzResearch.WordTrace tailWord_1941138 prefixEnd_1941138 996736810707331522347875 := by
  unfold tailWord_1941138
  simp only [CollatzResearch.WordTrace]
  refine ⟨17699779810399005205464017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47199412827730680547904045 17699779810399005205464017)
  ·
    refine ⟨13274834857799253904098013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17699779810399005205464017 13274834857799253904098013)
    ·
      refine ⟨4978063071674720214036755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13274834857799253904098013 4978063071674720214036755)
      ·
        refine ⟨7467094607512080321055133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4978063071674720214036755 7467094607512080321055133)
        ·
          refine ⟨2800160477817030120395675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7467094607512080321055133 2800160477817030120395675)
          ·
            refine ⟨4200240716725545180593513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2800160477817030120395675 4200240716725545180593513)
            ·
              refine ⟨3150180537544158885445135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4200240716725545180593513 3150180537544158885445135)
              ·
                refine ⟨4725270806316238328167703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150180537544158885445135 4725270806316238328167703)
                ·
                  refine ⟨7087906209474357492251555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4725270806316238328167703 7087906209474357492251555)
                  ·
                    refine ⟨10631859314211536238377333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7087906209474357492251555 10631859314211536238377333)
                    ·
                      refine ⟨996736810707331522347875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10631859314211536238377333 996736810707331522347875)
                      ·
                        rfl

theorem cell23_1941138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1941138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941138 prefixEnd_1941138 := by exact prefixLift 1941138
  have htrace : WordTrace (prefixWord ++ tailWord_1941138) baseStart_1941138 baseEnd_1941138 := by
    simpa [prefixWord, tailWord_1941138, baseEnd_1941138] using wordTrace_append hprefix tailTrace_1941138
  have hstable : (prefixWord ++ tailWord_1941138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941138).length < 2 ^ (prefixWord ++ tailWord_1941138).sum := by decide
  have hdescent : baseEnd_1941138 < baseStart_1941138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941178 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2]
def baseStart_1941178 : Nat := 118140960795 + 1941178 * 2 ^ 59
def prefixEnd_1941178 : Nat := 4983230072969 + 3 ^ 40 * 1941178 * 2
def baseEnd_1941178 : Nat := 996757349933511365847691

theorem tailTrace_1941178 : CollatzResearch.WordTrace tailWord_1941178 prefixEnd_1941178 996757349933511365847691 := by
  unfold tailWord_1941178
  simp only [CollatzResearch.WordTrace]
  refine ⟨17700144540362776913328047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47200385440967405102208125 17700144540362776913328047)
  ·
    refine ⟨26550216810544165369992071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17700144540362776913328047 26550216810544165369992071)
    ·
      refine ⟨39825325215816248054988107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26550216810544165369992071 39825325215816248054988107)
      ·
        refine ⟨59737987823724372082482161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39825325215816248054988107 59737987823724372082482161)
        ·
          refine ⟨44803490867793279061861621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59737987823724372082482161 44803490867793279061861621)
          ·
            refine ⟨4200327268855619912049527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44803490867793279061861621 4200327268855619912049527)
            ·
              refine ⟨6300490903283429868074291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4200327268855619912049527 6300490903283429868074291)
              ·
                refine ⟨9450736354925144802111437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300490903283429868074291 9450736354925144802111437)
                ·
                  refine ⟨3544026133096929300791789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9450736354925144802111437 3544026133096929300791789)
                  ·
                    refine ⟨1329009799911348487796921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544026133096929300791789 1329009799911348487796921)
                    ·
                      refine ⟨996757349933511365847691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329009799911348487796921 996757349933511365847691)
                      ·
                        rfl

theorem cell23_1941178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2].length) (baseStart_1941178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941178 prefixEnd_1941178 := by exact prefixLift 1941178
  have htrace : WordTrace (prefixWord ++ tailWord_1941178) baseStart_1941178 baseEnd_1941178 := by
    simpa [prefixWord, tailWord_1941178, baseEnd_1941178] using wordTrace_append hprefix tailTrace_1941178
  have hstable : (prefixWord ++ tailWord_1941178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941178).length < 2 ^ (prefixWord ++ tailWord_1941178).sum := by decide
  have hdescent : baseEnd_1941178 < baseStart_1941178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941221 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1941221 : Nat := 118140960795 + 1941221 * 2 ^ 59
def prefixEnd_1941221 : Nat := 4983230072969 + 3 ^ 40 * 1941221 * 2
def baseEnd_1941221 : Nat := 996779429601654697609993

theorem tailTrace_1941221 : CollatzResearch.WordTrace tailWord_1941221 prefixEnd_1941221 996779429601654697609993 := by
  unfold tailWord_1941221
  simp only [CollatzResearch.WordTrace]
  refine ⟨70802146500295325997127517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47201431000196883998085011 70802146500295325997127517)
  ·
    refine ⟨26550804937610747248922819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70802146500295325997127517 26550804937610747248922819)
    ·
      refine ⟨39826207406416120873384229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26550804937610747248922819 39826207406416120873384229)
      ·
        refine ⟨7467413888703022663759543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39826207406416120873384229 7467413888703022663759543)
        ·
          refine ⟨11201120833054533995639315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7467413888703022663759543 11201120833054533995639315)
          ·
            refine ⟨16801681249581800993458973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11201120833054533995639315 16801681249581800993458973)
            ·
              refine ⟨6300630468593175372547115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16801681249581800993458973 6300630468593175372547115)
              ·
                refine ⟨9450945702889763058820673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6300630468593175372547115 9450945702889763058820673)
                ·
                  refine ⟨7088209277167322294115505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9450945702889763058820673 7088209277167322294115505)
                  ·
                    refine ⟨5316156957875491720586629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7088209277167322294115505 5316156957875491720586629)
                    ·
                      refine ⟨996779429601654697609993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5316156957875491720586629 996779429601654697609993)
                      ·
                        rfl

theorem cell23_1941221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1941221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941221 prefixEnd_1941221 := by exact prefixLift 1941221
  have htrace : WordTrace (prefixWord ++ tailWord_1941221) baseStart_1941221 baseEnd_1941221 := by
    simpa [prefixWord, tailWord_1941221, baseEnd_1941221] using wordTrace_append hprefix tailTrace_1941221
  have hstable : (prefixWord ++ tailWord_1941221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941221).length < 2 ^ (prefixWord ++ tailWord_1941221).sum := by decide
  have hdescent : baseEnd_1941221 < baseStart_1941221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941246 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_1941246 : Nat := 118140960795 + 1941246 * 2 ^ 59
def prefixEnd_1941246 : Nat := 4983230072969 + 3 ^ 40 * 1941246 * 2
def baseEnd_1941246 : Nat := 996792266618017099797379

theorem tailTrace_1941246 : CollatzResearch.WordTrace tailWord_1941246 prefixEnd_1941246 996792266618017099797379 := by
  unfold tailWord_1941246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8850382290650594408348449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47202038883469836844525061 8850382290650594408348449)
  ·
    refine ⟨6637786717987945806261337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8850382290650594408348449 6637786717987945806261337)
    ·
      refine ⟨4978340038490959354696003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6637786717987945806261337 4978340038490959354696003)
      ·
        refine ⟨7467510057736439032044005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4978340038490959354696003 7467510057736439032044005)
        ·
          refine ⟨1400158135825582318508251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7467510057736439032044005 1400158135825582318508251)
          ·
            refine ⟨2100237203738373477762377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400158135825582318508251 2100237203738373477762377)
            ·
              refine ⟨1575177902803780108321783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2100237203738373477762377 1575177902803780108321783)
              ·
                refine ⟨2362766854205670162482675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575177902803780108321783 2362766854205670162482675)
                ·
                  refine ⟨3544150281308505243724013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2362766854205670162482675 3544150281308505243724013)
                  ·
                    refine ⟨1329056355490689466396505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544150281308505243724013 1329056355490689466396505)
                    ·
                      refine ⟨996792266618017099797379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329056355490689466396505 996792266618017099797379)
                      ·
                        rfl

theorem cell23_1941246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_1941246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941246 prefixEnd_1941246 := by exact prefixLift 1941246
  have htrace : WordTrace (prefixWord ++ tailWord_1941246) baseStart_1941246 baseEnd_1941246 := by
    simpa [prefixWord, tailWord_1941246, baseEnd_1941246] using wordTrace_append hprefix tailTrace_1941246
  have hstable : (prefixWord ++ tailWord_1941246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941246).length < 2 ^ (prefixWord ++ tailWord_1941246).sum := by decide
  have hdescent : baseEnd_1941246 < baseStart_1941246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941281 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1941281 : Nat := 118140960795 + 1941281 * 2 ^ 59
def prefixEnd_1941281 : Nat := 4983230072969 + 3 ^ 40 * 1941281 * 2
def baseEnd_1941281 : Nat := 996810238440924462859717

theorem tailTrace_1941281 : CollatzResearch.WordTrace tailWord_1941281 prefixEnd_1941281 996810238440924462859717 := by
  unfold tailWord_1941281
  simp only [CollatzResearch.WordTrace]
  refine ⟨70804334880077956244311697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47202889920051970829541131 70804334880077956244311697)
  ·
    refine ⟨53103251160058467183233773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70804334880077956244311697 53103251160058467183233773)
    ·
      refine ⟨19913719185021925193712665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53103251160058467183233773 19913719185021925193712665)
      ·
        refine ⟨14935289388766443895284499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19913719185021925193712665 14935289388766443895284499)
        ·
          refine ⟨22402934083149665842926749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14935289388766443895284499 22402934083149665842926749)
          ·
            refine ⟨8401100281181124691097531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22402934083149665842926749 8401100281181124691097531)
            ·
              refine ⟨12601650421771687036646297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8401100281181124691097531 12601650421771687036646297)
              ·
                refine ⟨9451237816328765277484723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12601650421771687036646297 9451237816328765277484723)
                ·
                  refine ⟨14176856724493147916227085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9451237816328765277484723 14176856724493147916227085)
                  ·
                    refine ⟨5316321271684930468585157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14176856724493147916227085 5316321271684930468585157)
                    ·
                      refine ⟨996810238440924462859717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5316321271684930468585157 996810238440924462859717)
                      ·
                        rfl

theorem cell23_1941281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1941281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941281 prefixEnd_1941281 := by exact prefixLift 1941281
  have htrace : WordTrace (prefixWord ++ tailWord_1941281) baseStart_1941281 baseEnd_1941281 := by
    simpa [prefixWord, tailWord_1941281, baseEnd_1941281] using wordTrace_append hprefix tailTrace_1941281
  have hstable : (prefixWord ++ tailWord_1941281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941281).length < 2 ^ (prefixWord ++ tailWord_1941281).sum := by decide
  have hdescent : baseEnd_1941281 < baseStart_1941281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941321 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 6]
def baseStart_1941321 : Nat := 118140960795 + 1941321 * 2 ^ 59
def prefixEnd_1941321 : Nat := 4983230072969 + 3 ^ 40 * 1941321 * 2
def baseEnd_1941321 : Nat := 110758975296344922928837

theorem tailTrace_1941321 : CollatzResearch.WordTrace tailWord_1941321 prefixEnd_1941321 110758975296344922928837 := by
  unfold tailWord_1941321
  simp only [CollatzResearch.WordTrace]
  refine ⟨70805793799933043075767817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47203862533288695383845211 70805793799933043075767817)
  ·
    refine ⟨53104345349949782306825863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70805793799933043075767817 53104345349949782306825863)
    ·
      refine ⟨79656518024924673460238795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53104345349949782306825863 79656518024924673460238795)
      ·
        refine ⟨119484777037387010190358193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79656518024924673460238795 119484777037387010190358193)
        ·
          refine ⟨89613582778040257642768645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119484777037387010190358193 89613582778040257642768645)
          ·
            refine ⟨16802546770882548308019121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89613582778040257642768645 16802546770882548308019121)
            ·
              refine ⟨12601910078161911231014341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16802546770882548308019121 12601910078161911231014341)
              ·
                refine ⟨2362858139655358355815189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12601910078161911231014341 2362858139655358355815189)
                ·
                  refine ⟨110758975296344922928837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2362858139655358355815189 110758975296344922928837)
                  ·
                    rfl

theorem cell23_1941321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 6].length) (baseStart_1941321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941321 prefixEnd_1941321 := by exact prefixLift 1941321
  have htrace : WordTrace (prefixWord ++ tailWord_1941321) baseStart_1941321 baseEnd_1941321 := by
    simpa [prefixWord, tailWord_1941321, baseEnd_1941321] using wordTrace_append hprefix tailTrace_1941321
  have hstable : (prefixWord ++ tailWord_1941321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941321).length < 2 ^ (prefixWord ++ tailWord_1941321).sum := by decide
  have hdescent : baseEnd_1941321 < baseStart_1941321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941381 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_1941381 : Nat := 118140960795 + 1941381 * 2 ^ 59
def prefixEnd_1941381 : Nat := 4983230072969 + 3 ^ 40 * 1941381 * 2
def baseEnd_1941381 : Nat := 332287195502124690536419

theorem tailTrace_1941381 : CollatzResearch.WordTrace tailWord_1941381 prefixEnd_1941381 332287195502124690536419 := by
  unfold tailWord_1941381
  simp only [CollatzResearch.WordTrace]
  refine ⟨70807982179715673322951997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47205321453143782215301331 70807982179715673322951997)
  ·
    refine ⟨26552993317393377496106999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70807982179715673322951997 26552993317393377496106999)
    ·
      refine ⟨39829489976090066244160499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26552993317393377496106999 39829489976090066244160499)
      ·
        refine ⟨59744234964135099366240749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39829489976090066244160499 59744234964135099366240749)
        ·
          refine ⟨22404088111550662262340281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59744234964135099366240749 22404088111550662262340281)
          ·
            refine ⟨16803066083662996696755211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22404088111550662262340281 16803066083662996696755211)
            ·
              refine ⟨25204599125494495045132817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16803066083662996696755211 25204599125494495045132817)
              ·
                refine ⟨18903449344120871283849613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25204599125494495045132817 18903449344120871283849613)
                ·
                  refine ⟨7088793504045326731443605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18903449344120871283849613 7088793504045326731443605)
                  ·
                    refine ⟨332287195502124690536419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7088793504045326731443605 332287195502124690536419)
                    ·
                      rfl

theorem cell23_1941381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_1941381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941381 prefixEnd_1941381 := by exact prefixLift 1941381
  have htrace : WordTrace (prefixWord ++ tailWord_1941381) baseStart_1941381 baseEnd_1941381 := by
    simpa [prefixWord, tailWord_1941381, baseEnd_1941381] using wordTrace_append hprefix tailTrace_1941381
  have hstable : (prefixWord ++ tailWord_1941381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941381).length < 2 ^ (prefixWord ++ tailWord_1941381).sum := by decide
  have hdescent : baseEnd_1941381 < baseStart_1941381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941388 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 2, 6, 2]
def baseStart_1941388 : Nat := 118140960795 + 1941388 * 2 ^ 59
def prefixEnd_1941388 : Nat := 4983230072969 + 3 ^ 40 * 1941388 * 2
def baseEnd_1941388 : Nat := 996865180870955544221725

theorem tailTrace_1941388 : CollatzResearch.WordTrace tailWord_1941388 prefixEnd_1941388 996865180870955544221725 := by
  unfold tailWord_1941388
  simp only [CollatzResearch.WordTrace]
  refine ⟨35404118745345156759228409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47205491660460209012304545 35404118745345156759228409)
  ·
    refine ⟨26553089059008867569421307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35404118745345156759228409 26553089059008867569421307)
    ·
      refine ⟨39829633588513301354131961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26553089059008867569421307 39829633588513301354131961)
      ·
        refine ⟨29872225191384976015598971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39829633588513301354131961 29872225191384976015598971)
        ·
          refine ⟨44808337787077464023398457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29872225191384976015598971 44808337787077464023398457)
          ·
            refine ⟨33606253340308098017548843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44808337787077464023398457 33606253340308098017548843)
            ·
              refine ⟨50409380010462147026323265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33606253340308098017548843 50409380010462147026323265)
              ·
                refine ⟨37807035007846610269742449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50409380010462147026323265 37807035007846610269742449)
                ·
                  refine ⟨28355276255884957702306837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37807035007846610269742449 28355276255884957702306837)
                  ·
                    refine ⟨1329153574494607392295633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28355276255884957702306837 1329153574494607392295633)
                    ·
                      refine ⟨996865180870955544221725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329153574494607392295633 996865180870955544221725)
                      ·
                        rfl

theorem cell23_1941388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_1941388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941388 prefixEnd_1941388 := by exact prefixLift 1941388
  have htrace : WordTrace (prefixWord ++ tailWord_1941388) baseStart_1941388 baseEnd_1941388 := by
    simpa [prefixWord, tailWord_1941388, baseEnd_1941388] using wordTrace_append hprefix tailTrace_1941388
  have hstable : (prefixWord ++ tailWord_1941388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941388).length < 2 ^ (prefixWord ++ tailWord_1941388).sum := by decide
  have hdescent : baseEnd_1941388 < baseStart_1941388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941401 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 6]
def baseStart_1941401 : Nat := 118140960795 + 1941401 * 2 ^ 59
def prefixEnd_1941401 : Nat := 4983230072969 + 3 ^ 40 * 1941401 * 2
def baseEnd_1941401 : Nat := 996871856119463993359165

theorem tailTrace_1941401 : CollatzResearch.WordTrace tailWord_1941401 prefixEnd_1941401 996871856119463993359165 := by
  unfold tailWord_1941401
  simp only [CollatzResearch.WordTrace]
  refine ⟨70808711639643216738680057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47205807759762144492453371 70808711639643216738680057)
  ·
    refine ⟨53106533729732412554010043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70808711639643216738680057 53106533729732412554010043)
    ·
      refine ⟨79659800594598618831015065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53106533729732412554010043 79659800594598618831015065)
      ·
        refine ⟨59744850445948964123261299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79659800594598618831015065 59744850445948964123261299)
        ·
          refine ⟨89617275668923446184891949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59744850445948964123261299 89617275668923446184891949)
          ·
            refine ⟨33606478375846292319334481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89617275668923446184891949 33606478375846292319334481)
            ·
              refine ⟨25204858781884719239500861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33606478375846292319334481 25204858781884719239500861)
              ·
                refine ⟨9451822043206769714812823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25204858781884719239500861 9451822043206769714812823)
                ·
                  refine ⟨14177733064810154572219235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9451822043206769714812823 14177733064810154572219235)
                  ·
                    refine ⟨21266599597215231858328853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14177733064810154572219235 21266599597215231858328853)
                    ·
                      refine ⟨996871856119463993359165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21266599597215231858328853 996871856119463993359165)
                      ·
                        rfl

theorem cell23_1941401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_1941401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941401 prefixEnd_1941401 := by exact prefixLift 1941401
  have htrace : WordTrace (prefixWord ++ tailWord_1941401) baseStart_1941401 baseEnd_1941401 := by
    simpa [prefixWord, tailWord_1941401, baseEnd_1941401] using wordTrace_append hprefix tailTrace_1941401
  have hstable : (prefixWord ++ tailWord_1941401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941401).length < 2 ^ (prefixWord ++ tailWord_1941401).sum := by decide
  have hdescent : baseEnd_1941401 < baseStart_1941401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941409 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1941409 : Nat := 118140960795 + 1941409 * 2 ^ 59
def prefixEnd_1941409 : Nat := 4983230072969 + 3 ^ 40 * 1941409 * 2
def baseEnd_1941409 : Nat := 996875963964699962059129

theorem tailTrace_1941409 : CollatzResearch.WordTrace tailWord_1941409 prefixEnd_1941409 996875963964699962059129 := by
  unfold tailWord_1941409
  simp only [CollatzResearch.WordTrace]
  refine ⟨70809003423614234104971281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47206002282409489403314187 70809003423614234104971281)
  ·
    refine ⟨53106752567710675578728461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70809003423614234104971281 53106752567710675578728461)
    ·
      refine ⟨19915032212891503342023173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53106752567710675578728461 19915032212891503342023173)
      ·
        refine ⟨3734068539917156876629345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19915032212891503342023173 3734068539917156876629345)
        ·
          refine ⟨2800551404937867657472009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3734068539917156876629345 2800551404937867657472009)
          ·
            refine ⟨2100413553703400743104007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2800551404937867657472009 2100413553703400743104007)
            ·
              refine ⟨3150620330555101114656011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100413553703400743104007 3150620330555101114656011)
              ·
                refine ⟨4725930495832651671984017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150620330555101114656011 4725930495832651671984017)
                ·
                  refine ⟨3544447871874488753988013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4725930495832651671984017 3544447871874488753988013)
                  ·
                    refine ⟨1329167951952933282745505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544447871874488753988013 1329167951952933282745505)
                    ·
                      refine ⟨996875963964699962059129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329167951952933282745505 996875963964699962059129)
                      ·
                        rfl

theorem cell23_1941409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1941409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941409 prefixEnd_1941409 := by exact prefixLift 1941409
  have htrace : WordTrace (prefixWord ++ tailWord_1941409) baseStart_1941409 baseEnd_1941409 := by
    simpa [prefixWord, tailWord_1941409, baseEnd_1941409] using wordTrace_append hprefix tailTrace_1941409
  have hstable : (prefixWord ++ tailWord_1941409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941409).length < 2 ^ (prefixWord ++ tailWord_1941409).sum := by decide
  have hdescent : baseEnd_1941409 < baseStart_1941409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941431 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_1941431 : Nat := 118140960795 + 1941431 * 2 ^ 59
def prefixEnd_1941431 : Nat := 4983230072969 + 3 ^ 40 * 1941431 * 2
def baseEnd_1941431 : Nat := 996887260539098875984027

theorem tailTrace_1941431 : CollatzResearch.WordTrace tailWord_1941431 prefixEnd_1941431 996887260539098875984027 := by
  unfold tailWord_1941431
  simp only [CollatzResearch.WordTrace]
  refine ⟨70809805829534531862272147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47206537219689687908181431 70809805829534531862272147)
  ·
    refine ⟨106214708744301797793408221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70809805829534531862272147 106214708744301797793408221)
    ·
      refine ⟨39830515779113174172528083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106214708744301797793408221 39830515779113174172528083)
      ·
        refine ⟨59745773668669761258792125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39830515779113174172528083 59745773668669761258792125)
        ·
          refine ⟨22404665125751160472047047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59745773668669761258792125 22404665125751160472047047)
          ·
            refine ⟨33606997688626740708070571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22404665125751160472047047 33606997688626740708070571)
            ·
              refine ⟨50410496532940111062105857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33606997688626740708070571 50410496532940111062105857)
              ·
                refine ⟨37807872399705083296579393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50410496532940111062105857 37807872399705083296579393)
                ·
                  refine ⟨28355904299778812472434545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37807872399705083296579393 28355904299778812472434545)
                  ·
                    refine ⟨21266928224834109354325909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28355904299778812472434545 21266928224834109354325909)
                    ·
                      refine ⟨996887260539098875984027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21266928224834109354325909 996887260539098875984027)
                      ·
                        rfl

theorem cell23_1941431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_1941431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941431 prefixEnd_1941431 := by exact prefixLift 1941431
  have htrace : WordTrace (prefixWord ++ tailWord_1941431) baseStart_1941431 baseEnd_1941431 := by
    simpa [prefixWord, tailWord_1941431, baseEnd_1941431] using wordTrace_append hprefix tailTrace_1941431
  have hstable : (prefixWord ++ tailWord_1941431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941431).length < 2 ^ (prefixWord ++ tailWord_1941431).sum := by decide
  have hdescent : baseEnd_1941431 < baseStart_1941431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941482 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_1941482 : Nat := 118140960795 + 1941482 * 2 ^ 59
def prefixEnd_1941482 : Nat := 4983230072969 + 3 ^ 40 * 1941482 * 2
def baseEnd_1941482 : Nat := 996913448052478176446293

theorem tailTrace_1941482 : CollatzResearch.WordTrace tailWord_1941482 prefixEnd_1941482 996913448052478176446293 := by
  unfold tailWord_1941482
  simp only [CollatzResearch.WordTrace]
  refine ⟨17702916488087441893094675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47207777301566511714919133 17702916488087441893094675)
  ·
    refine ⟨26554374732131162839642013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17702916488087441893094675 26554374732131162839642013)
    ·
      refine ⟨9957890524549186064865755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26554374732131162839642013 9957890524549186064865755)
      ·
        refine ⟨14936835786823779097298633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9957890524549186064865755 14936835786823779097298633)
        ·
          refine ⟨11202626840117834322973975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14936835786823779097298633 11202626840117834322973975)
          ·
            refine ⟨16803940260176751484460963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11202626840117834322973975 16803940260176751484460963)
            ·
              refine ⟨25205910390265127226691445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16803940260176751484460963 25205910390265127226691445)
              ·
                refine ⟨2363054099087355677502323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25205910390265127226691445 2363054099087355677502323)
                ·
                  refine ⟨3544581148631033516253485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363054099087355677502323 3544581148631033516253485)
                  ·
                    refine ⟨1329217930736637568595057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3544581148631033516253485 1329217930736637568595057)
                    ·
                      refine ⟨996913448052478176446293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329217930736637568595057 996913448052478176446293)
                      ·
                        rfl

theorem cell23_1941482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_1941482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941482 prefixEnd_1941482 := by exact prefixLift 1941482
  have htrace : WordTrace (prefixWord ++ tailWord_1941482) baseStart_1941482 baseEnd_1941482 := by
    simpa [prefixWord, tailWord_1941482, baseEnd_1941482] using wordTrace_append hprefix tailTrace_1941482
  have hstable : (prefixWord ++ tailWord_1941482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941482).length < 2 ^ (prefixWord ++ tailWord_1941482).sum := by decide
  have hdescent : baseEnd_1941482 < baseStart_1941482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941510 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1941510 : Nat := 118140960795 + 1941510 * 2 ^ 59
def prefixEnd_1941510 : Nat := 4983230072969 + 3 ^ 40 * 1941510 * 2
def baseEnd_1941510 : Nat := 996927825510804066896165

theorem tailTrace_1941510 : CollatzResearch.WordTrace tailWord_1941510 prefixEnd_1941510 996927825510804066896165 := by
  unfold tailWord_1941510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212896474882760261074937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47208458130832218902931989 2212896474882760261074937)
  ·
    refine ⟨1659672356162070195806203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2212896474882760261074937 1659672356162070195806203)
    ·
      refine ⟨2489508534243105293709305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659672356162070195806203 2489508534243105293709305)
      ·
        refine ⟨1867131400682328970281979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2489508534243105293709305 1867131400682328970281979)
        ·
          refine ⟨2800697101023493455422969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867131400682328970281979 2800697101023493455422969)
          ·
            refine ⟨2100522825767620091567227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2800697101023493455422969 2100522825767620091567227)
            ·
              refine ⟨3150784238651430137350841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100522825767620091567227 3150784238651430137350841)
              ·
                refine ⟨2363088178988572603013131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3150784238651430137350841 2363088178988572603013131)
                ·
                  refine ⟨3544632268482858904519697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2363088178988572603013131 3544632268482858904519697)
                  ·
                    refine ⟨2658474201362144178389773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3544632268482858904519697 2658474201362144178389773)
                    ·
                      refine ⟨996927825510804066896165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2658474201362144178389773 996927825510804066896165)
                      ·
                        rfl

theorem cell23_1941510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1941510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941510 prefixEnd_1941510 := by exact prefixLift 1941510
  have htrace : WordTrace (prefixWord ++ tailWord_1941510) baseStart_1941510 baseEnd_1941510 := by
    simpa [prefixWord, tailWord_1941510, baseEnd_1941510] using wordTrace_append hprefix tailTrace_1941510
  have hstable : (prefixWord ++ tailWord_1941510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941510).length < 2 ^ (prefixWord ++ tailWord_1941510).sum := by decide
  have hdescent : baseEnd_1941510 < baseStart_1941510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941518 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_1941518 : Nat := 118140960795 + 1941518 * 2 ^ 59
def prefixEnd_1941518 : Nat := 4983230072969 + 3 ^ 40 * 1941518 * 2
def baseEnd_1941518 : Nat := 110770214817337781732903

theorem tailTrace_1941518 : CollatzResearch.WordTrace tailWord_1941518 prefixEnd_1941518 110770214817337781732903 := by
  unfold tailWord_1941518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8851622372527418215086151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47208652653479563813792805 8851622372527418215086151)
  ·
    refine ⟨13277433558791127322629227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8851622372527418215086151 13277433558791127322629227)
    ·
      refine ⟨19916150338186690983943841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13277433558791127322629227 19916150338186690983943841)
      ·
        refine ⟨14937112753640018237957881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19916150338186690983943841 14937112753640018237957881)
        ·
          refine ⟨11202834565230013678468411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14937112753640018237957881 11202834565230013678468411)
          ·
            refine ⟨16804251847845020517702617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11202834565230013678468411 16804251847845020517702617)
            ·
              refine ⟨12603188885883765388276963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16804251847845020517702617 12603188885883765388276963)
              ·
                refine ⟨18904783328825648082415445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12603188885883765388276963 18904783328825648082415445)
                ·
                  refine ⟨110770214817337781732903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18904783328825648082415445 110770214817337781732903)
                  ·
                    rfl

theorem cell23_1941518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_1941518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941518 prefixEnd_1941518 := by exact prefixLift 1941518
  have htrace : WordTrace (prefixWord ++ tailWord_1941518) baseStart_1941518 baseEnd_1941518 := by
    simpa [prefixWord, tailWord_1941518, baseEnd_1941518] using wordTrace_append hprefix tailTrace_1941518
  have hstable : (prefixWord ++ tailWord_1941518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941518).length < 2 ^ (prefixWord ++ tailWord_1941518).sum := by decide
  have hdescent : baseEnd_1941518 < baseStart_1941518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941535 : List Nat := [1, 1, 2, 4, 1, 2, 2, 5, 5]
def baseStart_1941535 : Nat := 118140960795 + 1941535 * 2 ^ 59
def prefixEnd_1941535 : Nat := 4983230072969 + 3 ^ 40 * 1941535 * 2
def baseEnd_1941535 : Nat := 110771184725240718787061

theorem tailTrace_1941535 : CollatzResearch.WordTrace tailWord_1941535 prefixEnd_1941535 110771184725240718787061 := by
  unfold tailWord_1941535
  simp only [CollatzResearch.WordTrace]
  refine ⟨70813599021157757624058059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47209066014105171749372039 70813599021157757624058059)
  ·
    refine ⟨106220398531736636436087089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70813599021157757624058059 106220398531736636436087089)
    ·
      refine ⟨79665298898802477327065317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106220398531736636436087089 79665298898802477327065317)
      ·
        refine ⟨14937243543525464498824747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79665298898802477327065317 14937243543525464498824747)
        ·
          refine ⟨22405865315288196748237121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14937243543525464498824747 22405865315288196748237121)
          ·
            refine ⟨16804398986466147561177841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22405865315288196748237121 16804398986466147561177841)
            ·
              refine ⟨12603299239849610670883381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16804398986466147561177841 12603299239849610670883381)
              ·
                refine ⟨1181559303735901000395317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12603299239849610670883381 1181559303735901000395317)
                ·
                  refine ⟨110771184725240718787061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1181559303735901000395317 110771184725240718787061)
                  ·
                    rfl

theorem cell23_1941535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 5].length) (baseStart_1941535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941535 prefixEnd_1941535 := by exact prefixLift 1941535
  have htrace : WordTrace (prefixWord ++ tailWord_1941535) baseStart_1941535 baseEnd_1941535 := by
    simpa [prefixWord, tailWord_1941535, baseEnd_1941535] using wordTrace_append hprefix tailTrace_1941535
  have hstable : (prefixWord ++ tailWord_1941535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941535).length < 2 ^ (prefixWord ++ tailWord_1941535).sum := by decide
  have hdescent : baseEnd_1941535 < baseStart_1941535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941546 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_1941546 : Nat := 118140960795 + 1941546 * 2 ^ 59
def prefixEnd_1941546 : Nat := 4983230072969 + 3 ^ 40 * 1941546 * 2
def baseEnd_1941546 : Nat := 996946310814365926045999

theorem tailTrace_1941546 : CollatzResearch.WordTrace tailWord_1941546 prefixEnd_1941546 996946310814365926045999 := by
  unfold tailWord_1941546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17703500056029476625677123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47209333482745271001805661 17703500056029476625677123)
  ·
    refine ⟨26555250084044214938515685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17703500056029476625677123 26555250084044214938515685)
    ·
      refine ⟨4979109390758290300971691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26555250084044214938515685 4979109390758290300971691)
      ·
        refine ⟨7468664086137435451457537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4979109390758290300971691 7468664086137435451457537)
        ·
          refine ⟨5601498064603076588593153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7468664086137435451457537 5601498064603076588593153)
          ·
            refine ⟨4201123548452307441444865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5601498064603076588593153 4201123548452307441444865)
            ·
              refine ⟨3150842661339230581083649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4201123548452307441444865 3150842661339230581083649)
              ·
                refine ⟨2363131996004422935812737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3150842661339230581083649 2363131996004422935812737)
                ·
                  refine ⟨1772348997003317201859553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363131996004422935812737 1772348997003317201859553)
                  ·
                    refine ⟨1329261747752487901394665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1772348997003317201859553 1329261747752487901394665)
                    ·
                      refine ⟨996946310814365926045999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329261747752487901394665 996946310814365926045999)
                      ·
                        rfl

theorem cell23_1941546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_1941546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941546 prefixEnd_1941546 := by exact prefixLift 1941546
  have htrace : WordTrace (prefixWord ++ tailWord_1941546) baseStart_1941546 baseEnd_1941546 := by
    simpa [prefixWord, tailWord_1941546, baseEnd_1941546] using wordTrace_append hprefix tailTrace_1941546
  have hstable : (prefixWord ++ tailWord_1941546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941546).length < 2 ^ (prefixWord ++ tailWord_1941546).sum := by decide
  have hdescent : baseEnd_1941546 < baseStart_1941546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941548 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_1941548 : Nat := 118140960795 + 1941548 * 2 ^ 59
def prefixEnd_1941548 : Nat := 4983230072969 + 3 ^ 40 * 1941548 * 2
def baseEnd_1941548 : Nat := 332315779258558306073663

theorem tailTrace_1941548 : CollatzResearch.WordTrace tailWord_1941548 prefixEnd_1941548 332315779258558306073663 := by
  unfold tailWord_1941548
  simp only [CollatzResearch.WordTrace]
  refine ⟨35407036585055330422140649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47209382113407107229520865 35407036585055330422140649)
  ·
    refine ⟨26555277438791497816605487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35407036585055330422140649 26555277438791497816605487)
    ·
      refine ⟨39832916158187246724908231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26555277438791497816605487 39832916158187246724908231)
      ·
        refine ⟨59749374237280870087362347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39832916158187246724908231 59749374237280870087362347)
        ·
          refine ⟨89624061355921305131043521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59749374237280870087362347 89624061355921305131043521)
          ·
            refine ⟨67218046016940978848282641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89624061355921305131043521 67218046016940978848282641)
            ·
              refine ⟨50413534512705734136211981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67218046016940978848282641 50413534512705734136211981)
              ·
                refine ⟨18905075442264650301079493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50413534512705734136211981 18905075442264650301079493)
                ·
                  refine ⟨3544701645424621931452405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18905075442264650301079493 3544701645424621931452405)
                  ·
                    refine ⟨332315779258558306073663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3544701645424621931452405 332315779258558306073663)
                    ·
                      rfl

theorem cell23_1941548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_1941548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941548 prefixEnd_1941548 := by exact prefixLift 1941548
  have htrace : WordTrace (prefixWord ++ tailWord_1941548) baseStart_1941548 baseEnd_1941548 := by
    simpa [prefixWord, tailWord_1941548, baseEnd_1941548] using wordTrace_append hprefix tailTrace_1941548
  have hstable : (prefixWord ++ tailWord_1941548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941548).length < 2 ^ (prefixWord ++ tailWord_1941548).sum := by decide
  have hdescent : baseEnd_1941548 < baseStart_1941548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941552 : List Nat := [2, 1, 1, 1, 2, 5, 4, 2, 5]
def baseStart_1941552 : Nat := 118140960795 + 1941552 * 2 ^ 59
def prefixEnd_1941552 : Nat := 4983230072969 + 3 ^ 40 * 1941552 * 2
def baseEnd_1941552 : Nat := 110772154633143655841219

theorem tailTrace_1941552 : CollatzResearch.WordTrace tailWord_1941552 prefixEnd_1941552 110772154633143655841219 := by
  unfold tailWord_1941552
  simp only [CollatzResearch.WordTrace]
  refine ⟨35407109531048084763713455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47209479374730779684951273 35407109531048084763713455)
  ·
    refine ⟨53110664296572127145570183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35407109531048084763713455 53110664296572127145570183)
    ·
      refine ⟨79665996444858190718355275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53110664296572127145570183 79665996444858190718355275)
      ·
        refine ⟨119498994667287286077532913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79665996444858190718355275 119498994667287286077532913)
        ·
          refine ⟨89624246000465464558149685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119498994667287286077532913 89624246000465464558149685)
          ·
            refine ⟨8402273062543637302326533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89624246000465464558149685 8402273062543637302326533)
            ·
              refine ⟨1575426199226931994186225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8402273062543637302326533 1575426199226931994186225)
              ·
                refine ⟨1181569649420198995639669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1575426199226931994186225 1181569649420198995639669)
                ·
                  refine ⟨110772154633143655841219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1181569649420198995639669 110772154633143655841219)
                  ·
                    rfl

theorem cell23_1941552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 5].length) (baseStart_1941552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941552 prefixEnd_1941552 := by exact prefixLift 1941552
  have htrace : WordTrace (prefixWord ++ tailWord_1941552) baseStart_1941552 baseEnd_1941552 := by
    simpa [prefixWord, tailWord_1941552, baseEnd_1941552] using wordTrace_append hprefix tailTrace_1941552
  have hstable : (prefixWord ++ tailWord_1941552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941552).length < 2 ^ (prefixWord ++ tailWord_1941552).sum := by decide
  have hdescent : baseEnd_1941552 < baseStart_1941552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941555 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 2, 5, 2]
def baseStart_1941555 : Nat := 118140960795 + 1941555 * 2 ^ 59
def prefixEnd_1941555 : Nat := 4983230072969 + 3 ^ 40 * 1941555 * 2
def baseEnd_1941555 : Nat := 996950932140256390833457

theorem tailTrace_1941555 : CollatzResearch.WordTrace tailWord_1941555 prefixEnd_1941555 996950932140256390833457 := by
  unfold tailWord_1941555
  simp only [CollatzResearch.WordTrace]
  refine ⟨70814328481085301039786119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47209552320723534026524079 70814328481085301039786119)
  ·
    refine ⟨106221492721627951559679179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70814328481085301039786119 106221492721627951559679179)
    ·
      refine ⟨159332239082441927339518769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106221492721627951559679179 159332239082441927339518769)
      ·
        refine ⟨119499179311831445504639077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159332239082441927339518769 119499179311831445504639077)
        ·
          refine ⟨22406096120968396032119827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119499179311831445504639077 22406096120968396032119827)
          ·
            refine ⟨33609144181452594048179741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22406096120968396032119827 33609144181452594048179741)
            ·
              refine ⟨12603429068044722768067403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33609144181452594048179741 12603429068044722768067403)
              ·
                refine ⟨18905143602067084152101105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12603429068044722768067403 18905143602067084152101105)
                ·
                  refine ⟨14178857701550313114075829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18905143602067084152101105 14178857701550313114075829)
                  ·
                    refine ⟨1329267909520341854444609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14178857701550313114075829 1329267909520341854444609)
                    ·
                      refine ⟨996950932140256390833457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329267909520341854444609 996950932140256390833457)
                      ·
                        rfl

theorem cell23_1941555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 5, 2].length) (baseStart_1941555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941555 prefixEnd_1941555 := by exact prefixLift 1941555
  have htrace : WordTrace (prefixWord ++ tailWord_1941555) baseStart_1941555 baseEnd_1941555 := by
    simpa [prefixWord, tailWord_1941555, baseEnd_1941555] using wordTrace_append hprefix tailTrace_1941555
  have hstable : (prefixWord ++ tailWord_1941555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941555).length < 2 ^ (prefixWord ++ tailWord_1941555).sum := by decide
  have hdescent : baseEnd_1941555 < baseStart_1941555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941582 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_1941582 : Nat := 118140960795 + 1941582 * 2 ^ 59
def prefixEnd_1941582 : Nat := 4983230072969 + 3 ^ 40 * 1941582 * 2
def baseEnd_1941582 : Nat := 332321598705975928398611

theorem tailTrace_1941582 : CollatzResearch.WordTrace tailWord_1941582 prefixEnd_1941582 332321598705975928398611 := by
  unfold tailWord_1941582
  simp only [CollatzResearch.WordTrace]
  refine ⟨8851914156498435581377375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47210208834658323100679333 8851914156498435581377375)
  ·
    refine ⟨13277871234747653372066063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8851914156498435581377375 13277871234747653372066063)
    ·
      refine ⟨19916806852121480058099095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13277871234747653372066063 19916806852121480058099095)
      ·
        refine ⟨29875210278182220087148643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19916806852121480058099095 29875210278182220087148643)
        ·
          refine ⟨44812815417273330130722965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29875210278182220087148643 44812815417273330130722965)
          ·
            refine ⟨2100600722684687349877639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44812815417273330130722965 2100600722684687349877639)
            ·
              refine ⟨3150901084027031024816459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2100600722684687349877639 3150901084027031024816459)
              ·
                refine ⟨4726351626040546537224689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150901084027031024816459 4726351626040546537224689)
                ·
                  refine ⟨3544763719530409902918517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4726351626040546537224689 3544763719530409902918517)
                  ·
                    refine ⟨332321598705975928398611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3544763719530409902918517 332321598705975928398611)
                    ·
                      rfl

theorem cell23_1941582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_1941582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941582 prefixEnd_1941582 := by exact prefixLift 1941582
  have htrace : WordTrace (prefixWord ++ tailWord_1941582) baseStart_1941582 baseEnd_1941582 := by
    simpa [prefixWord, tailWord_1941582, baseEnd_1941582] using wordTrace_append hprefix tailTrace_1941582
  have hstable : (prefixWord ++ tailWord_1941582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941582).length < 2 ^ (prefixWord ++ tailWord_1941582).sum := by decide
  have hdescent : baseEnd_1941582 < baseStart_1941582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941585 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 3, 6, 2]
def baseStart_1941585 : Nat := 118140960795 + 1941585 * 2 ^ 59
def prefixEnd_1941585 : Nat := 4983230072969 + 3 ^ 40 * 1941585 * 2
def baseEnd_1941585 : Nat := 996966336559891273458319

theorem tailTrace_1941585 : CollatzResearch.WordTrace tailWord_1941585 prefixEnd_1941585 996966336559891273458319 := by
  unfold tailWord_1941585
  simp only [CollatzResearch.WordTrace]
  refine ⟨70815422670976616163378209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47210281780651077442252139 70815422670976616163378209)
  ·
    refine ⟨53111567003232462122533657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70815422670976616163378209 53111567003232462122533657)
    ·
      refine ⟨39833675252424346591900243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53111567003232462122533657 39833675252424346591900243)
      ·
        refine ⟨59750512878636519887850365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39833675252424346591900243 59750512878636519887850365)
        ·
          refine ⟨22406442329488694957943887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59750512878636519887850365 22406442329488694957943887)
          ·
            refine ⟨33609663494233042436915831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22406442329488694957943887 33609663494233042436915831)
            ·
              refine ⟨50414495241349563655373747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33609663494233042436915831 50414495241349563655373747)
              ·
                refine ⟨75621742862024345483060621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50414495241349563655373747 75621742862024345483060621)
                ·
                  refine ⟨28358153573259129556147733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75621742862024345483060621 28358153573259129556147733)
                  ·
                    refine ⟨1329288448746521697944425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28358153573259129556147733 1329288448746521697944425)
                    ·
                      refine ⟨996966336559891273458319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329288448746521697944425 996966336559891273458319)
                      ·
                        rfl

theorem cell23_1941585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 6, 2].length) (baseStart_1941585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941585 prefixEnd_1941585 := by exact prefixLift 1941585
  have htrace : WordTrace (prefixWord ++ tailWord_1941585) baseStart_1941585 baseEnd_1941585 := by
    simpa [prefixWord, tailWord_1941585, baseEnd_1941585] using wordTrace_append hprefix tailTrace_1941585
  have hstable : (prefixWord ++ tailWord_1941585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941585).length < 2 ^ (prefixWord ++ tailWord_1941585).sum := by decide
  have hdescent : baseEnd_1941585 < baseStart_1941585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941612 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 3, 4]
def baseStart_1941612 : Nat := 118140960795 + 1941612 * 2 ^ 59
def prefixEnd_1941612 : Nat := 4983230072969 + 3 ^ 40 * 1941612 * 2
def baseEnd_1941612 : Nat := 332326733512520889273565

theorem tailTrace_1941612 : CollatzResearch.WordTrace tailWord_1941612 prefixEnd_1941612 332326733512520889273565 := by
  unfold tailWord_1941612
  simp only [CollatzResearch.WordTrace]
  refine ⟨35408203720939399887305545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47210938294585866516407393 35408203720939399887305545)
  ·
    refine ⟨26556152790704549915479159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35408203720939399887305545 26556152790704549915479159)
    ·
      refine ⟨39834229186056824873218739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26556152790704549915479159 39834229186056824873218739)
      ·
        refine ⟨59751343779085237309828109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39834229186056824873218739 59751343779085237309828109)
        ·
          refine ⟨22406753917156963991185541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59751343779085237309828109 22406753917156963991185541)
          ·
            refine ⟨4201266359466930748347289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22406753917156963991185541 4201266359466930748347289)
            ·
              refine ⟨3150949769600198061260467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4201266359466930748347289 3150949769600198061260467)
              ·
                refine ⟨4726424654400297091890701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3150949769600198061260467 4726424654400297091890701)
                ·
                  refine ⟨1772409245400111409459013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4726424654400297091890701 1772409245400111409459013)
                  ·
                    refine ⟨332326733512520889273565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1772409245400111409459013 332326733512520889273565)
                    ·
                      rfl

theorem cell23_1941612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_1941612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941612 prefixEnd_1941612 := by exact prefixLift 1941612
  have htrace : WordTrace (prefixWord ++ tailWord_1941612) baseStart_1941612 baseEnd_1941612 := by
    simpa [prefixWord, tailWord_1941612, baseEnd_1941612] using wordTrace_append hprefix tailTrace_1941612
  have hstable : (prefixWord ++ tailWord_1941612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941612).length < 2 ^ (prefixWord ++ tailWord_1941612).sum := by decide
  have hdescent : baseEnd_1941612 < baseStart_1941612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941622 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1941622 : Nat := 118140960795 + 1941622 * 2 ^ 59
def prefixEnd_1941622 : Nat := 4983230072969 + 3 ^ 40 * 1941622 * 2
def baseEnd_1941622 : Nat := 996985335344107628695649

theorem tailTrace_1941622 : CollatzResearch.WordTrace tailWord_1941622 prefixEnd_1941622 996985335344107628695649 := by
  unfold tailWord_1941622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4426048260740160717654695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47211181447895047654983413 4426048260740160717654695)
  ·
    refine ⟨6639072391110241076482043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4426048260740160717654695 6639072391110241076482043)
    ·
      refine ⟨9958608586665361614723065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6639072391110241076482043 9958608586665361614723065)
      ·
        refine ⟨7468956439999021211042299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9958608586665361614723065 7468956439999021211042299)
        ·
          refine ⟨11203434659998531816563449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7468956439999021211042299 11203434659998531816563449)
          ·
            refine ⟨8402575994998898862422587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11203434659998531816563449 8402575994998898862422587)
            ·
              refine ⟨12603863992498348293633881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8402575994998898862422587 12603863992498348293633881)
              ·
                refine ⟨9452897994373761220225411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12603863992498348293633881 9452897994373761220225411)
                ·
                  refine ⟨14179346991560641830338117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9452897994373761220225411 14179346991560641830338117)
                  ·
                    refine ⟨2658627560917620343188397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14179346991560641830338117 2658627560917620343188397)
                    ·
                      refine ⟨996985335344107628695649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2658627560917620343188397 996985335344107628695649)
                      ·
                        rfl

theorem cell23_1941622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1941622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941622 prefixEnd_1941622 := by exact prefixLift 1941622
  have htrace : WordTrace (prefixWord ++ tailWord_1941622) baseStart_1941622 baseEnd_1941622 := by
    simpa [prefixWord, tailWord_1941622, baseEnd_1941622] using wordTrace_append hprefix tailTrace_1941622
  have hstable : (prefixWord ++ tailWord_1941622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941622).length < 2 ^ (prefixWord ++ tailWord_1941622).sum := by decide
  have hdescent : baseEnd_1941622 < baseStart_1941622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941765 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_1941765 : Nat := 118140960795 + 1941765 * 2 ^ 59
def prefixEnd_1941765 : Nat := 4983230072969 + 3 ^ 40 * 1941765 * 2
def baseEnd_1941765 : Nat := 997058763077700569207491

theorem tailTrace_1941765 : CollatzResearch.WordTrace tailWord_1941765 prefixEnd_1941765 997058763077700569207491 := by
  unfold tailWord_1941765
  simp only [CollatzResearch.WordTrace]
  refine ⟨70821987810324506904930749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47214658540216337936620499 70821987810324506904930749)
  ·
    refine ⟨26558245428871690089349031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70821987810324506904930749 26558245428871690089349031)
    ·
      refine ⟨39837368143307535134023547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26558245428871690089349031 39837368143307535134023547)
      ·
        refine ⟨59756052214961302701035321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39837368143307535134023547 59756052214961302701035321)
        ·
          refine ⟨44817039161220977025776491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59756052214961302701035321 44817039161220977025776491)
          ·
            refine ⟨67225558741831465538664737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44817039161220977025776491 67225558741831465538664737)
            ·
              refine ⟨50419169056373599153998553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67225558741831465538664737 50419169056373599153998553)
              ·
                refine ⟨37814376792280199365498915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50419169056373599153998553 37814376792280199365498915)
                ·
                  refine ⟨56721565188420299048248373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37814376792280199365498915 56721565188420299048248373)
                  ·
                    refine ⟨5317646736414403035773285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56721565188420299048248373 5317646736414403035773285)
                    ·
                      refine ⟨997058763077700569207491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5317646736414403035773285 997058763077700569207491)
                      ·
                        rfl

theorem cell23_1941765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_1941765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941765 prefixEnd_1941765 := by exact prefixLift 1941765
  have htrace : WordTrace (prefixWord ++ tailWord_1941765) baseStart_1941765 baseEnd_1941765 := by
    simpa [prefixWord, tailWord_1941765, baseEnd_1941765] using wordTrace_append hprefix tailTrace_1941765
  have hstable : (prefixWord ++ tailWord_1941765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941765).length < 2 ^ (prefixWord ++ tailWord_1941765).sum := by decide
  have hdescent : baseEnd_1941765 < baseStart_1941765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941792 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 2, 6]
def baseStart_1941792 : Nat := 118140960795 + 1941792 * 2 ^ 59
def prefixEnd_1941792 : Nat := 4983230072969 + 3 ^ 40 * 1941792 * 2
def baseEnd_1941792 : Nat := 332357542351790654523289

theorem tailTrace_1941792 : CollatzResearch.WordTrace tailWord_1941792 prefixEnd_1941792 332357542351790654523289 := by
  unfold tailWord_1941792
  simp only [CollatzResearch.WordTrace]
  refine ⟨35411486290613345258081815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47215315054151127010775753 35411486290613345258081815)
  ·
    refine ⟨53117229435920017887122723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35411486290613345258081815 53117229435920017887122723)
    ·
      refine ⟨79675844153880026830684085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53117229435920017887122723 79675844153880026830684085)
      ·
        refine ⟨7469610389426252515376633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79675844153880026830684085 7469610389426252515376633)
        ·
          refine ⟨5602207792069689386532475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7469610389426252515376633 5602207792069689386532475)
          ·
            refine ⟨8403311688104534079798713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602207792069689386532475 8403311688104534079798713)
            ·
              refine ⟨6302483766078400559849035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8403311688104534079798713 6302483766078400559849035)
              ·
                refine ⟨9453725649117600839773553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6302483766078400559849035 9453725649117600839773553)
                ·
                  refine ⟨7090294236838200629830165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9453725649117600839773553 7090294236838200629830165)
                  ·
                    refine ⟨332357542351790654523289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7090294236838200629830165 332357542351790654523289)
                    ·
                      rfl

theorem cell23_1941792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_1941792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941792 prefixEnd_1941792 := by exact prefixLift 1941792
  have htrace : WordTrace (prefixWord ++ tailWord_1941792) baseStart_1941792 baseEnd_1941792 := by
    simpa [prefixWord, tailWord_1941792, baseEnd_1941792] using wordTrace_append hprefix tailTrace_1941792
  have hstable : (prefixWord ++ tailWord_1941792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941792).length < 2 ^ (prefixWord ++ tailWord_1941792).sum := by decide
  have hdescent : baseEnd_1941792 < baseStart_1941792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941832 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_1941832 : Nat := 118140960795 + 1941832 * 2 ^ 59
def prefixEnd_1941832 : Nat := 4983230072969 + 3 ^ 40 * 1941832 * 2
def baseEnd_1941832 : Nat := 997093166281551807069683

theorem tailTrace_1941832 : CollatzResearch.WordTrace tailWord_1941832 prefixEnd_1941832 997093166281551807069683 := by
  unfold tailWord_1941832
  simp only [CollatzResearch.WordTrace]
  refine ⟨35412215750540888673809875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47216287667387851565079833 35412215750540888673809875)
  ·
    refine ⟨53118323625811333010714813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35412215750540888673809875 53118323625811333010714813)
    ·
      refine ⟨19919371359679249879018055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53118323625811333010714813 19919371359679249879018055)
      ·
        refine ⟨29879057039518874818527083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19919371359679249879018055 29879057039518874818527083)
        ·
          refine ⟨44818585559278312227790625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29879057039518874818527083 44818585559278312227790625)
          ·
            refine ⟨33613939169458734170842969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44818585559278312227790625 33613939169458734170842969)
            ·
              refine ⟨25210454377094050628132227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33613939169458734170842969 25210454377094050628132227)
              ·
                refine ⟨37815681565641075942198341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25210454377094050628132227 37815681565641075942198341)
                ·
                  refine ⟨7090440293557701739162189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37815681565641075942198341 7090440293557701739162189)
                  ·
                    refine ⟨2658915110084138152185821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7090440293557701739162189 2658915110084138152185821)
                    ·
                      refine ⟨997093166281551807069683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2658915110084138152185821 997093166281551807069683)
                      ·
                        rfl

theorem cell23_1941832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_1941832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941832 prefixEnd_1941832 := by exact prefixLift 1941832
  have htrace : WordTrace (prefixWord ++ tailWord_1941832) baseStart_1941832 baseEnd_1941832 := by
    simpa [prefixWord, tailWord_1941832, baseEnd_1941832] using wordTrace_append hprefix tailTrace_1941832
  have hstable : (prefixWord ++ tailWord_1941832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941832).length < 2 ^ (prefixWord ++ tailWord_1941832).sum := by decide
  have hdescent : baseEnd_1941832 < baseStart_1941832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941835 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 3, 7]
def baseStart_1941835 : Nat := 118140960795 + 1941835 * 2 ^ 59
def prefixEnd_1941835 : Nat := 4983230072969 + 3 ^ 40 * 1941835 * 2
def baseEnd_1941835 : Nat := 332364902241171765110723

theorem tailTrace_1941835 : CollatzResearch.WordTrace tailWord_1941835 prefixEnd_1941835 332364902241171765110723 := by
  unfold tailWord_1941835
  simp only [CollatzResearch.WordTrace]
  refine ⟨70824540920070908859978959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47216360613380605906652639 70824540920070908859978959)
  ·
    refine ⟨106236811380106363289968439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70824540920070908859978959 106236811380106363289968439)
    ·
      refine ⟨159355217070159544934952659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106236811380106363289968439 159355217070159544934952659)
      ·
        refine ⟨239032825605239317402428989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159355217070159544934952659 239032825605239317402428989)
        ·
          refine ⟨89637309601964744025910871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239032825605239317402428989 89637309601964744025910871)
          ·
            refine ⟨134455964402947116038866307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89637309601964744025910871 134455964402947116038866307)
            ·
              refine ⟨201683946604420674058299461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134455964402947116038866307 201683946604420674058299461)
              ·
                refine ⟨37815739988328876385931149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201683946604420674058299461 37815739988328876385931149)
                ·
                  refine ⟨14180902495623328644724181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37815739988328876385931149 14180902495623328644724181)
                  ·
                    refine ⟨332364902241171765110723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14180902495623328644724181 332364902241171765110723)
                    ·
                      rfl

theorem cell23_1941835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 7].length) (baseStart_1941835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941835 prefixEnd_1941835 := by exact prefixLift 1941835
  have htrace : WordTrace (prefixWord ++ tailWord_1941835) baseStart_1941835 baseEnd_1941835 := by
    simpa [prefixWord, tailWord_1941835, baseEnd_1941835] using wordTrace_append hprefix tailTrace_1941835
  have hstable : (prefixWord ++ tailWord_1941835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941835).length < 2 ^ (prefixWord ++ tailWord_1941835).sum := by decide
  have hdescent : baseEnd_1941835 < baseStart_1941835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941869 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_1941869 : Nat := 118140960795 + 1941869 * 2 ^ 59
def prefixEnd_1941869 : Nat := 4983230072969 + 3 ^ 40 * 1941869 * 2
def baseEnd_1941869 : Nat := 332370721688589387435671

theorem tailTrace_1941869 : CollatzResearch.WordTrace tailWord_1941869 prefixEnd_1941869 332370721688589387435671 := by
  unfold tailWord_1941869
  simp only [CollatzResearch.WordTrace]
  refine ⟨70825781001947732666716661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47217187334631821777811107 70825781001947732666716661)
  ·
    refine ⟨6639916968932599937504687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70825781001947732666716661 6639916968932599937504687)
    ·
      refine ⟨9959875453398899906257031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6639916968932599937504687 9959875453398899906257031)
      ·
        refine ⟨14939813180098349859385547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9959875453398899906257031 14939813180098349859385547)
        ·
          refine ⟨22409719770147524789078321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14939813180098349859385547 22409719770147524789078321)
          ·
            refine ⟨16807289827610643591808741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22409719770147524789078321 16807289827610643591808741)
            ·
              refine ⟨3151366842676995673464139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16807289827610643591808741 3151366842676995673464139)
              ·
                refine ⟨4727050264015493510196209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3151366842676995673464139 4727050264015493510196209)
                ·
                  refine ⟨3545287698011620132647157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4727050264015493510196209 3545287698011620132647157)
                  ·
                    refine ⟨332370721688589387435671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3545287698011620132647157 332370721688589387435671)
                    ·
                      rfl

theorem cell23_1941869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_1941869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941869 prefixEnd_1941869 := by exact prefixLift 1941869
  have htrace : WordTrace (prefixWord ++ tailWord_1941869) baseStart_1941869 baseEnd_1941869 := by
    simpa [prefixWord, tailWord_1941869, baseEnd_1941869] using wordTrace_append hprefix tailTrace_1941869
  have hstable : (prefixWord ++ tailWord_1941869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941869).length < 2 ^ (prefixWord ++ tailWord_1941869).sum := by decide
  have hdescent : baseEnd_1941869 < baseStart_1941869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941892 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1941892 : Nat := 118140960795 + 1941892 * 2 ^ 59
def prefixEnd_1941892 : Nat := 4983230072969 + 3 ^ 40 * 1941892 * 2
def baseEnd_1941892 : Nat := 997123975120821572319407

theorem tailTrace_1941892 : CollatzResearch.WordTrace tailWord_1941892 prefixEnd_1941892 997123975120821572319407 := by
  unfold tailWord_1941892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35413309940432203797401965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47217746587242938396535953 35413309940432203797401965)
  ·
    refine ⟨13279991227662076424025737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35413309940432203797401965 13279991227662076424025737)
    ·
      refine ⟨9959993420746557318019303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13279991227662076424025737 9959993420746557318019303)
      ·
        refine ⟨14939990131119835977028955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9959993420746557318019303 14939990131119835977028955)
        ·
          refine ⟨22409985196679753965543433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14939990131119835977028955 22409985196679753965543433)
          ·
            refine ⟨16807488897509815474157575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22409985196679753965543433 16807488897509815474157575)
            ·
              refine ⟨25211233346264723211236363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16807488897509815474157575 25211233346264723211236363)
              ·
                refine ⟨37816850019397084816854545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25211233346264723211236363 37816850019397084816854545)
                ·
                  refine ⟨28362637514547813612640909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37816850019397084816854545 28362637514547813612640909)
                  ·
                    refine ⟨10635989067955430104740341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28362637514547813612640909 10635989067955430104740341)
                    ·
                      refine ⟨997123975120821572319407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10635989067955430104740341 997123975120821572319407)
                      ·
                        rfl

theorem cell23_1941892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1941892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941892 prefixEnd_1941892 := by exact prefixLift 1941892
  have htrace : WordTrace (prefixWord ++ tailWord_1941892) baseStart_1941892 baseEnd_1941892 := by
    simpa [prefixWord, tailWord_1941892, baseEnd_1941892] using wordTrace_append hprefix tailTrace_1941892
  have hstable : (prefixWord ++ tailWord_1941892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941892).length < 2 ^ (prefixWord ++ tailWord_1941892).sum := by decide
  have hdescent : baseEnd_1941892 < baseStart_1941892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1941999 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 3]
def baseStart_1941999 : Nat := 118140960795 + 1941999 * 2 ^ 59
def prefixEnd_1941999 : Nat := 4983230072969 + 3 ^ 40 * 1941999 * 2
def baseEnd_1941999 : Nat := 997178917550852653681415

theorem tailTrace_1941999 : CollatzResearch.WordTrace tailWord_1941999 prefixEnd_1941999 997178917550852653681415 := by
  unfold tailWord_1941999
  simp only [CollatzResearch.WordTrace]
  refine ⟨70830522491476764868949051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47220348327651176579299367 70830522491476764868949051)
  ·
    refine ⟨106245783737215147303423577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70830522491476764868949051 106245783737215147303423577)
    ·
      refine ⟨79684337802911360477567683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106245783737215147303423577 79684337802911360477567683)
      ·
        refine ⟨119526506704367040716351525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79684337802911360477567683 119526506704367040716351525)
        ·
          refine ⟨22411220007068820134315911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119526506704367040716351525 22411220007068820134315911)
          ·
            refine ⟨33616830010603230201473867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22411220007068820134315911 33616830010603230201473867)
            ·
              refine ⟨50425245015904845302210801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33616830010603230201473867 50425245015904845302210801)
              ·
                refine ⟨37818933761928633976658101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50425245015904845302210801 37818933761928633976658101)
                ·
                  refine ⟨3545525040180809435311697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37818933761928633976658101 3545525040180809435311697)
                  ·
                    refine ⟨2659143780135607076483773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3545525040180809435311697 2659143780135607076483773)
                    ·
                      refine ⟨997178917550852653681415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2659143780135607076483773 997178917550852653681415)
                      ·
                        rfl

theorem cell23_1941999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 3].length) (baseStart_1941999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1941999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1941999 prefixEnd_1941999 := by exact prefixLift 1941999
  have htrace : WordTrace (prefixWord ++ tailWord_1941999) baseStart_1941999 baseEnd_1941999 := by
    simpa [prefixWord, tailWord_1941999, baseEnd_1941999] using wordTrace_append hprefix tailTrace_1941999
  have hstable : (prefixWord ++ tailWord_1941999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1941999).length < 2 ^ (prefixWord ++ tailWord_1941999).sum := by decide
  have hdescent : baseEnd_1941999 < baseStart_1941999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1941999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942006 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1942006 : Nat := 118140960795 + 1942006 * 2 ^ 59
def prefixEnd_1942006 : Nat := 4983230072969 + 3 ^ 40 * 1942006 * 2
def baseEnd_1942006 : Nat := 332394170638478042097961

theorem tailTrace_1942006 : CollatzResearch.WordTrace tailWord_1942006 prefixEnd_1942006 332394170638478042097961 := by
  unfold tailWord_1942006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4426923612653212816528367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47220518534967603376302581 4426923612653212816528367)
  ·
    refine ⟨6640385418979819224792551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4426923612653212816528367 6640385418979819224792551)
    ·
      refine ⟨9960578128469728837188827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6640385418979819224792551 9960578128469728837188827)
      ·
        refine ⟨14940867192704593255783241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9960578128469728837188827 14940867192704593255783241)
        ·
          refine ⟨11205650394528444941837431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14940867192704593255783241 11205650394528444941837431)
          ·
            refine ⟨16808475591792667412756147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11205650394528444941837431 16808475591792667412756147)
            ·
              refine ⟨25212713387689001119134221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16808475591792667412756147 25212713387689001119134221)
              ·
                refine ⟨9454767520383375419675333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25212713387689001119134221 9454767520383375419675333)
                ·
                  refine ⟨1772768910071882891189125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9454767520383375419675333 1772768910071882891189125)
                  ·
                    refine ⟨332394170638478042097961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1772768910071882891189125 332394170638478042097961)
                    ·
                      rfl

theorem cell23_1942006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1942006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942006 prefixEnd_1942006 := by exact prefixLift 1942006
  have htrace : WordTrace (prefixWord ++ tailWord_1942006) baseStart_1942006 baseEnd_1942006 := by
    simpa [prefixWord, tailWord_1942006, baseEnd_1942006] using wordTrace_append hprefix tailTrace_1942006
  have hstable : (prefixWord ++ tailWord_1942006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942006).length < 2 ^ (prefixWord ++ tailWord_1942006).sum := by decide
  have hdescent : baseEnd_1942006 < baseStart_1942006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942023 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 2, 4]
def baseStart_1942023 : Nat := 118140960795 + 1942023 * 2 ^ 59
def prefixEnd_1942023 : Nat := 4983230072969 + 3 ^ 40 * 1942023 * 2
def baseEnd_1942023 : Nat := 332397080362186853260435

theorem tailTrace_1942023 : CollatzResearch.WordTrace tailWord_1942023 prefixEnd_1942023 332397080362186853260435 := by
  unfold tailWord_1942023
  simp only [CollatzResearch.WordTrace]
  refine ⟨70831397843389816967822723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47220931895593211311881815 70831397843389816967822723)
  ·
    refine ⟨106247096765084725451734085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70831397843389816967822723 106247096765084725451734085)
    ·
      refine ⟨19921330643453386022200141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106247096765084725451734085 19921330643453386022200141)
      ·
        refine ⟨7470498991295019758325053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19921330643453386022200141 7470498991295019758325053)
        ·
          refine ⟨2801437121735632409371895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7470498991295019758325053 2801437121735632409371895)
          ·
            refine ⟨4202155682603448614057843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801437121735632409371895 4202155682603448614057843)
            ·
              refine ⟨6303233523905172921086765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4202155682603448614057843 6303233523905172921086765)
              ·
                refine ⟨2363712571464439845407537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6303233523905172921086765 2363712571464439845407537)
                ·
                  refine ⟨1772784428598329884055653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363712571464439845407537 1772784428598329884055653)
                  ·
                    refine ⟨332397080362186853260435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1772784428598329884055653 332397080362186853260435)
                    ·
                      rfl

theorem cell23_1942023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_1942023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942023 prefixEnd_1942023 := by exact prefixLift 1942023
  have htrace : WordTrace (prefixWord ++ tailWord_1942023) baseStart_1942023 baseEnd_1942023 := by
    simpa [prefixWord, tailWord_1942023, baseEnd_1942023] using wordTrace_append hprefix tailTrace_1942023
  have hstable : (prefixWord ++ tailWord_1942023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942023).length < 2 ^ (prefixWord ++ tailWord_1942023).sum := by decide
  have hdescent : baseEnd_1942023 < baseStart_1942023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942036 : List Nat := [2, 4, 3, 1, 1, 1, 2, 9]
def baseStart_1942036 : Nat := 118140960795 + 1942036 * 2 ^ 59
def prefixEnd_1942036 : Nat := 4983230072969 + 3 ^ 40 * 1942036 * 2
def baseEnd_1942036 : Nat := 36933256160558111441435

theorem tailTrace_1942036 : CollatzResearch.WordTrace tailWord_1942036 prefixEnd_1942036 36933256160558111441435 := by
  unfold tailWord_1942036
  simp only [CollatzResearch.WordTrace]
  refine ⟨35415935996171360094022981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47221247994895146792030641 35415935996171360094022981)
  ·
    refine ⟨6640487999282130017629309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35415935996171360094022981 6640487999282130017629309)
    ·
      refine ⟨2490182999730798756610991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6640487999282130017629309 2490182999730798756610991)
      ·
        refine ⟨3735274499596198134916487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490182999730798756610991 3735274499596198134916487)
        ·
          refine ⟨5602911749394297202374731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3735274499596198134916487 5602911749394297202374731)
          ·
            refine ⟨8404367624091445803562097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5602911749394297202374731 8404367624091445803562097)
            ·
              refine ⟨6303275718068584352671573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8404367624091445803562097 6303275718068584352671573)
              ·
                refine ⟨36933256160558111441435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6303275718068584352671573 36933256160558111441435)
                ·
                  rfl

theorem cell23_1942036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 9].length) (baseStart_1942036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942036 prefixEnd_1942036 := by exact prefixLift 1942036
  have htrace : WordTrace (prefixWord ++ tailWord_1942036) baseStart_1942036 baseEnd_1942036 := by
    simpa [prefixWord, tailWord_1942036, baseEnd_1942036] using wordTrace_append hprefix tailTrace_1942036
  have hstable : (prefixWord ++ tailWord_1942036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942036).length < 2 ^ (prefixWord ++ tailWord_1942036).sum := by decide
  have hdescent : baseEnd_1942036 < baseStart_1942036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942069 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1942069 : Nat := 118140960795 + 1942069 * 2 ^ 59
def prefixEnd_1942069 : Nat := 4983230072969 + 3 ^ 40 * 1942069 * 2
def baseEnd_1942069 : Nat := 997214861196667379806093

theorem tailTrace_1942069 : CollatzResearch.WordTrace tailWord_1942069 prefixEnd_1942069 997214861196667379806093 := by
  unfold tailWord_1942069
  simp only [CollatzResearch.WordTrace]
  refine ⟨70833075601223166823997261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47222050400815444549331507 70833075601223166823997261)
  ·
    refine ⟨26562403350458687558998973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70833075601223166823997261 26562403350458687558998973)
    ·
      refine ⟨9960901256422007834624615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26562403350458687558998973 9960901256422007834624615)
      ·
        refine ⟨14941351884633011751936923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9960901256422007834624615 14941351884633011751936923)
        ·
          refine ⟨22412027826949517627905385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14941351884633011751936923 22412027826949517627905385)
          ·
            refine ⟨16809020870212138220929039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22412027826949517627905385 16809020870212138220929039)
            ·
              refine ⟨25213531305318207331393559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16809020870212138220929039 25213531305318207331393559)
              ·
                refine ⟨37820296957977310997090339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25213531305318207331393559 37820296957977310997090339)
                ·
                  refine ⟨56730445436965966495635509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37820296957977310997090339 56730445436965966495635509)
                  ·
                    refine ⟨5318479259715559358965829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56730445436965966495635509 5318479259715559358965829)
                    ·
                      refine ⟨997214861196667379806093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5318479259715559358965829 997214861196667379806093)
                      ·
                        rfl

theorem cell23_1942069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1942069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942069 prefixEnd_1942069 := by exact prefixLift 1942069
  have htrace : WordTrace (prefixWord ++ tailWord_1942069) baseStart_1942069 baseEnd_1942069 := by
    simpa [prefixWord, tailWord_1942069, baseEnd_1942069] using wordTrace_append hprefix tailTrace_1942069
  have hstable : (prefixWord ++ tailWord_1942069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942069).length < 2 ^ (prefixWord ++ tailWord_1942069).sum := by decide
  have hdescent : baseEnd_1942069 < baseStart_1942069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942079 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 2, 6]
def baseStart_1942079 : Nat := 118140960795 + 1942079 * 2 ^ 59
def prefixEnd_1942079 : Nat := 4983230072969 + 3 ^ 40 * 1942079 * 2
def baseEnd_1942079 : Nat := 332406665334404113560349

theorem tailTrace_1942079 : CollatzResearch.WordTrace tailWord_1942079 prefixEnd_1942079 332406665334404113560349 := by
  unfold tailWord_1942079
  simp only [CollatzResearch.WordTrace]
  refine ⟨70833440331186938531861291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47222293554124625687907527 70833440331186938531861291)
  ·
    refine ⟨106250160496780407797791937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70833440331186938531861291 106250160496780407797791937)
    ·
      refine ⟨79687620372585305848343953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106250160496780407797791937 79687620372585305848343953)
      ·
        refine ⟨59765715279438979386257965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79687620372585305848343953 59765715279438979386257965)
        ·
          refine ⟨22412143229789617269846737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59765715279438979386257965 22412143229789617269846737)
          ·
            refine ⟨16809107422342212952385053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22412143229789617269846737 16809107422342212952385053)
            ·
              refine ⟨6303415283378329857144395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16809107422342212952385053 6303415283378329857144395)
              ·
                refine ⟨9455122925067494785716593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6303415283378329857144395 9455122925067494785716593)
                ·
                  refine ⟨7091342193800621089287445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9455122925067494785716593 7091342193800621089287445)
                  ·
                    refine ⟨332406665334404113560349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7091342193800621089287445 332406665334404113560349)
                    ·
                      rfl

theorem cell23_1942079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_1942079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942079 prefixEnd_1942079 := by exact prefixLift 1942079
  have htrace : WordTrace (prefixWord ++ tailWord_1942079) baseStart_1942079 baseEnd_1942079 := by
    simpa [prefixWord, tailWord_1942079, baseEnd_1942079] using wordTrace_append hprefix tailTrace_1942079
  have hstable : (prefixWord ++ tailWord_1942079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942079).length < 2 ^ (prefixWord ++ tailWord_1942079).sum := by decide
  have hdescent : baseEnd_1942079 < baseStart_1942079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942103 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 4, 2, 2]
def baseStart_1942103 : Nat := 118140960795 + 1942103 * 2 ^ 59
def prefixEnd_1942103 : Nat := 4983230072969 + 3 ^ 40 * 1942103 * 2
def baseEnd_1942103 : Nat := 997232319538920246780937

theorem tailTrace_1942103 : CollatzResearch.WordTrace tailWord_1942103 prefixEnd_1942103 997232319538920246780937 := by
  unfold tailWord_1942103
  simp only [CollatzResearch.WordTrace]
  refine ⟨70834315683099990630734963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47222877122066660420489975 70834315683099990630734963)
  ·
    refine ⟨106251473524649985946102445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70834315683099990630734963 106251473524649985946102445)
    ·
      refine ⟨39844302571743744729788417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106251473524649985946102445 39844302571743744729788417)
      ·
        refine ⟨29883226928807808547341313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39844302571743744729788417 29883226928807808547341313)
        ·
          refine ⟨22412420196605856410505985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29883226928807808547341313 22412420196605856410505985)
          ·
            refine ⟨16809315147454392307879489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22412420196605856410505985 16809315147454392307879489)
            ·
              refine ⟨12606986360590794230909617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16809315147454392307879489 12606986360590794230909617)
              ·
                refine ⟨9455239770443095673182213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12606986360590794230909617 9455239770443095673182213)
                ·
                  refine ⟨1772857456958080438721665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9455239770443095673182213 1772857456958080438721665)
                  ·
                    refine ⟨1329643092718560329041249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1772857456958080438721665 1329643092718560329041249)
                    ·
                      refine ⟨997232319538920246780937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329643092718560329041249 997232319538920246780937)
                      ·
                        rfl

theorem cell23_1942103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_1942103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942103 prefixEnd_1942103 := by exact prefixLift 1942103
  have htrace : WordTrace (prefixWord ++ tailWord_1942103) baseStart_1942103 baseEnd_1942103 := by
    simpa [prefixWord, tailWord_1942103, baseEnd_1942103] using wordTrace_append hprefix tailTrace_1942103
  have hstable : (prefixWord ++ tailWord_1942103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942103).length < 2 ^ (prefixWord ++ tailWord_1942103).sum := by decide
  have hdescent : baseEnd_1942103 < baseStart_1942103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942114 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1942114 : Nat := 118140960795 + 1942114 * 2 ^ 59
def prefixEnd_1942114 : Nat := 4983230072969 + 3 ^ 40 * 1942114 * 2
def baseEnd_1942114 : Nat := 997237967826119703743387

theorem tailTrace_1942114 : CollatzResearch.WordTrace tailWord_1942114 prefixEnd_1942114 997237967826119703743387 := by
  unfold tailWord_1942114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17708679221515034877346349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47223144590706759672923597 17708679221515034877346349)
  ·
    refine ⟨6640754708068138079004881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17708679221515034877346349 6640754708068138079004881)
    ·
      refine ⟨4980566031051103559253661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6640754708068138079004881 4980566031051103559253661)
      ·
        refine ⟨1867712261644163834720123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4980566031051103559253661 1867712261644163834720123)
        ·
          refine ⟨2801568392466245752080185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867712261644163834720123 2801568392466245752080185)
          ·
            refine ⟨2101176294349684314060139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2801568392466245752080185 2101176294349684314060139)
            ·
              refine ⟨3151764441524526471090209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101176294349684314060139 3151764441524526471090209)
              ·
                refine ⟨2363823331143394853317657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3151764441524526471090209 2363823331143394853317657)
                ·
                  refine ⟨1772867498357546139988243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363823331143394853317657 1772867498357546139988243)
                  ·
                    refine ⟨2659301247536319209982365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1772867498357546139988243 2659301247536319209982365)
                    ·
                      refine ⟨997237967826119703743387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2659301247536319209982365 997237967826119703743387)
                      ·
                        rfl

theorem cell23_1942114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1942114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942114 prefixEnd_1942114 := by exact prefixLift 1942114
  have htrace : WordTrace (prefixWord ++ tailWord_1942114) baseStart_1942114 baseEnd_1942114 := by
    simpa [prefixWord, tailWord_1942114, baseEnd_1942114] using wordTrace_append hprefix tailTrace_1942114
  have hstable : (prefixWord ++ tailWord_1942114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942114).length < 2 ^ (prefixWord ++ tailWord_1942114).sum := by decide
  have hdescent : baseEnd_1942114 < baseStart_1942114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942126 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_1942126 : Nat := 118140960795 + 1942126 * 2 ^ 59
def prefixEnd_1942126 : Nat := 4983230072969 + 3 ^ 40 * 1942126 * 2
def baseEnd_1942126 : Nat := 110804903288219295199259

theorem tailTrace_1942126 : CollatzResearch.WordTrace tailWord_1942126 prefixEnd_1942126 110804903288219295199259 := by
  unfold tailWord_1942126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8854394320252083194852779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47223436374677777039214821 8854394320252083194852779)
  ·
    refine ⟨13281591480378124792279169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8854394320252083194852779 13281591480378124792279169)
    ·
      refine ⟨9961193610283593594209377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13281591480378124792279169 9961193610283593594209377)
      ·
        refine ⟨7470895207712695195657033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9961193610283593594209377 7470895207712695195657033)
        ·
          refine ⟨5603171405784521396742775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7470895207712695195657033 5603171405784521396742775)
          ·
            refine ⟨8404757108676782095114163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603171405784521396742775 8404757108676782095114163)
            ·
              refine ⟨12607135663015173142671245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8404757108676782095114163 12607135663015173142671245)
              ·
                refine ⟨4727675873630689928501717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12607135663015173142671245 4727675873630689928501717)
                ·
                  refine ⟨110804903288219295199259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4727675873630689928501717 110804903288219295199259)
                  ·
                    rfl

theorem cell23_1942126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_1942126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942126 prefixEnd_1942126 := by exact prefixLift 1942126
  have htrace : WordTrace (prefixWord ++ tailWord_1942126) baseStart_1942126 baseEnd_1942126 := by
    simpa [prefixWord, tailWord_1942126, baseEnd_1942126] using wordTrace_append hprefix tailTrace_1942126
  have hstable : (prefixWord ++ tailWord_1942126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942126).length < 2 ^ (prefixWord ++ tailWord_1942126).sum := by decide
  have hdescent : baseEnd_1942126 < baseStart_1942126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942137 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 2, 2, 2]
def baseStart_1942137 : Nat := 118140960795 + 1942137 * 2 ^ 59
def prefixEnd_1942137 : Nat := 4983230072969 + 3 ^ 40 * 1942137 * 2
def baseEnd_1942137 : Nat := 997249777881173113755781

theorem tailTrace_1942137 : CollatzResearch.WordTrace tailWord_1942137 prefixEnd_1942137 997249777881173113755781 := by
  unfold tailWord_1942137
  simp only [CollatzResearch.WordTrace]
  refine ⟨70835555764976814437472665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47223703843317876291648443 70835555764976814437472665)
  ·
    refine ⟨53126666823732610828104499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70835555764976814437472665 53126666823732610828104499)
    ·
      refine ⟨79690000235598916242156749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53126666823732610828104499 79690000235598916242156749)
      ·
        refine ⟨29883750088349593590808781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79690000235598916242156749 29883750088349593590808781)
        ·
          refine ⟨11206406283131097596553293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29883750088349593590808781 11206406283131097596553293)
          ·
            refine ⟨4202402356174161598707485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11206406283131097596553293 4202402356174161598707485)
            ·
              refine ⟨1575900883565310599515307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4202402356174161598707485 1575900883565310599515307)
              ·
                refine ⟨2363851325347965899272961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1575900883565310599515307 2363851325347965899272961)
                ·
                  refine ⟨1772888494010974424454721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2363851325347965899272961 1772888494010974424454721)
                  ·
                    refine ⟨1329666370508230818341041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1772888494010974424454721 1329666370508230818341041)
                    ·
                      refine ⟨997249777881173113755781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329666370508230818341041 997249777881173113755781)
                      ·
                        rfl

theorem cell23_1942137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_1942137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942137 prefixEnd_1942137 := by exact prefixLift 1942137
  have htrace : WordTrace (prefixWord ++ tailWord_1942137) baseStart_1942137 baseEnd_1942137 := by
    simpa [prefixWord, tailWord_1942137, baseEnd_1942137] using wordTrace_append hprefix tailTrace_1942137
  have hstable : (prefixWord ++ tailWord_1942137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942137).length < 2 ^ (prefixWord ++ tailWord_1942137).sum := by decide
  have hdescent : baseEnd_1942137 < baseStart_1942137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942139 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 6, 5]
def baseStart_1942139 : Nat := 118140960795 + 1942139 * 2 ^ 59
def prefixEnd_1942139 : Nat := 4983230072969 + 3 ^ 40 * 1942139 * 2
def baseEnd_1942139 : Nat := 332416934947494035310257

theorem tailTrace_1942139 : CollatzResearch.WordTrace tailWord_1942139 prefixEnd_1942139 332416934947494035310257 := by
  unfold tailWord_1942139
  simp only [CollatzResearch.WordTrace]
  refine ⟨70835628710969568779045471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47223752473979712519363647 70835628710969568779045471)
  ·
    refine ⟨106253443066454353168568207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70835628710969568779045471 106253443066454353168568207)
    ·
      refine ⟨159380164599681529752852311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106253443066454353168568207 159380164599681529752852311)
      ·
        refine ⟨239070246899522294629278467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159380164599681529752852311 239070246899522294629278467)
        ·
          refine ⟨358605370349283441943917701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239070246899522294629278467 358605370349283441943917701)
          ·
            refine ⟨67238506940490645364484569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358605370349283441943917701 67238506940490645364484569)
            ·
              refine ⟨50428880205367984023363427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67238506940490645364484569 50428880205367984023363427)
              ·
                refine ⟨75643320308051976035045141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50428880205367984023363427 75643320308051976035045141)
                ·
                  refine ⟨3545780639439936376642741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75643320308051976035045141 3545780639439936376642741)
                  ·
                    refine ⟨332416934947494035310257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3545780639439936376642741 332416934947494035310257)
                    ·
                      rfl

theorem cell23_1942139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 5].length) (baseStart_1942139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942139 prefixEnd_1942139 := by exact prefixLift 1942139
  have htrace : WordTrace (prefixWord ++ tailWord_1942139) baseStart_1942139 baseEnd_1942139 := by
    simpa [prefixWord, tailWord_1942139, baseEnd_1942139] using wordTrace_append hprefix tailTrace_1942139
  have hstable : (prefixWord ++ tailWord_1942139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942139).length < 2 ^ (prefixWord ++ tailWord_1942139).sum := by decide
  have hdescent : baseEnd_1942139 < baseStart_1942139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942179 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 5]
def baseStart_1942179 : Nat := 118140960795 + 1942179 * 2 ^ 59
def prefixEnd_1942179 : Nat := 4983230072969 + 3 ^ 40 * 1942179 * 2
def baseEnd_1942179 : Nat := 997271344068661949430587

theorem tailTrace_1942179 : CollatzResearch.WordTrace tailWord_1942179 prefixEnd_1942179 997271344068661949430587 := by
  unfold tailWord_1942179
  simp only [CollatzResearch.WordTrace]
  refine ⟨70837087630824655610501591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47224725087216437073667727 70837087630824655610501591)
  ·
    refine ⟨106255631446236983415752387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70837087630824655610501591 106255631446236983415752387)
    ·
      refine ⟨159383447169355475123628581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106255631446236983415752387 159383447169355475123628581)
      ·
        refine ⟨29884396344254151585680359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159383447169355475123628581 29884396344254151585680359)
        ·
          refine ⟨44826594516381227378520539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29884396344254151585680359 44826594516381227378520539)
          ·
            refine ⟨67239891774571841067780809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44826594516381227378520539 67239891774571841067780809)
            ·
              refine ⟨50429918830928880800835607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67239891774571841067780809 50429918830928880800835607)
              ·
                refine ⟨75644878246393321201253411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50429918830928880800835607 75644878246393321201253411)
                ·
                  refine ⟨113467317369589981801880117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75644878246393321201253411 113467317369589981801880117)
                  ·
                    refine ⟨10637561003399060793926261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113467317369589981801880117 10637561003399060793926261)
                    ·
                      refine ⟨997271344068661949430587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10637561003399060793926261 997271344068661949430587)
                      ·
                        rfl

theorem cell23_1942179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_1942179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942179 prefixEnd_1942179 := by exact prefixLift 1942179
  have htrace : WordTrace (prefixWord ++ tailWord_1942179) baseStart_1942179 baseEnd_1942179 := by
    simpa [prefixWord, tailWord_1942179, baseEnd_1942179] using wordTrace_append hprefix tailTrace_1942179
  have hstable : (prefixWord ++ tailWord_1942179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942179).length < 2 ^ (prefixWord ++ tailWord_1942179).sum := by decide
  have hdescent : baseEnd_1942179 < baseStart_1942179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942219 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 8]
def baseStart_1942219 : Nat := 118140960795 + 1942219 * 2 ^ 59
def prefixEnd_1942219 : Nat := 4983230072969 + 3 ^ 40 * 1942219 * 2
def baseEnd_1942219 : Nat := 997291883294841792930403

theorem tailTrace_1942219 : CollatzResearch.WordTrace tailWord_1942219 prefixEnd_1942219 997291883294841792930403 := by
  unfold tailWord_1942219
  simp only [CollatzResearch.WordTrace]
  refine ⟨70838546550679742441957711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47225697700453161627971807 70838546550679742441957711)
  ·
    refine ⟨106257819826019613662936567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70838546550679742441957711 106257819826019613662936567)
    ·
      refine ⟨159386729739029420494404851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106257819826019613662936567 159386729739029420494404851)
      ·
        refine ⟨239080094608544130741607277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159386729739029420494404851 239080094608544130741607277)
        ·
          refine ⟨89655035478204049028102729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239080094608544130741607277 89655035478204049028102729)
          ·
            refine ⟨67241276608653036771077047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89655035478204049028102729 67241276608653036771077047)
            ·
              refine ⟨100861914912979555156615571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67241276608653036771077047 100861914912979555156615571)
              ·
                refine ⟨151292872369469332734923357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100861914912979555156615571 151292872369469332734923357)
                ·
                  refine ⟨56734827138550999775596259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151292872369469332734923357 56734827138550999775596259)
                  ·
                    refine ⟨85102240707826499663394389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56734827138550999775596259 85102240707826499663394389)
                    ·
                      refine ⟨997291883294841792930403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 85102240707826499663394389 997291883294841792930403)
                      ·
                        rfl

theorem cell23_1942219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_1942219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942219 prefixEnd_1942219 := by exact prefixLift 1942219
  have htrace : WordTrace (prefixWord ++ tailWord_1942219) baseStart_1942219 baseEnd_1942219 := by
    simpa [prefixWord, tailWord_1942219, baseEnd_1942219] using wordTrace_append hprefix tailTrace_1942219
  have hstable : (prefixWord ++ tailWord_1942219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942219).length < 2 ^ (prefixWord ++ tailWord_1942219).sum := by decide
  have hdescent : baseEnd_1942219 < baseStart_1942219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942261 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1942261 : Nat := 118140960795 + 1942261 * 2 ^ 59
def prefixEnd_1942261 : Nat := 4983230072969 + 3 ^ 40 * 1942261 * 2
def baseEnd_1942261 : Nat := 997313449482330628605211

theorem tailTrace_1942261 : CollatzResearch.WordTrace tailWord_1942261 prefixEnd_1942261 997313449482330628605211 := by
  unfold tailWord_1942261
  simp only [CollatzResearch.WordTrace]
  refine ⟨70840078416527583614986637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47226718944351722409991091 70840078416527583614986637)
  ·
    refine ⟨26565029406197843855619989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70840078416527583614986637 26565029406197843855619989)
    ·
      refine ⟨1245235753415523930732187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26565029406197843855619989 1245235753415523930732187)
      ·
        refine ⟨1867853630123285896098281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245235753415523930732187 1867853630123285896098281)
        ·
          refine ⟨1400890222592464422073711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1867853630123285896098281 1400890222592464422073711)
          ·
            refine ⟨2101335333888696633110567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400890222592464422073711 2101335333888696633110567)
            ·
              refine ⟨3152003000833044949665851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2101335333888696633110567 3152003000833044949665851)
              ·
                refine ⟨4728004501249567424498777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152003000833044949665851 4728004501249567424498777)
                ·
                  refine ⟨3546003375937175568374083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4728004501249567424498777 3546003375937175568374083)
                  ·
                    refine ⟨5319005063905763352561125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3546003375937175568374083 5319005063905763352561125)
                    ·
                      refine ⟨997313449482330628605211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5319005063905763352561125 997313449482330628605211)
                      ·
                        rfl

theorem cell23_1942261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1942261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942261 prefixEnd_1942261 := by exact prefixLift 1942261
  have htrace : WordTrace (prefixWord ++ tailWord_1942261) baseStart_1942261 baseEnd_1942261 := by
    simpa [prefixWord, tailWord_1942261, baseEnd_1942261] using wordTrace_append hprefix tailTrace_1942261
  have hstable : (prefixWord ++ tailWord_1942261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942261).length < 2 ^ (prefixWord ++ tailWord_1942261).sum := by decide
  have hdescent : baseEnd_1942261 < baseStart_1942261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942280 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 1, 5]
def baseStart_1942280 : Nat := 118140960795 + 1942280 * 2 ^ 59
def prefixEnd_1942280 : Nat := 4983230072969 + 3 ^ 40 * 1942280 * 2
def baseEnd_1942280 : Nat := 332441068538255351422541

theorem tailTrace_1942280 : CollatzResearch.WordTrace tailWord_1942280 prefixEnd_1942280 332441068538255351422541 := by
  unfold tailWord_1942280
  simp only [CollatzResearch.WordTrace]
  refine ⟨35420385701729374929964147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47227180935639166573285529 35420385701729374929964147)
  ·
    refine ⟨53130578552594062394946221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35420385701729374929964147 53130578552594062394946221)
    ·
      refine ⟨19923966957222773398104833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53130578552594062394946221 19923966957222773398104833)
      ·
        refine ⟨14942975217917080048578625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19923966957222773398104833 14942975217917080048578625)
        ·
          refine ⟨11207231413437810036433969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14942975217917080048578625 11207231413437810036433969)
          ·
            refine ⟨8405423560078357527325477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11207231413437810036433969 8405423560078357527325477)
            ·
              refine ⟨1576016917514692036373527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8405423560078357527325477 1576016917514692036373527)
              ·
                refine ⟨2364025376272038054560291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576016917514692036373527 2364025376272038054560291)
                ·
                  refine ⟨3546038064408057081840437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364025376272038054560291 3546038064408057081840437)
                  ·
                    refine ⟨332441068538255351422541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3546038064408057081840437 332441068538255351422541)
                    ·
                      rfl

theorem cell23_1942280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_1942280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942280 prefixEnd_1942280 := by exact prefixLift 1942280
  have htrace : WordTrace (prefixWord ++ tailWord_1942280) baseStart_1942280 baseEnd_1942280 := by
    simpa [prefixWord, tailWord_1942280, baseEnd_1942280] using wordTrace_append hprefix tailTrace_1942280
  have hstable : (prefixWord ++ tailWord_1942280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942280).length < 2 ^ (prefixWord ++ tailWord_1942280).sum := by decide
  have hdescent : baseEnd_1942280 < baseStart_1942280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942293 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 4, 4]
def baseStart_1942293 : Nat := 118140960795 + 1942293 * 2 ^ 59
def prefixEnd_1942293 : Nat := 4983230072969 + 3 ^ 40 * 1942293 * 2
def baseEnd_1942293 : Nat := 332443293621091501135021

theorem tailTrace_1942293 : CollatzResearch.WordTrace tailWord_1942293 prefixEnd_1942293 332443293621091501135021 := by
  unfold tailWord_1942293
  simp only [CollatzResearch.WordTrace]
  refine ⟨70841245552411653080151533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47227497034941102053434355 70841245552411653080151533)
  ·
    refine ⟨26565467082154369905056825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70841245552411653080151533 26565467082154369905056825)
    ·
      refine ⟨19924100311615777428792619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26565467082154369905056825 19924100311615777428792619)
      ·
        refine ⟨29886150467423666143188929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19924100311615777428792619 29886150467423666143188929)
        ·
          refine ⟨22414612850567749607391697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29886150467423666143188929 22414612850567749607391697)
          ·
            refine ⟨16810959637925812205543773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22414612850567749607391697 16810959637925812205543773)
            ·
              refine ⟨6304109864222179577078915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16810959637925812205543773 6304109864222179577078915)
              ·
                refine ⟨9456164796333269365618373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304109864222179577078915 9456164796333269365618373)
                ·
                  refine ⟨1773030899312488006053445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9456164796333269365618373 1773030899312488006053445)
                  ·
                    refine ⟨332443293621091501135021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1773030899312488006053445 332443293621091501135021)
                    ·
                      rfl

theorem cell23_1942293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_1942293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942293 prefixEnd_1942293 := by exact prefixLift 1942293
  have htrace : WordTrace (prefixWord ++ tailWord_1942293) baseStart_1942293 baseEnd_1942293 := by
    simpa [prefixWord, tailWord_1942293, baseEnd_1942293] using wordTrace_append hprefix tailTrace_1942293
  have hstable : (prefixWord ++ tailWord_1942293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942293).length < 2 ^ (prefixWord ++ tailWord_1942293).sum := by decide
  have hdescent : baseEnd_1942293 < baseStart_1942293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942296 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1942296 : Nat := 118140960795 + 1942296 * 2 ^ 59
def prefixEnd_1942296 : Nat := 4983230072969 + 3 ^ 40 * 1942296 * 2
def baseEnd_1942296 : Nat := 997331421305237991667549

theorem tailTrace_1942296 : CollatzResearch.WordTrace tailWord_1942296 prefixEnd_1942296 997331421305237991667549 := by
  unfold tailWord_1942296
  simp only [CollatzResearch.WordTrace]
  refine ⟨35420677485700392296255371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47227569980933856395007161 35420677485700392296255371)
  ·
    refine ⟨53131016228550588444383057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35420677485700392296255371 53131016228550588444383057)
    ·
      refine ⟨39848262171412941333287293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53131016228550588444383057 39848262171412941333287293)
      ·
        refine ⟨14943098314279852999982735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39848262171412941333287293 14943098314279852999982735)
        ·
          refine ⟨22414647471419779499974103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14943098314279852999982735 22414647471419779499974103)
          ·
            refine ⟨33621971207129669249961155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22414647471419779499974103 33621971207129669249961155)
            ·
              refine ⟨50432956810694503874941733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33621971207129669249961155 50432956810694503874941733)
              ·
                refine ⟨9456179402005219476551575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50432956810694503874941733 9456179402005219476551575)
                ·
                  refine ⟨14184269103007829214827363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9456179402005219476551575 14184269103007829214827363)
                  ·
                    refine ⟨21276403654511743822241045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14184269103007829214827363 21276403654511743822241045)
                    ·
                      refine ⟨997331421305237991667549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21276403654511743822241045 997331421305237991667549)
                      ·
                        rfl

theorem cell23_1942296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1942296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942296 prefixEnd_1942296 := by exact prefixLift 1942296
  have htrace : WordTrace (prefixWord ++ tailWord_1942296) baseStart_1942296 baseEnd_1942296 := by
    simpa [prefixWord, tailWord_1942296, baseEnd_1942296] using wordTrace_append hprefix tailTrace_1942296
  have hstable : (prefixWord ++ tailWord_1942296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942296).length < 2 ^ (prefixWord ++ tailWord_1942296).sum := by decide
  have hdescent : baseEnd_1942296 < baseStart_1942296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942303 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 5]
def baseStart_1942303 : Nat := 118140960795 + 1942303 * 2 ^ 59
def prefixEnd_1942303 : Nat := 4983230072969 + 3 ^ 40 * 1942303 * 2
def baseEnd_1942303 : Nat := 997335015669819464280017

theorem tailTrace_1942303 : CollatzResearch.WordTrace tailWord_1942303 prefixEnd_1942303 997335015669819464280017 := by
  unfold tailWord_1942303
  simp only [CollatzResearch.WordTrace]
  refine ⟨70841610282375424788015563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47227740188250283192010375 70841610282375424788015563)
  ·
    refine ⟨106262415423563137182023345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70841610282375424788015563 106262415423563137182023345)
    ·
      refine ⟨79696811567672352886517509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106262415423563137182023345 79696811567672352886517509)
      ·
        refine ⟨14943152168938566166222033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79696811567672352886517509 14943152168938566166222033)
        ·
          refine ⟨11207364126703924624666525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14943152168938566166222033 11207364126703924624666525)
          ·
            refine ⟨4202761547513971734249947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11207364126703924624666525 4202761547513971734249947)
            ·
              refine ⟨6304142321270957601374921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4202761547513971734249947 6304142321270957601374921)
              ·
                refine ⟨4728106740953218201031191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6304142321270957601374921 4728106740953218201031191)
                ·
                  refine ⟨7092160111429827301546787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728106740953218201031191 7092160111429827301546787)
                  ·
                    refine ⟨10638240167144740952320181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7092160111429827301546787 10638240167144740952320181)
                    ·
                      refine ⟨997335015669819464280017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10638240167144740952320181 997335015669819464280017)
                      ·
                        rfl

theorem cell23_1942303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_1942303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942303 prefixEnd_1942303 := by exact prefixLift 1942303
  have htrace : WordTrace (prefixWord ++ tailWord_1942303) baseStart_1942303 baseEnd_1942303 := by
    simpa [prefixWord, tailWord_1942303, baseEnd_1942303] using wordTrace_append hprefix tailTrace_1942303
  have hstable : (prefixWord ++ tailWord_1942303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942303).length < 2 ^ (prefixWord ++ tailWord_1942303).sum := by decide
  have hdescent : baseEnd_1942303 < baseStart_1942303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942323 : List Nat := [1, 1, 1, 2, 6, 1, 4, 7]
def baseStart_1942323 : Nat := 118140960795 + 1942323 * 2 ^ 59
def prefixEnd_1942323 : Nat := 4983230072969 + 3 ^ 40 * 1942323 * 2
def baseEnd_1942323 : Nat := 36938714269737384667775

theorem tailTrace_1942323 : CollatzResearch.WordTrace tailWord_1942323 prefixEnd_1942323 36938714269737384667775 := by
  unfold tailWord_1942323
  simp only [CollatzResearch.WordTrace]
  refine ⟨70842339742302968203743623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47228226494868645469162415 70842339742302968203743623)
  ·
    refine ⟨106263509613454452305615435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70842339742302968203743623 106263509613454452305615435)
    ·
      refine ⟨159395264420181678458423153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106263509613454452305615435 159395264420181678458423153)
      ·
        refine ⟨119546448315136258843817365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159395264420181678458423153 119546448315136258843817365)
        ·
          refine ⟨5603739764772012133303939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119546448315136258843817365 5603739764772012133303939)
          ·
            refine ⟨8405609647158018199955909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603739764772012133303939 8405609647158018199955909)
            ·
              refine ⟨1576051808842128412491733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8405609647158018199955909 1576051808842128412491733)
              ·
                refine ⟨36938714269737384667775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1576051808842128412491733 36938714269737384667775)
                ·
                  rfl

theorem cell23_1942323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 7].length) (baseStart_1942323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942323 prefixEnd_1942323 := by exact prefixLift 1942323
  have htrace : WordTrace (prefixWord ++ tailWord_1942323) baseStart_1942323 baseEnd_1942323 := by
    simpa [prefixWord, tailWord_1942323, baseEnd_1942323] using wordTrace_append hprefix tailTrace_1942323
  have hstable : (prefixWord ++ tailWord_1942323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942323).length < 2 ^ (prefixWord ++ tailWord_1942323).sum := by decide
  have hdescent : baseEnd_1942323 < baseStart_1942323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942337 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1942337 : Nat := 118140960795 + 1942337 * 2 ^ 59
def prefixEnd_1942337 : Nat := 4983230072969 + 3 ^ 40 * 1942337 * 2
def baseEnd_1942337 : Nat := 997352474012072331254861

theorem tailTrace_1942337 : CollatzResearch.WordTrace tailWord_1942337 prefixEnd_1942337 997352474012072331254861 := by
  unfold tailWord_1942337
  simp only [CollatzResearch.WordTrace]
  refine ⟨70842850364252248594753265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47228566909501499063168843 70842850364252248594753265)
  ·
    refine ⟨53132137773189186446064949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70842850364252248594753265 53132137773189186446064949)
    ·
      refine ⟨4981137916236486229318589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53132137773189186446064949 4981137916236486229318589)
      ·
        refine ⟨1867926718588682335994471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4981137916236486229318589 1867926718588682335994471)
        ·
          refine ⟨2801890077883023503991707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867926718588682335994471 2801890077883023503991707)
          ·
            refine ⟨4202835116824535255987561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2801890077883023503991707 4202835116824535255987561)
            ·
              refine ⟨3152126337618401441990671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4202835116824535255987561 3152126337618401441990671)
              ·
                refine ⟨4728189506427602162986007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3152126337618401441990671 4728189506427602162986007)
                ·
                  refine ⟨7092284259641403244479011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4728189506427602162986007 7092284259641403244479011)
                  ·
                    refine ⟨10638426389462104866718517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7092284259641403244479011 10638426389462104866718517)
                    ·
                      refine ⟨997352474012072331254861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10638426389462104866718517 997352474012072331254861)
                      ·
                        rfl

theorem cell23_1942337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1942337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942337 prefixEnd_1942337 := by exact prefixLift 1942337
  have htrace : WordTrace (prefixWord ++ tailWord_1942337) baseStart_1942337 baseEnd_1942337 := by
    simpa [prefixWord, tailWord_1942337, baseEnd_1942337] using wordTrace_append hprefix tailTrace_1942337
  have hstable : (prefixWord ++ tailWord_1942337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942337).length < 2 ^ (prefixWord ++ tailWord_1942337).sum := by decide
  have hdescent : baseEnd_1942337 < baseStart_1942337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942393 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1942393 : Nat := 118140960795 + 1942393 * 2 ^ 59
def prefixEnd_1942393 : Nat := 4983230072969 + 3 ^ 40 * 1942393 * 2
def baseEnd_1942393 : Nat := 997381228928724112154603

theorem tailTrace_1942393 : CollatzResearch.WordTrace tailWord_1942393 prefixEnd_1942393 997381228928724112154603 := by
  unfold tailWord_1942393
  simp only [CollatzResearch.WordTrace]
  refine ⟨70844892852049370158791833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47229928568032913439194555 70844892852049370158791833)
  ·
    refine ⟨53133669639037027619093875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70844892852049370158791833 53133669639037027619093875)
    ·
      refine ⟨79700504458555541428640813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53133669639037027619093875 79700504458555541428640813)
      ·
        refine ⟨29887689171958328035740305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79700504458555541428640813 29887689171958328035740305)
        ·
          refine ⟨22415766878968746026805229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29887689171958328035740305 22415766878968746026805229)
          ·
            refine ⟨8405912579613279760051961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22415766878968746026805229 8405912579613279760051961)
            ·
              refine ⟨6304434434709959820038971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8405912579613279760051961 6304434434709959820038971)
              ·
                refine ⟨9456651652064939730058457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304434434709959820038971 9456651652064939730058457)
                ·
                  refine ⟨7092488739048704797543843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9456651652064939730058457 7092488739048704797543843)
                  ·
                    refine ⟨10638733108573057196315765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7092488739048704797543843 10638733108573057196315765)
                    ·
                      refine ⟨997381228928724112154603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10638733108573057196315765 997381228928724112154603)
                      ·
                        rfl

theorem cell23_1942393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1942393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942393 prefixEnd_1942393 := by exact prefixLift 1942393
  have htrace : WordTrace (prefixWord ++ tailWord_1942393) baseStart_1942393 baseEnd_1942393 := by
    simpa [prefixWord, tailWord_1942393, baseEnd_1942393] using wordTrace_append hprefix tailTrace_1942393
  have hstable : (prefixWord ++ tailWord_1942393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942393).length < 2 ^ (prefixWord ++ tailWord_1942393).sum := by decide
  have hdescent : baseEnd_1942393 < baseStart_1942393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942402 : List Nat := [3, 4, 2, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_1942402 : Nat := 118140960795 + 1942402 * 2 ^ 59
def prefixEnd_1942402 : Nat := 4983230072969 + 3 ^ 40 * 1942402 * 2
def baseEnd_1942402 : Nat := 997385850254614576942063

theorem tailTrace_1942402 : CollatzResearch.WordTrace tailWord_1942402 prefixEnd_1942402 997385850254614576942063 := by
  unfold tailWord_1942402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17711305277254191173967365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47230147406011176463912973 17711305277254191173967365)
  ·
    refine ⟨3320869739485160845118881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17711305277254191173967365 3320869739485160845118881)
    ·
      refine ⟨2490652304613870633839161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3320869739485160845118881 2490652304613870633839161)
      ·
        refine ⟨1867989228460402975379371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2490652304613870633839161 1867989228460402975379371)
        ·
          refine ⟨2801983842690604463069057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867989228460402975379371 2801983842690604463069057)
          ·
            refine ⟨2101487882017953347301793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2801983842690604463069057 2101487882017953347301793)
            ·
              refine ⟨1576115911513465010476345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101487882017953347301793 1576115911513465010476345)
              ·
                refine ⟨1182086933635098757857259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1576115911513465010476345 1182086933635098757857259)
                ·
                  refine ⟨1773130400452648136785889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182086933635098757857259 1773130400452648136785889)
                  ·
                    refine ⟨1329847800339486102589417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1773130400452648136785889 1329847800339486102589417)
                    ·
                      refine ⟨997385850254614576942063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329847800339486102589417 997385850254614576942063)
                      ·
                        rfl

theorem cell23_1942402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_1942402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942402 prefixEnd_1942402 := by exact prefixLift 1942402
  have htrace : WordTrace (prefixWord ++ tailWord_1942402) baseStart_1942402 baseEnd_1942402 := by
    simpa [prefixWord, tailWord_1942402, baseEnd_1942402] using wordTrace_append hprefix tailTrace_1942402
  have hstable : (prefixWord ++ tailWord_1942402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942402).length < 2 ^ (prefixWord ++ tailWord_1942402).sum := by decide
  have hdescent : baseEnd_1942402 < baseStart_1942402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942403 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 4]
def baseStart_1942403 : Nat := 118140960795 + 1942403 * 2 ^ 59
def prefixEnd_1942403 : Nat := 4983230072969 + 3 ^ 40 * 1942403 * 2
def baseEnd_1942403 : Nat := 997386363735269073029557

theorem tailTrace_1942403 : CollatzResearch.WordTrace tailWord_1942403 prefixEnd_1942403 997386363735269073029557 := by
  unfold tailWord_1942403
  simp only [CollatzResearch.WordTrace]
  refine ⟨70845257582013141866655863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47230171721342094577770575 70845257582013141866655863)
  ·
    refine ⟨106267886373019712799983795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70845257582013141866655863 106267886373019712799983795)
    ·
      refine ⟨159401829559529569199975693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106267886373019712799983795 159401829559529569199975693)
      ·
        refine ⟨59775686084823588449990885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159401829559529569199975693 59775686084823588449990885)
        ·
          refine ⟨11207941140904422834373291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59775686084823588449990885 11207941140904422834373291)
          ·
            refine ⟨16811911711356634251559937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11207941140904422834373291 16811911711356634251559937)
            ·
              refine ⟨12608933783517475688669953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16811911711356634251559937 12608933783517475688669953)
              ·
                refine ⟨9456700337638106766502465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12608933783517475688669953 9456700337638106766502465)
                ·
                  refine ⟨7092525253228580074876849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9456700337638106766502465 7092525253228580074876849)
                  ·
                    refine ⟨5319393939921435056157637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7092525253228580074876849 5319393939921435056157637)
                    ·
                      refine ⟨997386363735269073029557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5319393939921435056157637 997386363735269073029557)
                      ·
                        rfl

theorem cell23_1942403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_1942403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942403 prefixEnd_1942403 := by exact prefixLift 1942403
  have htrace : WordTrace (prefixWord ++ tailWord_1942403) baseStart_1942403 baseEnd_1942403 := by
    simpa [prefixWord, tailWord_1942403, baseEnd_1942403] using wordTrace_append hprefix tailTrace_1942403
  have hstable : (prefixWord ++ tailWord_1942403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942403).length < 2 ^ (prefixWord ++ tailWord_1942403).sum := by decide
  have hdescent : baseEnd_1942403 < baseStart_1942403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942410 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1942410 : Nat := 118140960795 + 1942410 * 2 ^ 59
def prefixEnd_1942410 : Nat := 4983230072969 + 3 ^ 40 * 1942410 * 2
def baseEnd_1942410 : Nat := 997389958099850545642025

theorem tailTrace_1942410 : CollatzResearch.WordTrace tailWord_1942410 prefixEnd_1942410 997389958099850545642025 := by
  unfold tailWord_1942410
  simp only [CollatzResearch.WordTrace]
  refine ⟨17711378223246945515540171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47230341928658521374773789 17711378223246945515540171)
  ·
    refine ⟨26567067334870418273310257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17711378223246945515540171 26567067334870418273310257)
    ·
      refine ⟨19925300501152813704982693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26567067334870418273310257 19925300501152813704982693)
      ·
        refine ⟨3735993843966152569684255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19925300501152813704982693 3735993843966152569684255)
        ·
          refine ⟨5603990765949228854526383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3735993843966152569684255 5603990765949228854526383)
          ·
            refine ⟨8405986148923843281789575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5603990765949228854526383 8405986148923843281789575)
            ·
              refine ⟨12608979223385764922684363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8405986148923843281789575 12608979223385764922684363)
              ·
                refine ⟨18913468835078647384026545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12608979223385764922684363 18913468835078647384026545)
                ·
                  refine ⟨14185101626308985538019909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18913468835078647384026545 14185101626308985538019909)
                  ·
                    refine ⟨2659706554932934788378733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14185101626308985538019909 2659706554932934788378733)
                    ·
                      refine ⟨997389958099850545642025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2659706554932934788378733 997389958099850545642025)
                      ·
                        rfl

theorem cell23_1942410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1942410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942410 prefixEnd_1942410 := by exact prefixLift 1942410
  have htrace : WordTrace (prefixWord ++ tailWord_1942410) baseStart_1942410 baseEnd_1942410 := by
    simpa [prefixWord, tailWord_1942410, baseEnd_1942410] using wordTrace_append hprefix tailTrace_1942410
  have hstable : (prefixWord ++ tailWord_1942410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942410).length < 2 ^ (prefixWord ++ tailWord_1942410).sum := by decide
  have hdescent : baseEnd_1942410 < baseStart_1942410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942420 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1942420 : Nat := 118140960795 + 1942420 * 2 ^ 59
def prefixEnd_1942420 : Nat := 4983230072969 + 3 ^ 40 * 1942420 * 2
def baseEnd_1942420 : Nat := 997395092906395506516979

theorem tailTrace_1942420 : CollatzResearch.WordTrace tailWord_1942420 prefixEnd_1942420 997395092906395506516979 := by
  unfold tailWord_1942420
  simp only [CollatzResearch.WordTrace]
  refine ⟨35422938811475776885012357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47230585081967702513349809 35422938811475776885012357)
  ·
    refine ⟨6641801027151708165939817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35422938811475776885012357 6641801027151708165939817)
    ·
      refine ⟨4981350770363781124454863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6641801027151708165939817 4981350770363781124454863)
      ·
        refine ⟨7472026155545671686682295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4981350770363781124454863 7472026155545671686682295)
        ·
          refine ⟨11208039233318507530023443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7472026155545671686682295 11208039233318507530023443)
          ·
            refine ⟨16812058849977761295035165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11208039233318507530023443 16812058849977761295035165)
            ·
              refine ⟨6304522068741660485638187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16812058849977761295035165 6304522068741660485638187)
              ·
                refine ⟨9456783103112490728457281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6304522068741660485638187 9456783103112490728457281)
                ·
                  refine ⟨7092587327334368046342961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9456783103112490728457281 7092587327334368046342961)
                  ·
                    refine ⟨5319440495500776034757221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7092587327334368046342961 5319440495500776034757221)
                    ·
                      refine ⟨997395092906395506516979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5319440495500776034757221 997395092906395506516979)
                      ·
                        rfl

theorem cell23_1942420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1942420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942420 prefixEnd_1942420 := by exact prefixLift 1942420
  have htrace : WordTrace (prefixWord ++ tailWord_1942420) baseStart_1942420 baseEnd_1942420 := by
    simpa [prefixWord, tailWord_1942420, baseEnd_1942420] using wordTrace_append hprefix tailTrace_1942420
  have hstable : (prefixWord ++ tailWord_1942420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942420).length < 2 ^ (prefixWord ++ tailWord_1942420).sum := by decide
  have hdescent : baseEnd_1942420 < baseStart_1942420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942445 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_1942445 : Nat := 118140960795 + 1942445 * 2 ^ 59
def prefixEnd_1942445 : Nat := 4983230072969 + 3 ^ 40 * 1942445 * 2
def baseEnd_1942445 : Nat := 997407929922757908704365

theorem tailTrace_1942445 : CollatzResearch.WordTrace tailWord_1942445 prefixEnd_1942445 997407929922757908704365 := by
  unfold tailWord_1942445
  simp only [CollatzResearch.WordTrace]
  refine ⟨70846789447860983039684789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47231192965240655359789859 70846789447860983039684789)
  ·
    refine ⟨6641886510736967159970449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70846789447860983039684789 6641886510736967159970449)
    ·
      refine ⟨4981414883052725369977837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6641886510736967159970449 4981414883052725369977837)
      ·
        refine ⟨1868030581144772013741689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4981414883052725369977837 1868030581144772013741689)
        ·
          refine ⟨1401022935858579010306267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1868030581144772013741689 1401022935858579010306267)
          ·
            refine ⟨2101534403787868515459401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401022935858579010306267 2101534403787868515459401)
            ·
              refine ⟨1576150802840901386594551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2101534403787868515459401 1576150802840901386594551)
              ·
                refine ⟨2364226204261352079891827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576150802840901386594551 2364226204261352079891827)
                ·
                  refine ⟨3546339306392028119837741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364226204261352079891827 3546339306392028119837741)
                  ·
                    refine ⟨1329877239897010544939153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3546339306392028119837741 1329877239897010544939153)
                    ·
                      refine ⟨997407929922757908704365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329877239897010544939153 997407929922757908704365)
                      ·
                        rfl

theorem cell23_1942445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_1942445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942445 prefixEnd_1942445 := by exact prefixLift 1942445
  have htrace : WordTrace (prefixWord ++ tailWord_1942445) baseStart_1942445 baseEnd_1942445 := by
    simpa [prefixWord, tailWord_1942445, baseEnd_1942445] using wordTrace_append hprefix tailTrace_1942445
  have hstable : (prefixWord ++ tailWord_1942445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942445).length < 2 ^ (prefixWord ++ tailWord_1942445).sum := by decide
  have hdescent : baseEnd_1942445 < baseStart_1942445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942514 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1942514 : Nat := 118140960795 + 1942514 * 2 ^ 59
def prefixEnd_1942514 : Nat := 4983230072969 + 3 ^ 40 * 1942514 * 2
def baseEnd_1942514 : Nat := 997443360087918138741547

theorem tailTrace_1942514 : CollatzResearch.WordTrace tailWord_1942514 prefixEnd_1942514 997443360087918138741547 := by
  unfold tailWord_1942514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17712326521152751955986649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47232870723074005215964397 17712326521152751955986649)
  ·
    refine ⟨13284244890864563966989987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17712326521152751955986649 13284244890864563966989987)
    ·
      refine ⟨19926367336296845950484981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13284244890864563966989987 19926367336296845950484981)
      ·
        refine ⟨1868096937777829307857967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19926367336296845950484981 1868096937777829307857967)
        ·
          refine ⟨2802145406666743961786951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868096937777829307857967 2802145406666743961786951)
          ·
            refine ⟨4203218110000115942680427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802145406666743961786951 4203218110000115942680427)
            ·
              refine ⟨6304827165000173914020641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203218110000115942680427 6304827165000173914020641)
              ·
                refine ⟨4728620373750130435515481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6304827165000173914020641 4728620373750130435515481)
                ·
                  refine ⟨3546465280312597826636611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4728620373750130435515481 3546465280312597826636611)
                  ·
                    refine ⟨5319697920468896739954917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3546465280312597826636611 5319697920468896739954917)
                    ·
                      refine ⟨997443360087918138741547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5319697920468896739954917 997443360087918138741547)
                      ·
                        rfl

theorem cell23_1942514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1942514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942514 prefixEnd_1942514 := by exact prefixLift 1942514
  have htrace : WordTrace (prefixWord ++ tailWord_1942514) baseStart_1942514 baseEnd_1942514 := by
    simpa [prefixWord, tailWord_1942514, baseEnd_1942514] using wordTrace_append hprefix tailTrace_1942514
  have hstable : (prefixWord ++ tailWord_1942514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942514).length < 2 ^ (prefixWord ++ tailWord_1942514).sum := by decide
  have hdescent : baseEnd_1942514 < baseStart_1942514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942574 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_1942574 : Nat := 118140960795 + 1942574 * 2 ^ 59
def prefixEnd_1942574 : Nat := 4983230072969 + 3 ^ 40 * 1942574 * 2
def baseEnd_1942574 : Nat := 997474168927187903991271

theorem tailTrace_1942574 : CollatzResearch.WordTrace tailWord_1942574 prefixEnd_1942574 997474168927187903991271 := by
  unfold tailWord_1942574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856436808049204758891347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47234329642929092047420517 8856436808049204758891347)
  ·
    refine ⟨13284655212073807138337021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8856436808049204758891347 13284655212073807138337021)
    ·
      refine ⟨4981745704527677676876383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13284655212073807138337021 4981745704527677676876383)
      ·
        refine ⟨7472618556791516515314575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4981745704527677676876383 7472618556791516515314575)
        ·
          refine ⟨11208927835187274772971863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7472618556791516515314575 11208927835187274772971863)
          ·
            refine ⟨16813391752780912159457795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11208927835187274772971863 16813391752780912159457795)
            ·
              refine ⟨25220087629171368239186693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16813391752780912159457795 25220087629171368239186693)
              ·
                refine ⟨4728766430469631544847505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25220087629171368239186693 4728766430469631544847505)
                ·
                  refine ⟨3546574822852223658635629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4728766430469631544847505 3546574822852223658635629)
                  ·
                    refine ⟨1329965558569583871988361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3546574822852223658635629 1329965558569583871988361)
                    ·
                      refine ⟨997474168927187903991271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1329965558569583871988361 997474168927187903991271)
                      ·
                        rfl

theorem cell23_1942574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_1942574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942574 prefixEnd_1942574 := by exact prefixLift 1942574
  have htrace : WordTrace (prefixWord ++ tailWord_1942574) baseStart_1942574 baseEnd_1942574 := by
    simpa [prefixWord, tailWord_1942574, baseEnd_1942574] using wordTrace_append hprefix tailTrace_1942574
  have hstable : (prefixWord ++ tailWord_1942574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942574).length < 2 ^ (prefixWord ++ tailWord_1942574).sum := by decide
  have hdescent : baseEnd_1942574 < baseStart_1942574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942597 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 2, 4]
def baseStart_1942597 : Nat := 118140960795 + 1942597 * 2 ^ 59
def prefixEnd_1942597 : Nat := 4983230072969 + 3 ^ 40 * 1942597 * 2
def baseEnd_1942597 : Nat := 332495326327413771334555

theorem tailTrace_1942597 : CollatzResearch.WordTrace tailWord_1942597 prefixEnd_1942597 332495326327413771334555 := by
  unfold tailWord_1942597
  simp only [CollatzResearch.WordTrace]
  refine ⟨70852333343310312999218045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47234888895540208666145363 70852333343310312999218045)
  ·
    refine ⟨26569625003741367374706767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70852333343310312999218045 26569625003741367374706767)
    ·
      refine ⟨39854437505612051062060151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26569625003741367374706767 39854437505612051062060151)
      ·
        refine ⟨59781656258418076593090227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39854437505612051062060151 59781656258418076593090227)
        ·
          refine ⟨89672484387627114889635341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59781656258418076593090227 89672484387627114889635341)
          ·
            refine ⟨33627181645360168083613253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89672484387627114889635341 33627181645360168083613253)
            ·
              refine ⟨6305096558505031515677485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33627181645360168083613253 6305096558505031515677485)
              ·
                refine ⟨2364411209439386818379057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6305096558505031515677485 2364411209439386818379057)
                ·
                  refine ⟨1773308407079540113784293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2364411209439386818379057 1773308407079540113784293)
                  ·
                    refine ⟨332495326327413771334555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1773308407079540113784293 332495326327413771334555)
                    ·
                      rfl

theorem cell23_1942597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_1942597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942597 prefixEnd_1942597 := by exact prefixLift 1942597
  have htrace : WordTrace (prefixWord ++ tailWord_1942597) baseStart_1942597 baseEnd_1942597 := by
    simpa [prefixWord, tailWord_1942597, baseEnd_1942597] using wordTrace_append hprefix tailTrace_1942597
  have hstable : (prefixWord ++ tailWord_1942597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942597).length < 2 ^ (prefixWord ++ tailWord_1942597).sum := by decide
  have hdescent : baseEnd_1942597 < baseStart_1942597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942621 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1942621 : Nat := 118140960795 + 1942621 * 2 ^ 59
def prefixEnd_1942621 : Nat := 4983230072969 + 3 ^ 40 * 1942621 * 2
def baseEnd_1942621 : Nat := 997498302517949220103555

theorem tailTrace_1942621 : CollatzResearch.WordTrace tailWord_1942621 prefixEnd_1942621 997498302517949220103555 := by
  unfold tailWord_1942621
  simp only [CollatzResearch.WordTrace]
  refine ⟨70853208695223365098091717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47235472463482243398727811 70853208695223365098091717)
  ·
    refine ⟨13284976630354380955892197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70853208695223365098091717 13284976630354380955892197)
    ·
      refine ⟨2490933118191446429229787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13284976630354380955892197 2490933118191446429229787)
      ·
        refine ⟨3736399677287169643844681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490933118191446429229787 3736399677287169643844681)
        ·
          refine ⟨2802299757965377232883511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3736399677287169643844681 2802299757965377232883511)
          ·
            refine ⟨4203449636948065849325267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802299757965377232883511 4203449636948065849325267)
            ·
              refine ⟨6305174455422098773987901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4203449636948065849325267 6305174455422098773987901)
              ·
                refine ⟨2364440420783287040245463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6305174455422098773987901 2364440420783287040245463)
                ·
                  refine ⟨3546660631174930560368195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364440420783287040245463 3546660631174930560368195)
                  ·
                    refine ⟨5319990946762395840552293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3546660631174930560368195 5319990946762395840552293)
                    ·
                      refine ⟨997498302517949220103555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5319990946762395840552293 997498302517949220103555)
                      ·
                        rfl

theorem cell23_1942621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1942621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942621 prefixEnd_1942621 := by exact prefixLift 1942621
  have htrace : WordTrace (prefixWord ++ tailWord_1942621) baseStart_1942621 baseEnd_1942621 := by
    simpa [prefixWord, tailWord_1942621, baseEnd_1942621] using wordTrace_append hprefix tailTrace_1942621
  have hstable : (prefixWord ++ tailWord_1942621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942621).length < 2 ^ (prefixWord ++ tailWord_1942621).sum := by decide
  have hdescent : baseEnd_1942621 < baseStart_1942621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942638 : List Nat := [4, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_1942638 : Nat := 118140960795 + 1942638 * 2 ^ 59
def prefixEnd_1942638 : Nat := 4983230072969 + 3 ^ 40 * 1942638 * 2
def baseEnd_1942638 : Nat := 997507031689075653590977

theorem tailTrace_1942638 : CollatzResearch.WordTrace tailWord_1942638 prefixEnd_1942638 997507031689075653590977 := by
  unfold tailWord_1942638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8856728592020222125182571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47235885824107851334307045 8856728592020222125182571)
  ·
    refine ⟨13285092888030333187773857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8856728592020222125182571 13285092888030333187773857)
    ·
      refine ⟨9963819666022749890830393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13285092888030333187773857 9963819666022749890830393)
      ·
        refine ⟨7472864749517062418122795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9963819666022749890830393 7472864749517062418122795)
        ·
          refine ⟨11209297124275593627184193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7472864749517062418122795 11209297124275593627184193)
          ·
            refine ⟨8406972843206695220388145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11209297124275593627184193 8406972843206695220388145)
            ·
              refine ⟨6305229632405021415291109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8406972843206695220388145 6305229632405021415291109)
              ·
                refine ⟨1182230556075941515367083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6305229632405021415291109 1182230556075941515367083)
                ·
                  refine ⟨1773345834113912273050625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182230556075941515367083 1773345834113912273050625)
                  ·
                    refine ⟨1330009375585434204787969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1773345834113912273050625 1330009375585434204787969)
                    ·
                      refine ⟨997507031689075653590977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330009375585434204787969 997507031689075653590977)
                      ·
                        rfl

theorem cell23_1942638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_1942638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942638 prefixEnd_1942638 := by exact prefixLift 1942638
  have htrace : WordTrace (prefixWord ++ tailWord_1942638) baseStart_1942638 baseEnd_1942638 := by
    simpa [prefixWord, tailWord_1942638, baseEnd_1942638] using wordTrace_append hprefix tailTrace_1942638
  have hstable : (prefixWord ++ tailWord_1942638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942638).length < 2 ^ (prefixWord ++ tailWord_1942638).sum := by decide
  have hdescent : baseEnd_1942638 < baseStart_1942638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942700 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 7]
def baseStart_1942700 : Nat := 118140960795 + 1942700 * 2 ^ 59
def prefixEnd_1942700 : Nat := 4983230072969 + 3 ^ 40 * 1942700 * 2
def baseEnd_1942700 : Nat := 110837651943294934557299

theorem tailTrace_1942700 : CollatzResearch.WordTrace tailWord_1942700 prefixEnd_1942700 110837651943294934557299 := by
  unfold tailWord_1942700
  simp only [CollatzResearch.WordTrace]
  refine ⟨35428045030968580795108777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47237393374624774393478369 35428045030968580795108777)
  ·
    refine ⟨26571033773226435596331583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35428045030968580795108777 26571033773226435596331583)
    ·
      refine ⟨39856550659839653394497375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26571033773226435596331583 39856550659839653394497375)
      ·
        refine ⟨59784825989759480091746063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39856550659839653394497375 59784825989759480091746063)
        ·
          refine ⟨89677238984639220137619095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59784825989759480091746063 89677238984639220137619095)
          ·
            refine ⟨134515858476958830206428643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89677238984639220137619095 134515858476958830206428643)
            ·
              refine ⟨201773787715438245309642965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134515858476958830206428643 201773787715438245309642965)
              ·
                refine ⟨4729073149580583874444757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 201773787715438245309642965 4729073149580583874444757)
                ·
                  refine ⟨110837651943294934557299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4729073149580583874444757 110837651943294934557299)
                  ·
                    rfl

theorem cell23_1942700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_1942700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942700 prefixEnd_1942700 := by exact prefixLift 1942700
  have htrace : WordTrace (prefixWord ++ tailWord_1942700) baseStart_1942700 baseEnd_1942700 := by
    simpa [prefixWord, tailWord_1942700, baseEnd_1942700] using wordTrace_append hprefix tailTrace_1942700
  have hstable : (prefixWord ++ tailWord_1942700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942700).length < 2 ^ (prefixWord ++ tailWord_1942700).sum := by decide
  have hdescent : baseEnd_1942700 < baseStart_1942700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942711 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 2, 2, 2]
def baseStart_1942711 : Nat := 118140960795 + 1942711 * 2 ^ 59
def prefixEnd_1942711 : Nat := 4983230072969 + 3 ^ 40 * 1942711 * 2
def baseEnd_1942711 : Nat := 997544515776853867978141

theorem tailTrace_1942711 : CollatzResearch.WordTrace tailWord_1942711 prefixEnd_1942711 997544515776853867978141 := by
  unfold tailWord_1942711
  simp only [CollatzResearch.WordTrace]
  refine ⟨70856491264897310468867987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47237660843264873645911991 70856491264897310468867987)
  ·
    refine ⟨106284736897345965703301981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70856491264897310468867987 106284736897345965703301981)
    ·
      refine ⟨39856776336504737138738243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106284736897345965703301981 39856776336504737138738243)
      ·
        refine ⟨59785164504757105708107365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39856776336504737138738243 59785164504757105708107365)
        ·
          refine ⟨11209718344641957320270131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59785164504757105708107365 11209718344641957320270131)
          ·
            refine ⟨16814577516962935980405197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11209718344641957320270131 16814577516962935980405197)
            ·
              refine ⟨6305466568861100992651949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16814577516962935980405197 6305466568861100992651949)
              ·
                refine ⟨2364549963322912872244481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6305466568861100992651949 2364549963322912872244481)
                ·
                  refine ⟨1773412472492184654183361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2364549963322912872244481 1773412472492184654183361)
                  ·
                    refine ⟨1330059354369138490637521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1773412472492184654183361 1330059354369138490637521)
                    ·
                      refine ⟨997544515776853867978141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330059354369138490637521 997544515776853867978141)
                      ·
                        rfl

theorem cell23_1942711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 2, 2].length) (baseStart_1942711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942711 prefixEnd_1942711 := by exact prefixLift 1942711
  have htrace : WordTrace (prefixWord ++ tailWord_1942711) baseStart_1942711 baseEnd_1942711 := by
    simpa [prefixWord, tailWord_1942711, baseEnd_1942711] using wordTrace_append hprefix tailTrace_1942711
  have hstable : (prefixWord ++ tailWord_1942711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942711).length < 2 ^ (prefixWord ++ tailWord_1942711).sum := by decide
  have hdescent : baseEnd_1942711 < baseStart_1942711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942807 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 8]
def baseStart_1942807 : Nat := 118140960795 + 1942807 * 2 ^ 59
def prefixEnd_1942807 : Nat := 4983230072969 + 3 ^ 40 * 1942807 * 2
def baseEnd_1942807 : Nat := 110843756657742832486411

theorem tailTrace_1942807 : CollatzResearch.WordTrace tailWord_1942807 prefixEnd_1942807 110843756657742832486411 := by
  unfold tailWord_1942807
  simp only [CollatzResearch.WordTrace]
  refine ⟨70859992672549518864362675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47239995115033012576241783 70859992672549518864362675)
  ·
    refine ⟨106289989008824278296544013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70859992672549518864362675 106289989008824278296544013)
    ·
      refine ⟨39858745878309104361204005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106289989008824278296544013 39858745878309104361204005)
      ·
        refine ⟨7473514852182957067725751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39858745878309104361204005 7473514852182957067725751)
        ·
          refine ⟨11210272278274435601588627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7473514852182957067725751 11210272278274435601588627)
          ·
            refine ⟨16815408417411653402382941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11210272278274435601588627 16815408417411653402382941)
            ·
              refine ⟨6305778156529370025893603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16815408417411653402382941 6305778156529370025893603)
              ·
                refine ⟨9458667234794055038840405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6305778156529370025893603 9458667234794055038840405)
                ·
                  refine ⟨110843756657742832486411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9458667234794055038840405 110843756657742832486411)
                  ·
                    rfl

theorem cell23_1942807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 8].length) (baseStart_1942807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942807 prefixEnd_1942807 := by exact prefixLift 1942807
  have htrace : WordTrace (prefixWord ++ tailWord_1942807) baseStart_1942807 baseEnd_1942807 := by
    simpa [prefixWord, tailWord_1942807, baseEnd_1942807] using wordTrace_append hprefix tailTrace_1942807
  have hstable : (prefixWord ++ tailWord_1942807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942807).length < 2 ^ (prefixWord ++ tailWord_1942807).sum := by decide
  have hdescent : baseEnd_1942807 < baseStart_1942807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942888 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1942888 : Nat := 118140960795 + 1942888 * 2 ^ 59
def prefixEnd_1942888 : Nat := 4983230072969 + 3 ^ 40 * 1942888 * 2
def baseEnd_1942888 : Nat := 332545133950899891821609

theorem tailTrace_1942888 : CollatzResearch.WordTrace tailWord_1942888 prefixEnd_1942888 332545133950899891821609 := by
  unfold tailWord_1942888
  simp only [CollatzResearch.WordTrace]
  refine ⟨35431473492628034849030659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47241964656837379798707545 35431473492628034849030659)
  ·
    refine ⟨53147210238942052273545989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35431473492628034849030659 53147210238942052273545989)
    ·
      refine ⟨9965101919801634801289873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53147210238942052273545989 9965101919801634801289873)
      ·
        refine ⟨7473826439851226100967405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9965101919801634801289873 7473826439851226100967405)
        ·
          refine ⟨2802684914944209787862777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7473826439851226100967405 2802684914944209787862777)
          ·
            refine ⟨2102013686208157340897083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2802684914944209787862777 2102013686208157340897083)
            ·
              refine ⟨3153020529312236011345625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102013686208157340897083 3153020529312236011345625)
              ·
                refine ⟨2364765396984177008509219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3153020529312236011345625 2364765396984177008509219)
                ·
                  refine ⟨3547148095476265512763829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2364765396984177008509219 3547148095476265512763829)
                  ·
                    refine ⟨332545133950899891821609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3547148095476265512763829 332545133950899891821609)
                    ·
                      rfl

theorem cell23_1942888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1942888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942888 prefixEnd_1942888 := by exact prefixLift 1942888
  have htrace : WordTrace (prefixWord ++ tailWord_1942888) baseStart_1942888 baseEnd_1942888 := by
    simpa [prefixWord, tailWord_1942888, baseEnd_1942888] using wordTrace_append hprefix tailTrace_1942888
  have hstable : (prefixWord ++ tailWord_1942888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942888).length < 2 ^ (prefixWord ++ tailWord_1942888).sum := by decide
  have hdescent : baseEnd_1942888 < baseStart_1942888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942897 : List Nat := [1, 2, 2, 2, 1, 2, 4, 9]
def baseStart_1942897 : Nat := 118140960795 + 1942897 * 2 ^ 59
def prefixEnd_1942897 : Nat := 4983230072969 + 3 ^ 40 * 1942897 * 2
def baseEnd_1942897 : Nat := 36949630488095931120455

theorem tailTrace_1942897 : CollatzResearch.WordTrace tailWord_1942897 prefixEnd_1942897 36949630488095931120455 := by
  unfold tailWord_1942897
  simp only [CollatzResearch.WordTrace]
  refine ⟨70863275242223464235138945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47242183494815642823425963 70863275242223464235138945)
  ·
    refine ⟨53147456431667598176354209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70863275242223464235138945 53147456431667598176354209)
    ·
      refine ⟨39860592323750698632265657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53147456431667598176354209 39860592323750698632265657)
      ·
        refine ⟨29895444242813023974199243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39860592323750698632265657 29895444242813023974199243)
        ·
          refine ⟨44843166364219535961298865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29895444242813023974199243 44843166364219535961298865)
          ·
            refine ⟨33632374773164651970974149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44843166364219535961298865 33632374773164651970974149)
            ·
              refine ⟨6306070269968372244557653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33632374773164651970974149 6306070269968372244557653)
              ·
                refine ⟨36949630488095931120455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6306070269968372244557653 36949630488095931120455)
                ·
                  rfl

theorem cell23_1942897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 9].length) (baseStart_1942897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942897 prefixEnd_1942897 := by exact prefixLift 1942897
  have htrace : WordTrace (prefixWord ++ tailWord_1942897) baseStart_1942897 baseEnd_1942897 := by
    simpa [prefixWord, tailWord_1942897, baseEnd_1942897] using wordTrace_append hprefix tailTrace_1942897
  have hstable : (prefixWord ++ tailWord_1942897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942897).length < 2 ^ (prefixWord ++ tailWord_1942897).sum := by decide
  have hdescent : baseEnd_1942897 < baseStart_1942897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942901 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1942901 : Nat := 118140960795 + 1942901 * 2 ^ 59
def prefixEnd_1942901 : Nat := 4983230072969 + 3 ^ 40 * 1942901 * 2
def baseEnd_1942901 : Nat := 332547359033736041534089

theorem tailTrace_1942901 : CollatzResearch.WordTrace tailWord_1942901 prefixEnd_1942901 332547359033736041534089 := by
  unfold tailWord_1942901
  simp only [CollatzResearch.WordTrace]
  refine ⟨70863421134208972918284557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47242280756139315278856371 70863421134208972918284557)
  ·
    refine ⟨26573782925328364844356709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70863421134208972918284557 26573782925328364844356709)
    ·
      refine ⟨4982584298499068408316883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26573782925328364844356709 4982584298499068408316883)
      ·
        refine ⟨7473876447748602612475325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4982584298499068408316883 7473876447748602612475325)
        ·
          refine ⟨2802703667905725979678247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7473876447748602612475325 2802703667905725979678247)
          ·
            refine ⟨4204055501858588969517371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802703667905725979678247 4204055501858588969517371)
            ·
              refine ⟨6306083252787883454276057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4204055501858588969517371 6306083252787883454276057)
              ·
                refine ⟨4729562439590912590707043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6306083252787883454276057 4729562439590912590707043)
                ·
                  refine ⟨7094343659386368886060565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729562439590912590707043 7094343659386368886060565)
                  ·
                    refine ⟨332547359033736041534089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7094343659386368886060565 332547359033736041534089)
                    ·
                      rfl

theorem cell23_1942901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1942901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942901 prefixEnd_1942901 := by exact prefixLift 1942901
  have htrace : WordTrace (prefixWord ++ tailWord_1942901) baseStart_1942901 baseEnd_1942901 := by
    simpa [prefixWord, tailWord_1942901, baseEnd_1942901] using wordTrace_append hprefix tailTrace_1942901
  have hstable : (prefixWord ++ tailWord_1942901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942901).length < 2 ^ (prefixWord ++ tailWord_1942901).sum := by decide
  have hdescent : baseEnd_1942901 < baseStart_1942901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942924 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 3, 3, 3]
def baseStart_1942924 : Nat := 118140960795 + 1942924 * 2 ^ 59
def prefixEnd_1942924 : Nat := 4983230072969 + 3 ^ 40 * 1942924 * 2
def baseEnd_1942924 : Nat := 997653887156261534614661

theorem tailTrace_1942924 : CollatzResearch.WordTrace tailWord_1942924 prefixEnd_1942924 997653887156261534614661 := by
  unfold tailWord_1942924
  simp only [CollatzResearch.WordTrace]
  refine ⟨35432130006562823923185913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47242840008750431897581217 35432130006562823923185913)
  ·
    refine ⟨26574097504922117942389435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35432130006562823923185913 26574097504922117942389435)
    ·
      refine ⟨39861146257383176913584153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26574097504922117942389435 39861146257383176913584153)
      ·
        refine ⟨29895859693037382685188115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39861146257383176913584153 29895859693037382685188115)
        ·
          refine ⟨44843789539556074027782173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29895859693037382685188115 44843789539556074027782173)
          ·
            refine ⟨16816421077333527760418315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44843789539556074027782173 16816421077333527760418315)
            ·
              refine ⟨25224631616000291640627473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16816421077333527760418315 25224631616000291640627473)
              ·
                refine ⟨18918473712000218730470605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25224631616000291640627473 18918473712000218730470605)
                ·
                  refine ⟨7094427642000082023926477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18918473712000218730470605 7094427642000082023926477)
                  ·
                    refine ⟨2660410365750030758972429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7094427642000082023926477 2660410365750030758972429)
                    ·
                      refine ⟨997653887156261534614661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2660410365750030758972429 997653887156261534614661)
                      ·
                        rfl

theorem cell23_1942924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_1942924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942924 prefixEnd_1942924 := by exact prefixLift 1942924
  have htrace : WordTrace (prefixWord ++ tailWord_1942924) baseStart_1942924 baseEnd_1942924 := by
    simpa [prefixWord, tailWord_1942924, baseEnd_1942924] using wordTrace_append hprefix tailTrace_1942924
  have hstable : (prefixWord ++ tailWord_1942924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942924).length < 2 ^ (prefixWord ++ tailWord_1942924).sum := by decide
  have hdescent : baseEnd_1942924 < baseStart_1942924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942941 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_1942941 : Nat := 118140960795 + 1942941 * 2 ^ 59
def prefixEnd_1942941 : Nat := 4983230072969 + 3 ^ 40 * 1942941 * 2
def baseEnd_1942941 : Nat := 997662616327387968102083

theorem tailTrace_1942941 : CollatzResearch.WordTrace tailWord_1942941 prefixEnd_1942941 997662616327387968102083 := by
  unfold tailWord_1942941
  simp only [CollatzResearch.WordTrace]
  refine ⟨70864880054064059749740677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47243253369376039833160451 70864880054064059749740677)
  ·
    refine ⟨13287165010137011203076377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70864880054064059749740677 13287165010137011203076377)
    ·
      refine ⟨9965373757602758402307283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13287165010137011203076377 9965373757602758402307283)
      ·
        refine ⟨14948060636404137603460925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9965373757602758402307283 14948060636404137603460925)
        ·
          refine ⟨5605522738651551601297847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14948060636404137603460925 5605522738651551601297847)
          ·
            refine ⟨8408284107977327401946771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5605522738651551601297847 8408284107977327401946771)
            ·
              refine ⟨12612426161965991102920157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8408284107977327401946771 12612426161965991102920157)
              ·
                refine ⟨4729659810737246663595059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12612426161965991102920157 4729659810737246663595059)
                ·
                  refine ⟨7094489716105869995392589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4729659810737246663595059 7094489716105869995392589)
                  ·
                    refine ⟨2660433643539701248272221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7094489716105869995392589 2660433643539701248272221)
                    ·
                      refine ⟨997662616327387968102083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2660433643539701248272221 997662616327387968102083)
                      ·
                        rfl

theorem cell23_1942941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_1942941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942941 prefixEnd_1942941 := by exact prefixLift 1942941
  have htrace : WordTrace (prefixWord ++ tailWord_1942941) baseStart_1942941 baseEnd_1942941 := by
    simpa [prefixWord, tailWord_1942941, baseEnd_1942941] using wordTrace_append hprefix tailTrace_1942941
  have hstable : (prefixWord ++ tailWord_1942941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942941).length < 2 ^ (prefixWord ++ tailWord_1942941).sum := by decide
  have hdescent : baseEnd_1942941 < baseStart_1942941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1942942 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_1942942 : Nat := 118140960795 + 1942942 * 2 ^ 59
def prefixEnd_1942942 : Nat := 4983230072969 + 3 ^ 40 * 1942942 * 2
def baseEnd_1942942 : Nat := 997663129808042464189579

theorem tailTrace_1942942 : CollatzResearch.WordTrace tailWord_1942942 prefixEnd_1942942 997663129808042464189579 := by
  unfold tailWord_1942942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8858114565882554615065885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47243277684706957947018053 8858114565882554615065885)
  ·
    refine ⟨3321792962205957980649707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8858114565882554615065885 3321792962205957980649707)
    ·
      refine ⟨4982689443308936970974561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3321792962205957980649707 4982689443308936970974561)
      ·
        refine ⟨3737017082481702728230921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4982689443308936970974561 3737017082481702728230921)
        ·
          refine ⟨2802762811861277046173191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3737017082481702728230921 2802762811861277046173191)
          ·
            refine ⟨4204144217791915569259787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2802762811861277046173191 4204144217791915569259787)
            ·
              refine ⟨6306216326687873353889681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4204144217791915569259787 6306216326687873353889681)
              ·
                refine ⟨4729662245015905015417261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6306216326687873353889681 4729662245015905015417261)
                ·
                  refine ⟨1773623341880964380781473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4729662245015905015417261 1773623341880964380781473)
                  ·
                    refine ⟨1330217506410723285586105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1773623341880964380781473 1330217506410723285586105)
                    ·
                      refine ⟨997663129808042464189579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330217506410723285586105 997663129808042464189579)
                      ·
                        rfl

theorem cell23_1942942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_1942942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1942942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1942942 prefixEnd_1942942 := by exact prefixLift 1942942
  have htrace : WordTrace (prefixWord ++ tailWord_1942942) baseStart_1942942 baseEnd_1942942 := by
    simpa [prefixWord, tailWord_1942942, baseEnd_1942942] using wordTrace_append hprefix tailTrace_1942942
  have hstable : (prefixWord ++ tailWord_1942942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1942942).length < 2 ^ (prefixWord ++ tailWord_1942942).sum := by decide
  have hdescent : baseEnd_1942942 < baseStart_1942942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1942942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943071 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 4]
def baseStart_1943071 : Nat := 118140960795 + 1943071 * 2 ^ 59
def prefixEnd_1943071 : Nat := 4983230072969 + 3 ^ 40 * 1943071 * 2
def baseEnd_1943071 : Nat := 997729368812472459476485

theorem tailTrace_1943071 : CollatzResearch.WordTrace tailWord_1943071 prefixEnd_1943071 997729368812472459476485 := by
  unfold tailWord_1943071
  simp only [CollatzResearch.WordTrace]
  refine ⟨70869621543593091951973067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47246414362395394634648711 70869621543593091951973067)
  ·
    refine ⟨106304432315389637927959601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70869621543593091951973067 106304432315389637927959601)
    ·
      refine ⟨79728324236542228445969701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106304432315389637927959601 79728324236542228445969701)
      ·
        refine ⟨14949060794351667833619319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79728324236542228445969701 14949060794351667833619319)
        ·
          refine ⟨22423591191527501750428979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14949060794351667833619319 22423591191527501750428979)
          ·
            refine ⟨33635386787291252625643469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22423591191527501750428979 33635386787291252625643469)
            ·
              refine ⟨12613270045234219734616301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33635386787291252625643469 12613270045234219734616301)
              ·
                refine ⟨4729976266962832400481113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12613270045234219734616301 4729976266962832400481113)
                ·
                  refine ⟨3547482200222124300360835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4729976266962832400481113 3547482200222124300360835)
                  ·
                    refine ⟨5321223300333186450541253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3547482200222124300360835 5321223300333186450541253)
                    ·
                      refine ⟨997729368812472459476485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5321223300333186450541253 997729368812472459476485)
                      ·
                        rfl

theorem cell23_1943071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_1943071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943071 prefixEnd_1943071 := by exact prefixLift 1943071
  have htrace : WordTrace (prefixWord ++ tailWord_1943071) baseStart_1943071 baseEnd_1943071 := by
    simpa [prefixWord, tailWord_1943071, baseEnd_1943071] using wordTrace_append hprefix tailTrace_1943071
  have hstable : (prefixWord ++ tailWord_1943071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943071).length < 2 ^ (prefixWord ++ tailWord_1943071).sum := by decide
  have hdescent : baseEnd_1943071 < baseStart_1943071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943132 : List Nat := [2, 2, 4, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1943132 : Nat := 118140960795 + 1943132 * 2 ^ 59
def prefixEnd_1943132 : Nat := 4983230072969 + 3 ^ 40 * 1943132 * 2
def baseEnd_1943132 : Nat := 332586897044132240271235

theorem tailTrace_1943132 : CollatzResearch.WordTrace tailWord_1943132 prefixEnd_1943132 332586897044132240271235 := by
  unfold tailWord_1943132
  simp only [CollatzResearch.WordTrace]
  refine ⟨35435923198186049684971825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47247897597581399579962433 35435923198186049684971825)
  ·
    refine ⟨26576942398639537263728869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35435923198186049684971825 26576942398639537263728869)
    ·
      refine ⟨4983176699744913236949163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26576942398639537263728869 4983176699744913236949163)
      ·
        refine ⟨7474765049617369855423745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4983176699744913236949163 7474765049617369855423745)
        ·
          refine ⟨5606073787213027391567809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7474765049617369855423745 5606073787213027391567809)
          ·
            refine ⟨4204555340409770543675857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5606073787213027391567809 4204555340409770543675857)
            ·
              refine ⟨3153416505307327907756893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4204555340409770543675857 3153416505307327907756893)
              ·
                refine ⟨1182531189490247965408835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3153416505307327907756893 1182531189490247965408835)
                ·
                  refine ⟨1773796784235371948113253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182531189490247965408835 1773796784235371948113253)
                  ·
                    refine ⟨332586897044132240271235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1773796784235371948113253 332586897044132240271235)
                    ·
                      rfl

theorem cell23_1943132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1943132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943132 prefixEnd_1943132 := by exact prefixLift 1943132
  have htrace : WordTrace (prefixWord ++ tailWord_1943132) baseStart_1943132 baseEnd_1943132 := by
    simpa [prefixWord, tailWord_1943132, baseEnd_1943132] using wordTrace_append hprefix tailTrace_1943132
  have hstable : (prefixWord ++ tailWord_1943132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943132).length < 2 ^ (prefixWord ++ tailWord_1943132).sum := by decide
  have hdescent : baseEnd_1943132 < baseStart_1943132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943148 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 4, 3, 2]
def baseStart_1943148 : Nat := 118140960795 + 1943148 * 2 ^ 59
def prefixEnd_1943148 : Nat := 4983230072969 + 3 ^ 40 * 1943148 * 2
def baseEnd_1943148 : Nat := 997768906822868658213631

theorem tailTrace_1943148 : CollatzResearch.WordTrace tailWord_1943148 prefixEnd_1943148 997768906822868658213631 := by
  unfold tailWord_1943148
  simp only [CollatzResearch.WordTrace]
  refine ⟨35436214982157067051263049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47248286642876089401684065 35436214982157067051263049)
  ·
    refine ⟨26577161236617800288447287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35436214982157067051263049 26577161236617800288447287)
    ·
      refine ⟨39865741854926700432670931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26577161236617800288447287 39865741854926700432670931)
      ·
        refine ⟨59798612782390050649006397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39865741854926700432670931 59798612782390050649006397)
        ·
          refine ⟨22424479793396268993377399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59798612782390050649006397 22424479793396268993377399)
          ·
            refine ⟨33636719690094403490066099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22424479793396268993377399 33636719690094403490066099)
            ·
              refine ⟨50455079535141605235099149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33636719690094403490066099 50455079535141605235099149)
              ·
                refine ⟨18920654825678101963162181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50455079535141605235099149 18920654825678101963162181)
                ·
                  refine ⟨3547622779814644118092909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18920654825678101963162181 3547622779814644118092909)
                  ·
                    refine ⟨1330358542430491544284841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3547622779814644118092909 1330358542430491544284841)
                    ·
                      refine ⟨997768906822868658213631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330358542430491544284841 997768906822868658213631)
                      ·
                        rfl

theorem cell23_1943148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 3, 2].length) (baseStart_1943148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943148 prefixEnd_1943148 := by exact prefixLift 1943148
  have htrace : WordTrace (prefixWord ++ tailWord_1943148) baseStart_1943148 baseEnd_1943148 := by
    simpa [prefixWord, tailWord_1943148, baseEnd_1943148] using wordTrace_append hprefix tailTrace_1943148
  have hstable : (prefixWord ++ tailWord_1943148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943148).length < 2 ^ (prefixWord ++ tailWord_1943148).sum := by decide
  have hdescent : baseEnd_1943148 < baseStart_1943148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943201 : List Nat := [1, 2, 3, 3, 2, 1, 11]
def baseStart_1943201 : Nat := 118140960795 + 1943201 * 2 ^ 59
def prefixEnd_1943201 : Nat := 4983230072969 + 3 ^ 40 * 1943201 * 2
def baseEnd_1943201 : Nat := 12318470633303172232727

theorem tailTrace_1943201 : CollatzResearch.WordTrace tailWord_1943201 prefixEnd_1943201 12318470633303172232727 := by
  unfold tailWord_1943201
  simp only [CollatzResearch.WordTrace]
  refine ⟨70874363033122124154205457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47249575355414749436136971 70874363033122124154205457)
  ·
    refine ⟨53155772274841593115654093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70874363033122124154205457 53155772274841593115654093)
    ·
      refine ⟨19933414603065597418370285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53155772274841593115654093 19933414603065597418370285)
      ·
        refine ⟨7475030476149599031888857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19933414603065597418370285 7475030476149599031888857)
        ·
          refine ⟨5606272857112199273916643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7475030476149599031888857 5606272857112199273916643)
          ·
            refine ⟨8409409285668298910874965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5606272857112199273916643 8409409285668298910874965)
            ·
              refine ⟨12318470633303172232727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8409409285668298910874965 12318470633303172232727)
              ·
                rfl

theorem cell23_1943201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 11].length) (baseStart_1943201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943201 prefixEnd_1943201 := by exact prefixLift 1943201
  have htrace : WordTrace (prefixWord ++ tailWord_1943201) baseStart_1943201 baseEnd_1943201 := by
    simpa [prefixWord, tailWord_1943201, baseEnd_1943201] using wordTrace_append hprefix tailTrace_1943201
  have hstable : (prefixWord ++ tailWord_1943201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943201).length < 2 ^ (prefixWord ++ tailWord_1943201).sum := by decide
  have hdescent : baseEnd_1943201 < baseStart_1943201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943278 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1943278 : Nat := 118140960795 + 1943278 * 2 ^ 59
def prefixEnd_1943278 : Nat := 4983230072969 + 3 ^ 40 * 1943278 * 2
def baseEnd_1943278 : Nat := 332611886435984383196011

theorem tailTrace_1943278 : CollatzResearch.WordTrace tailWord_1943278 prefixEnd_1943278 332611886435984383196011 := by
  unfold tailWord_1943278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8859646431730395788094811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47251447635895444203172325 8859646431730395788094811)
  ·
    refine ⟨13289469647595593682142217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8859646431730395788094811 13289469647595593682142217)
    ·
      refine ⟨9967102235696695261606663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13289469647595593682142217 9967102235696695261606663)
      ·
        refine ⟨14950653353545042892409995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9967102235696695261606663 14950653353545042892409995)
        ·
          refine ⟨22425980030317564338614993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14950653353545042892409995 22425980030317564338614993)
          ·
            refine ⟨16819485022738173253961245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22425980030317564338614993 16819485022738173253961245)
            ·
              refine ⟨6307306883526814970235467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16819485022738173253961245 6307306883526814970235467)
              ·
                refine ⟨9460960325290222455353201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6307306883526814970235467 9460960325290222455353201)
                ·
                  refine ⟨7095720243967666841514901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9460960325290222455353201 7095720243967666841514901)
                  ·
                    refine ⟨332611886435984383196011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7095720243967666841514901 332611886435984383196011)
                    ·
                      rfl

theorem cell23_1943278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1943278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943278 prefixEnd_1943278 := by exact prefixLift 1943278
  have htrace : WordTrace (prefixWord ++ tailWord_1943278) baseStart_1943278 baseEnd_1943278 := by
    simpa [prefixWord, tailWord_1943278, baseEnd_1943278] using wordTrace_append hprefix tailTrace_1943278
  have hstable : (prefixWord ++ tailWord_1943278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943278).length < 2 ^ (prefixWord ++ tailWord_1943278).sum := by decide
  have hdescent : baseEnd_1943278 < baseStart_1943278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943301 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_1943301 : Nat := 118140960795 + 1943301 * 2 ^ 59
def prefixEnd_1943301 : Nat := 4983230072969 + 3 ^ 40 * 1943301 * 2
def baseEnd_1943301 : Nat := 997847469363006559600427

theorem tailTrace_1943301 : CollatzResearch.WordTrace tailWord_1943301 prefixEnd_1943301 997847469363006559600427 := by
  unfold tailWord_1943301
  simp only [CollatzResearch.WordTrace]
  refine ⟨70878010332759841232845757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47252006888506560821897171 70878010332759841232845757)
  ·
    refine ⟨26579253874784940462317159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70878010332759841232845757 26579253874784940462317159)
    ·
      refine ⟨39868880812177410693475739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26579253874784940462317159 39868880812177410693475739)
      ·
        refine ⟨59803321218266116040213609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39868880812177410693475739 59803321218266116040213609)
        ·
          refine ⟨44852490913699587030160207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59803321218266116040213609 44852490913699587030160207)
          ·
            refine ⟨67278736370549380545240311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44852490913699587030160207 67278736370549380545240311)
            ·
              refine ⟨100918104555824070817860467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67278736370549380545240311 100918104555824070817860467)
              ·
                refine ⟨151377156833736106226790701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100918104555824070817860467 151377156833736106226790701)
                ·
                  refine ⟨56766433812651039835046513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151377156833736106226790701 56766433812651039835046513)
                  ·
                    refine ⟨42574825359488279876284885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56766433812651039835046513 42574825359488279876284885)
                    ·
                      refine ⟨997847469363006559600427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42574825359488279876284885 997847469363006559600427)
                      ·
                        rfl

theorem cell23_1943301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_1943301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943301 prefixEnd_1943301 := by exact prefixLift 1943301
  have htrace : WordTrace (prefixWord ++ tailWord_1943301) baseStart_1943301 baseEnd_1943301 := by
    simpa [prefixWord, tailWord_1943301, baseEnd_1943301] using wordTrace_append hprefix tailTrace_1943301
  have hstable : (prefixWord ++ tailWord_1943301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943301).length < 2 ^ (prefixWord ++ tailWord_1943301).sum := by decide
  have hdescent : baseEnd_1943301 < baseStart_1943301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943319 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 2, 2, 2]
def baseStart_1943319 : Nat := 118140960795 + 1943319 * 2 ^ 59
def prefixEnd_1943319 : Nat := 4983230072969 + 3 ^ 40 * 1943319 * 2
def baseEnd_1943319 : Nat := 997856712014787489175345

theorem tailTrace_1943319 : CollatzResearch.WordTrace tailWord_1943319 prefixEnd_1943319 997856712014787489175345 := by
  unfold tailWord_1943319
  simp only [CollatzResearch.WordTrace]
  refine ⟨70878666846694630307001011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47252444564463086871334007 70878666846694630307001011)
  ·
    refine ⟨106318000270041945460501517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70878666846694630307001011 106318000270041945460501517)
    ·
      refine ⟨39869250101265729547688069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106318000270041945460501517 39869250101265729547688069)
      ·
        refine ⟨7475484393987324290191513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39869250101265729547688069 7475484393987324290191513)
        ·
          refine ⟨5606613295490493217643635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7475484393987324290191513 5606613295490493217643635)
          ·
            refine ⟨8409919943235739826465453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5606613295490493217643635 8409919943235739826465453)
            ·
              refine ⟨3153719978713402434924545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8409919943235739826465453 3153719978713402434924545)
              ·
                refine ⟨2365289984035051826193409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3153719978713402434924545 2365289984035051826193409)
                ·
                  refine ⟨1773967488026288869645057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2365289984035051826193409 1773967488026288869645057)
                  ·
                    refine ⟨1330475616019716652233793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1773967488026288869645057 1330475616019716652233793)
                    ·
                      refine ⟨997856712014787489175345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330475616019716652233793 997856712014787489175345)
                      ·
                        rfl

theorem cell23_1943319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_1943319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943319 prefixEnd_1943319 := by exact prefixLift 1943319
  have htrace : WordTrace (prefixWord ++ tailWord_1943319) baseStart_1943319 baseEnd_1943319 := by
    simpa [prefixWord, tailWord_1943319, baseEnd_1943319] using wordTrace_append hprefix tailTrace_1943319
  have hstable : (prefixWord ++ tailWord_1943319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943319).length < 2 ^ (prefixWord ++ tailWord_1943319).sum := by decide
  have hdescent : baseEnd_1943319 < baseStart_1943319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943336 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_1943336 : Nat := 118140960795 + 1943336 * 2 ^ 59
def prefixEnd_1943336 : Nat := 4983230072969 + 3 ^ 40 * 1943336 * 2
def baseEnd_1943336 : Nat := 997865441185913922662767

theorem tailTrace_1943336 : CollatzResearch.WordTrace tailWord_1943336 prefixEnd_1943336 997865441185913922662767 := by
  unfold tailWord_1943336
  simp only [CollatzResearch.WordTrace]
  refine ⟨35439643443816521105184931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47252857925088694806913241 35439643443816521105184931)
  ·
    refine ⟨53159465165724781657777397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35439643443816521105184931 53159465165724781657777397)
    ·
      refine ⟨4983699859286698280416631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53159465165724781657777397 4983699859286698280416631)
      ·
        refine ⟨7475549788930047420624947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4983699859286698280416631 7475549788930047420624947)
        ·
          refine ⟨11213324683395071130937421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7475549788930047420624947 11213324683395071130937421)
          ·
            refine ⟨4204996756273151674101533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11213324683395071130937421 4204996756273151674101533)
            ·
              refine ⟨1576873783602431877788075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4204996756273151674101533 1576873783602431877788075)
              ·
                refine ⟨2365310675403647816682113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576873783602431877788075 2365310675403647816682113)
                ·
                  refine ⟨1773983006552735862511585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2365310675403647816682113 1773983006552735862511585)
                  ·
                    refine ⟨1330487254914551896883689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1773983006552735862511585 1330487254914551896883689)
                    ·
                      refine ⟨997865441185913922662767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330487254914551896883689 997865441185913922662767)
                      ·
                        rfl

theorem cell23_1943336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_1943336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943336 prefixEnd_1943336 := by exact prefixLift 1943336
  have htrace : WordTrace (prefixWord ++ tailWord_1943336) baseStart_1943336 baseEnd_1943336 := by
    simpa [prefixWord, tailWord_1943336, baseEnd_1943336] using wordTrace_append hprefix tailTrace_1943336
  have hstable : (prefixWord ++ tailWord_1943336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943336).length < 2 ^ (prefixWord ++ tailWord_1943336).sum := by decide
  have hdescent : baseEnd_1943336 < baseStart_1943336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943359 : List Nat := [1, 1, 2, 2, 7, 1, 1, 3, 5]
def baseStart_1943359 : Nat := 118140960795 + 1943359 * 2 ^ 59
def prefixEnd_1943359 : Nat := 4983230072969 + 3 ^ 40 * 1943359 * 2
def baseEnd_1943359 : Nat := 110875250137885259186129

theorem tailTrace_1943359 : CollatzResearch.WordTrace tailWord_1943359 prefixEnd_1943359 110875250137885259186129 := by
  unfold tailWord_1943359
  simp only [CollatzResearch.WordTrace]
  refine ⟨70880125766549717138457131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47253417177699811425638087 70880125766549717138457131)
  ·
    refine ⟨106320188649824575707685697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70880125766549717138457131 106320188649824575707685697)
    ·
      refine ⟨79740141487368431780764273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106320188649824575707685697 79740141487368431780764273)
      ·
        refine ⟨59805106115526323835573205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79740141487368431780764273 59805106115526323835573205)
        ·
          refine ⟨1401682174582648214896247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 59805106115526323835573205 1401682174582648214896247)
          ·
            refine ⟨2102523261873972322344371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401682174582648214896247 2102523261873972322344371)
            ·
              refine ⟨3153784892810958483516557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2102523261873972322344371 3153784892810958483516557)
              ·
                refine ⟨1182669334804109431318709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3153784892810958483516557 1182669334804109431318709)
                ·
                  refine ⟨110875250137885259186129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1182669334804109431318709 110875250137885259186129)
                  ·
                    rfl

theorem cell23_1943359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 5].length) (baseStart_1943359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943359 prefixEnd_1943359 := by exact prefixLift 1943359
  have htrace : WordTrace (prefixWord ++ tailWord_1943359) baseStart_1943359 baseEnd_1943359 := by
    simpa [prefixWord, tailWord_1943359, baseEnd_1943359] using wordTrace_append hprefix tailTrace_1943359
  have hstable : (prefixWord ++ tailWord_1943359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943359).length < 2 ^ (prefixWord ++ tailWord_1943359).sum := by decide
  have hdescent : baseEnd_1943359 < baseStart_1943359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943432 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 6]
def baseStart_1943432 : Nat := 118140960795 + 1943432 * 2 ^ 59
def prefixEnd_1943432 : Nat := 4983230072969 + 3 ^ 40 * 1943432 * 2
def baseEnd_1943432 : Nat := 110879415036527283006925

theorem tailTrace_1943432 : CollatzResearch.WordTrace tailWord_1943432 prefixEnd_1943432 110879415036527283006925 := by
  unfold tailWord_1943432
  simp only [CollatzResearch.WordTrace]
  refine ⟨35441394147642625302932275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47255192196856833737243033 35441394147642625302932275)
  ·
    refine ⟨53162091221463937954398413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35441394147642625302932275 53162091221463937954398413)
    ·
      refine ⟨19935784208048976732899405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53162091221463937954398413 19935784208048976732899405)
      ·
        refine ⟨7475919078018366274837277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19935784208048976732899405 7475919078018366274837277)
        ·
          refine ⟨2803469654256887353063979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7475919078018366274837277 2803469654256887353063979)
          ·
            refine ⟨4205204481385331029595969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803469654256887353063979 4205204481385331029595969)
            ·
              refine ⟨3153903361038998272196977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4205204481385331029595969 3153903361038998272196977)
              ·
                refine ⟨2365427520779248704147733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3153903361038998272196977 2365427520779248704147733)
                ·
                  refine ⟨110879415036527283006925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2365427520779248704147733 110879415036527283006925)
                  ·
                    rfl

theorem cell23_1943432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 6].length) (baseStart_1943432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943432 prefixEnd_1943432 := by exact prefixLift 1943432
  have htrace : WordTrace (prefixWord ++ tailWord_1943432) baseStart_1943432 baseEnd_1943432 := by
    simpa [prefixWord, tailWord_1943432, baseEnd_1943432] using wordTrace_append hprefix tailTrace_1943432
  have hstable : (prefixWord ++ tailWord_1943432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943432).length < 2 ^ (prefixWord ++ tailWord_1943432).sum := by decide
  have hdescent : baseEnd_1943432 < baseStart_1943432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943435 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 3, 5, 2]
def baseStart_1943435 : Nat := 118140960795 + 1943435 * 2 ^ 59
def prefixEnd_1943435 : Nat := 4983230072969 + 3 ^ 40 * 1943435 * 2
def baseEnd_1943435 : Nat := 997916275770709035324811

theorem tailTrace_1943435 : CollatzResearch.WordTrace tailWord_1943435 prefixEnd_1943435 997916275770709035324811 := by
  unfold tailWord_1943435
  simp only [CollatzResearch.WordTrace]
  refine ⟨70882897714274382118223759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47255265142849588078815839 70882897714274382118223759)
  ·
    refine ⟨106324346571411573177335639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70882897714274382118223759 106324346571411573177335639)
    ·
      refine ⟨159486519857117359766003459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106324346571411573177335639 159486519857117359766003459)
      ·
        refine ⟨239229779785676039649005189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159486519857117359766003459 239229779785676039649005189)
        ·
          refine ⟨44855583709814257434188473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239229779785676039649005189 44855583709814257434188473)
          ·
            refine ⟨33641687782360693075641355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44855583709814257434188473 33641687782360693075641355)
            ·
              refine ⟨50462531673541039613462033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33641687782360693075641355 50462531673541039613462033)
              ·
                refine ⟨37846898755155779710096525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50462531673541039613462033 37846898755155779710096525)
                ·
                  refine ⟨14192587033183417391286197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37846898755155779710096525 14192587033183417391286197)
                  ·
                    refine ⟨1330555034360945380433081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14192587033183417391286197 1330555034360945380433081)
                    ·
                      refine ⟨997916275770709035324811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330555034360945380433081 997916275770709035324811)
                      ·
                        rfl

theorem cell23_1943435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 5, 2].length) (baseStart_1943435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943435 prefixEnd_1943435 := by exact prefixLift 1943435
  have htrace : WordTrace (prefixWord ++ tailWord_1943435) baseStart_1943435 baseEnd_1943435 := by
    simpa [prefixWord, tailWord_1943435, baseEnd_1943435] using wordTrace_append hprefix tailTrace_1943435
  have hstable : (prefixWord ++ tailWord_1943435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943435).length < 2 ^ (prefixWord ++ tailWord_1943435).sum := by decide
  have hdescent : baseEnd_1943435 < baseStart_1943435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943465 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 1, 8, 2]
def baseStart_1943465 : Nat := 118140960795 + 1943465 * 2 ^ 59
def prefixEnd_1943465 : Nat := 4983230072969 + 3 ^ 40 * 1943465 * 2
def baseEnd_1943465 : Nat := 997931680190343917949673

theorem tailTrace_1943465 : CollatzResearch.WordTrace tailWord_1943465 prefixEnd_1943465 997931680190343917949673 := by
  unfold tailWord_1943465
  simp only [CollatzResearch.WordTrace]
  refine ⟨70883991904165697241815849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47255994602777131494543899 70883991904165697241815849)
  ·
    refine ⟨53162993928124272931361887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70883991904165697241815849 53162993928124272931361887)
    ·
      refine ⟨79744490892186409397042831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53162993928124272931361887 79744490892186409397042831)
      ·
        refine ⟨119616736338279614095564247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79744490892186409397042831 119616736338279614095564247)
        ·
          refine ⟨179425104507419421143346371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119616736338279614095564247 179425104507419421143346371)
          ·
            refine ⟨269137656761129131715019557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179425104507419421143346371 269137656761129131715019557)
            ·
              refine ⟨50463310642711712196566167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269137656761129131715019557 50463310642711712196566167)
              ·
                refine ⟨75694965964067568294849251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50463310642711712196566167 75694965964067568294849251)
                ·
                  refine ⟨113542448946101352442273877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75694965964067568294849251 113542448946101352442273877)
                  ·
                    refine ⟨1330575573587125223932897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113542448946101352442273877 1330575573587125223932897)
                    ·
                      refine ⟨997931680190343917949673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330575573587125223932897 997931680190343917949673)
                      ·
                        rfl

theorem cell23_1943465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 8, 2].length) (baseStart_1943465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943465 prefixEnd_1943465 := by exact prefixLift 1943465
  have htrace : WordTrace (prefixWord ++ tailWord_1943465) baseStart_1943465 baseEnd_1943465 := by
    simpa [prefixWord, tailWord_1943465, baseEnd_1943465] using wordTrace_append hprefix tailTrace_1943465
  have hstable : (prefixWord ++ tailWord_1943465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943465).length < 2 ^ (prefixWord ++ tailWord_1943465).sum := by decide
  have hdescent : baseEnd_1943465 < baseStart_1943465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943468 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_1943468 : Nat := 118140960795 + 1943468 * 2 ^ 59
def prefixEnd_1943468 : Nat := 4983230072969 + 3 ^ 40 * 1943468 * 2
def baseEnd_1943468 : Nat := 997933220632307406212159

theorem tailTrace_1943468 : CollatzResearch.WordTrace tailWord_1943468 prefixEnd_1943468 997933220632307406212159 := by
  unfold tailWord_1943468
  simp only [CollatzResearch.WordTrace]
  refine ⟨35442050661577414377087529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47256067548769885836116705 35442050661577414377087529)
  ·
    refine ⟨26581537996183060782815647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35442050661577414377087529 26581537996183060782815647)
    ·
      refine ⟨39872306994274591174223471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26581537996183060782815647 39872306994274591174223471)
      ·
        refine ⟨59808460491411886761335207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39872306994274591174223471 59808460491411886761335207)
        ·
          refine ⟨89712690737117830142002811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59808460491411886761335207 89712690737117830142002811)
          ·
            refine ⟨134569036105676745213004217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89712690737117830142002811 134569036105676745213004217)
            ·
              refine ⟨100926777079257558909753163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134569036105676745213004217 100926777079257558909753163)
              ·
                refine ⟨151390165618886338364629745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100926777079257558909753163 151390165618886338364629745)
                ·
                  refine ⟨113542624214164753773472309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151390165618886338364629745 113542624214164753773472309)
                  ·
                    refine ⟨10644621020077945666263029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113542624214164753773472309 10644621020077945666263029)
                    ·
                      refine ⟨997933220632307406212159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10644621020077945666263029 997933220632307406212159)
                      ·
                        rfl

theorem cell23_1943468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_1943468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943468 prefixEnd_1943468 := by exact prefixLift 1943468
  have htrace : WordTrace (prefixWord ++ tailWord_1943468) baseStart_1943468 baseEnd_1943468 := by
    simpa [prefixWord, tailWord_1943468, baseEnd_1943468] using wordTrace_append hprefix tailTrace_1943468
  have hstable : (prefixWord ++ tailWord_1943468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943468).length < 2 ^ (prefixWord ++ tailWord_1943468).sum := by decide
  have hdescent : baseEnd_1943468 < baseStart_1943468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943470 : List Nat := [4, 1, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1943470 : Nat := 118140960795 + 1943470 * 2 ^ 59
def prefixEnd_1943470 : Nat := 4983230072969 + 3 ^ 40 * 1943470 * 2
def baseEnd_1943470 : Nat := 332644749197872132795717

theorem tailTrace_1943470 : CollatzResearch.WordTrace tailWord_1943470 prefixEnd_1943470 332644749197872132795717 := by
  unfold tailWord_1943470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8860521783643447886968483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47256116179431722063831909 8860521783643447886968483)
  ·
    refine ⟨13290782675465171830452725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8860521783643447886968483 13290782675465171830452725)
    ·
      refine ⟨1246010875824859859104943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13290782675465171830452725 1246010875824859859104943)
      ·
        refine ⟨1869016313737289788657415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246010875824859859104943 1869016313737289788657415)
        ·
          refine ⟨2803524470605934682986123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869016313737289788657415 2803524470605934682986123)
          ·
            refine ⟨4205286705908902024479185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803524470605934682986123 4205286705908902024479185)
            ·
              refine ⟨3153965029431676518359389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4205286705908902024479185 3153965029431676518359389)
              ·
                refine ⟨1182736886036878694384771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3153965029431676518359389 1182736886036878694384771)
                ·
                  refine ⟨1774105329055318041577157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182736886036878694384771 1774105329055318041577157)
                  ·
                    refine ⟨332644749197872132795717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1774105329055318041577157 332644749197872132795717)
                    ·
                      rfl

theorem cell23_1943470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1943470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943470 prefixEnd_1943470 := by exact prefixLift 1943470
  have htrace : WordTrace (prefixWord ++ tailWord_1943470) baseStart_1943470 baseEnd_1943470 := by
    simpa [prefixWord, tailWord_1943470, baseEnd_1943470] using wordTrace_append hprefix tailTrace_1943470
  have hstable : (prefixWord ++ tailWord_1943470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943470).length < 2 ^ (prefixWord ++ tailWord_1943470).sum := by decide
  have hdescent : baseEnd_1943470 < baseStart_1943470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943475 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 4, 4]
def baseStart_1943475 : Nat := 118140960795 + 1943475 * 2 ^ 59
def prefixEnd_1943475 : Nat := 4983230072969 + 3 ^ 40 * 1943475 * 2
def baseEnd_1943475 : Nat := 332645604998962959608209

theorem tailTrace_1943475 : CollatzResearch.WordTrace tailWord_1943475 prefixEnd_1943475 332645604998962959608209 := by
  unfold tailWord_1943475
  simp only [CollatzResearch.WordTrace]
  refine ⟨70884356634129468949679879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47256237756086312633119919 70884356634129468949679879)
  ·
    refine ⟨106326534951194203424519819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70884356634129468949679879 106326534951194203424519819)
    ·
      refine ⟨159489802426791305136779729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106326534951194203424519819 159489802426791305136779729)
      ·
        refine ⟨119617351820093478852584797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159489802426791305136779729 119617351820093478852584797)
        ·
          refine ⟨44856506932535054569719299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119617351820093478852584797 44856506932535054569719299)
          ·
            refine ⟨67284760398802581854578949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44856506932535054569719299 67284760398802581854578949)
            ·
              refine ⟨12615892574775484097733553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67284760398802581854578949 12615892574775484097733553)
              ·
                refine ⟨9461919431081613073300165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12615892574775484097733553 9461919431081613073300165)
                ·
                  refine ⟨1774109893327802451243781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9461919431081613073300165 1774109893327802451243781)
                  ·
                    refine ⟨332645604998962959608209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1774109893327802451243781 332645604998962959608209)
                    ·
                      rfl

theorem cell23_1943475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 4].length) (baseStart_1943475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943475 prefixEnd_1943475 := by exact prefixLift 1943475
  have htrace : WordTrace (prefixWord ++ tailWord_1943475) baseStart_1943475 baseEnd_1943475 := by
    simpa [prefixWord, tailWord_1943475, baseEnd_1943475] using wordTrace_append hprefix tailTrace_1943475
  have hstable : (prefixWord ++ tailWord_1943475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943475).length < 2 ^ (prefixWord ++ tailWord_1943475).sum := by decide
  have hdescent : baseEnd_1943475 < baseStart_1943475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943488 : List Nat := [2, 1, 1, 2, 3, 2, 12]
def baseStart_1943488 : Nat := 118140960795 + 1943488 * 2 ^ 59
def prefixEnd_1943488 : Nat := 4983230072969 + 3 ^ 40 * 1943488 * 2
def baseEnd_1943488 : Nat := 12320290003029596641507

theorem tailTrace_1943488 : CollatzResearch.WordTrace tailWord_1943488 prefixEnd_1943488 12320290003029596641507 := by
  unfold tailWord_1943488
  simp only [CollatzResearch.WordTrace]
  refine ⟨35442415391541186084951559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47256553855388248113268745 35442415391541186084951559)
  ·
    refine ⟨53163623087311779127427339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35442415391541186084951559 53163623087311779127427339)
    ·
      refine ⟨79745434630967668691141009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53163623087311779127427339 79745434630967668691141009)
      ·
        refine ⟨59809075973225751518355757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79745434630967668691141009 59809075973225751518355757)
        ·
          refine ⟨22428403489959656819383409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59809075973225751518355757 22428403489959656819383409)
          ·
            refine ⟨16821302617469742614537557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22428403489959656819383409 16821302617469742614537557)
            ·
              refine ⟨12320290003029596641507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 16821302617469742614537557 12320290003029596641507)
              ·
                rfl

theorem cell23_1943488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 12].length) (baseStart_1943488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943488 prefixEnd_1943488 := by exact prefixLift 1943488
  have htrace : WordTrace (prefixWord ++ tailWord_1943488) baseStart_1943488 baseEnd_1943488 := by
    simpa [prefixWord, tailWord_1943488, baseEnd_1943488] using wordTrace_append hprefix tailTrace_1943488
  have hstable : (prefixWord ++ tailWord_1943488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943488).length < 2 ^ (prefixWord ++ tailWord_1943488).sum := by decide
  have hdescent : baseEnd_1943488 < baseStart_1943488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943499 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 3, 2, 2]
def baseStart_1943499 : Nat := 118140960795 + 1943499 * 2 ^ 59
def prefixEnd_1943499 : Nat := 4983230072969 + 3 ^ 40 * 1943499 * 2
def baseEnd_1943499 : Nat := 997949138532596784924517

theorem tailTrace_1943499 : CollatzResearch.WordTrace tailWord_1943499 prefixEnd_1943499 997949138532596784924517 := by
  unfold tailWord_1943499
  simp only [CollatzResearch.WordTrace]
  refine ⟨70885231986042521048553551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47256821324028347365702367 70885231986042521048553551)
  ·
    refine ⟨106327847979063781572830327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70885231986042521048553551 106327847979063781572830327)
    ·
      refine ⟨159491771968595672359245491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106327847979063781572830327 159491771968595672359245491)
      ·
        refine ⟨239237657952893508538868237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159491771968595672359245491 239237657952893508538868237)
        ·
          refine ⟨89714121732335065702075589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239237657952893508538868237 89714121732335065702075589)
          ·
            refine ⟨16821397824812824819139173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89714121732335065702075589 16821397824812824819139173)
            ·
              refine ⟨3154012092152404653588595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16821397824812824819139173 3154012092152404653588595)
              ·
                refine ⟨4731018138228606980382893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154012092152404653588595 4731018138228606980382893)
                ·
                  refine ⟨1774131801835727617643585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4731018138228606980382893 1774131801835727617643585)
                  ·
                    refine ⟨1330598851376795713232689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1774131801835727617643585 1330598851376795713232689)
                    ·
                      refine ⟨997949138532596784924517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330598851376795713232689 997949138532596784924517)
                      ·
                        rfl

theorem cell23_1943499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 2, 2].length) (baseStart_1943499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943499 prefixEnd_1943499 := by exact prefixLift 1943499
  have htrace : WordTrace (prefixWord ++ tailWord_1943499) baseStart_1943499 baseEnd_1943499 := by
    simpa [prefixWord, tailWord_1943499, baseEnd_1943499] using wordTrace_append hprefix tailTrace_1943499
  have hstable : (prefixWord ++ tailWord_1943499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943499).length < 2 ^ (prefixWord ++ tailWord_1943499).sum := by decide
  have hdescent : baseEnd_1943499 < baseStart_1943499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943519 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 1, 2, 3]
def baseStart_1943519 : Nat := 118140960795 + 1943519 * 2 ^ 59
def prefixEnd_1943519 : Nat := 4983230072969 + 3 ^ 40 * 1943519 * 2
def baseEnd_1943519 : Nat := 997959408145686706674425

theorem tailTrace_1943519 : CollatzResearch.WordTrace tailWord_1943519 prefixEnd_1943519 997959408145686706674425 := by
  unfold tailWord_1943519
  simp only [CollatzResearch.WordTrace]
  refine ⟨70885961445970064464281611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47257307630646709642854407 70885961445970064464281611)
  ·
    refine ⟨106328942168955096696422417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70885961445970064464281611 106328942168955096696422417)
    ·
      refine ⟨79746706626716322522316813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106328942168955096696422417 79746706626716322522316813)
      ·
        refine ⟨29905014985018620945868805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79746706626716322522316813 29905014985018620945868805)
        ·
          refine ⟨5607190309690991427350401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29905014985018620945868805 5607190309690991427350401)
          ·
            refine ⟨4205392732268243570512801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5607190309690991427350401 4205392732268243570512801)
            ·
              refine ⟨3154044549201182677884601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4205392732268243570512801 3154044549201182677884601)
              ·
                refine ⟨2365533411900887008413451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3154044549201182677884601 2365533411900887008413451)
                ·
                  refine ⟨3548300117851330512620177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365533411900887008413451 3548300117851330512620177)
                  ·
                    refine ⟨2661225088388497884465133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3548300117851330512620177 2661225088388497884465133)
                    ·
                      refine ⟨997959408145686706674425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2661225088388497884465133 997959408145686706674425)
                      ·
                        rfl

theorem cell23_1943519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_1943519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943519 prefixEnd_1943519 := by exact prefixLift 1943519
  have htrace : WordTrace (prefixWord ++ tailWord_1943519) baseStart_1943519 baseEnd_1943519 := by
    simpa [prefixWord, tailWord_1943519, baseEnd_1943519] using wordTrace_append hprefix tailTrace_1943519
  have hstable : (prefixWord ++ tailWord_1943519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943519).length < 2 ^ (prefixWord ++ tailWord_1943519).sum := by decide
  have hdescent : baseEnd_1943519 < baseStart_1943519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943589 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 1, 4, 2]
def baseStart_1943589 : Nat := 118140960795 + 1943589 * 2 ^ 59
def prefixEnd_1943589 : Nat := 4983230072969 + 3 ^ 40 * 1943589 * 2
def baseEnd_1943589 : Nat := 997995351791501432799103

theorem tailTrace_1943589 : CollatzResearch.WordTrace tailWord_1943589 prefixEnd_1943589 997995351791501432799103 := by
  unfold tailWord_1943589
  simp only [CollatzResearch.WordTrace]
  refine ⟨70888514555716466419329821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47259009703810977612886547 70888514555716466419329821)
  ·
    refine ⟨26583192958393674907248683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70888514555716466419329821 26583192958393674907248683)
    ·
      refine ⟨39874789437590512360873025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26583192958393674907248683 39874789437590512360873025)
      ·
        refine ⟨29906092078192884270654769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39874789437590512360873025 29906092078192884270654769)
        ·
          refine ⟨22429569058644663202991077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29906092078192884270654769 22429569058644663202991077)
          ·
            refine ⟨4205544198495874350560827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22429569058644663202991077 4205544198495874350560827)
            ·
              refine ⟨6308316297743811525841241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4205544198495874350560827 6308316297743811525841241)
              ·
                refine ⟨4731237223307858644380931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6308316297743811525841241 4731237223307858644380931)
                ·
                  refine ⟨7096855834961787966571397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731237223307858644380931 7096855834961787966571397)
                  ·
                    refine ⟨1330660469055335243732137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7096855834961787966571397 1330660469055335243732137)
                    ·
                      refine ⟨997995351791501432799103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330660469055335243732137 997995351791501432799103)
                      ·
                        rfl

theorem cell23_1943589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_1943589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943589 prefixEnd_1943589 := by exact prefixLift 1943589
  have htrace : WordTrace (prefixWord ++ tailWord_1943589) baseStart_1943589 baseEnd_1943589 := by
    simpa [prefixWord, tailWord_1943589, baseEnd_1943589] using wordTrace_append hprefix tailTrace_1943589
  have hstable : (prefixWord ++ tailWord_1943589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943589).length < 2 ^ (prefixWord ++ tailWord_1943589).sum := by decide
  have hdescent : baseEnd_1943589 < baseStart_1943589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943605 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1943605 : Nat := 118140960795 + 1943605 * 2 ^ 59
def prefixEnd_1943605 : Nat := 4983230072969 + 3 ^ 40 * 1943605 * 2
def baseEnd_1943605 : Nat := 998003567481973370199029

theorem tailTrace_1943605 : CollatzResearch.WordTrace tailWord_1943605 prefixEnd_1943605 998003567481973370199029 := by
  unfold tailWord_1943605
  simp only [CollatzResearch.WordTrace]
  refine ⟨70889098123658501151912269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47259398749105667434608179 70889098123658501151912269)
  ·
    refine ⟨26583411796371937931967101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70889098123658501151912269 26583411796371937931967101)
    ·
      refine ⟨9968779423639476724487663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26583411796371937931967101 9968779423639476724487663)
      ·
        refine ⟨14953169135459215086731495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9968779423639476724487663 14953169135459215086731495)
        ·
          refine ⟨22429753703188822630097243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14953169135459215086731495 22429753703188822630097243)
          ·
            refine ⟨33644630554783233945145865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22429753703188822630097243 33644630554783233945145865)
            ·
              refine ⟨25233472916087425458859399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33644630554783233945145865 25233472916087425458859399)
              ·
                refine ⟨37850209374131138188289099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25233472916087425458859399 37850209374131138188289099)
                ·
                  refine ⟨56775314061196707282433649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37850209374131138188289099 56775314061196707282433649)
                  ·
                    refine ⟨42581485545897530461825237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56775314061196707282433649 42581485545897530461825237)
                    ·
                      refine ⟨998003567481973370199029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42581485545897530461825237 998003567481973370199029)
                      ·
                        rfl

theorem cell23_1943605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1943605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943605 prefixEnd_1943605 := by exact prefixLift 1943605
  have htrace : WordTrace (prefixWord ++ tailWord_1943605) baseStart_1943605 baseEnd_1943605 := by
    simpa [prefixWord, tailWord_1943605, baseEnd_1943605] using wordTrace_append hprefix tailTrace_1943605
  have hstable : (prefixWord ++ tailWord_1943605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943605).length < 2 ^ (prefixWord ++ tailWord_1943605).sum := by decide
  have hdescent : baseEnd_1943605 < baseStart_1943605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943625 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 1, 7]
def baseStart_1943625 : Nat := 118140960795 + 1943625 * 2 ^ 59
def prefixEnd_1943625 : Nat := 4983230072969 + 3 ^ 40 * 1943625 * 2
def baseEnd_1943625 : Nat := 332671279031687763982979

theorem tailTrace_1943625 : CollatzResearch.WordTrace tailWord_1943625 prefixEnd_1943625 332671279031687763982979 := by
  unfold tailWord_1943625
  simp only [CollatzResearch.WordTrace]
  refine ⟨70889827583586044567640329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47259885055724029711760219 70889827583586044567640329)
  ·
    refine ⟨53167370687689533425730247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70889827583586044567640329 53167370687689533425730247)
    ·
      refine ⟨79751056031534300138595371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53167370687689533425730247 79751056031534300138595371)
      ·
        refine ⟨119626584047301450207893057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79751056031534300138595371 119626584047301450207893057)
        ·
          refine ⟨89719938035476087655919793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119626584047301450207893057 89719938035476087655919793)
          ·
            refine ⟨67289953526607065741939845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89719938035476087655919793 67289953526607065741939845)
            ·
              refine ⟨12616866286238824826613721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67289953526607065741939845 12616866286238824826613721)
              ·
                refine ⟨9462649714679118619960291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12616866286238824826613721 9462649714679118619960291)
                ·
                  refine ⟨14193974572018677929940437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9462649714679118619960291 14193974572018677929940437)
                  ·
                    refine ⟨332671279031687763982979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14193974572018677929940437 332671279031687763982979)
                    ·
                      rfl

theorem cell23_1943625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_1943625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943625 prefixEnd_1943625 := by exact prefixLift 1943625
  have htrace : WordTrace (prefixWord ++ tailWord_1943625) baseStart_1943625 baseEnd_1943625 := by
    simpa [prefixWord, tailWord_1943625, baseEnd_1943625] using wordTrace_append hprefix tailTrace_1943625
  have hstable : (prefixWord ++ tailWord_1943625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943625).length < 2 ^ (prefixWord ++ tailWord_1943625).sum := by decide
  have hdescent : baseEnd_1943625 < baseStart_1943625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943716 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_1943716 : Nat := 118140960795 + 1943716 * 2 ^ 59
def prefixEnd_1943716 : Nat := 4983230072969 + 3 ^ 40 * 1943716 * 2
def baseEnd_1943716 : Nat := 998060563834622435911019

theorem tailTrace_1943716 : CollatzResearch.WordTrace tailWord_1943716 prefixEnd_1943716 998060563834622435911019 := by
  unfold tailWord_1943716
  simp only [CollatzResearch.WordTrace]
  refine ⟨35446573313128183554601501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47262097750837578072802001 35446573313128183554601501)
  ·
    refine ⟨13292464992423068832975563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35446573313128183554601501 13292464992423068832975563)
    ·
      refine ⟨19938697488634603249463345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13292464992423068832975563 19938697488634603249463345)
      ·
        refine ⟨14954023116475952437097509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19938697488634603249463345 14954023116475952437097509)
        ·
          refine ⟨2803879334339241081955783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14954023116475952437097509 2803879334339241081955783)
          ·
            refine ⟨4205819001508861622933675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2803879334339241081955783 4205819001508861622933675)
            ·
              refine ⟨6308728502263292434400513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4205819001508861622933675 6308728502263292434400513)
              ·
                refine ⟨4731546376697469325800385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6308728502263292434400513 4731546376697469325800385)
                ·
                  refine ⟨3548659782523101994350289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4731546376697469325800385 3548659782523101994350289)
                  ·
                    refine ⟨2661494836892326495762717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3548659782523101994350289 2661494836892326495762717)
                    ·
                      refine ⟨998060563834622435911019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2661494836892326495762717 998060563834622435911019)
                      ·
                        rfl

theorem cell23_1943716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_1943716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943716 prefixEnd_1943716 := by exact prefixLift 1943716
  have htrace : WordTrace (prefixWord ++ tailWord_1943716) baseStart_1943716 baseEnd_1943716 := by
    simpa [prefixWord, tailWord_1943716, baseEnd_1943716] using wordTrace_append hprefix tailTrace_1943716
  have hstable : (prefixWord ++ tailWord_1943716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943716).length < 2 ^ (prefixWord ++ tailWord_1943716).sum := by decide
  have hdescent : baseEnd_1943716 < baseStart_1943716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943739 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 4, 3, 2]
def baseStart_1943739 : Nat := 118140960795 + 1943739 * 2 ^ 59
def prefixEnd_1943739 : Nat := 4983230072969 + 3 ^ 40 * 1943739 * 2
def baseEnd_1943739 : Nat := 998072373889675845923413

theorem tailTrace_1943739 : CollatzResearch.WordTrace tailWord_1943739 prefixEnd_1943739 998072373889675845923413 := by
  unfold tailWord_1943739
  simp only [CollatzResearch.WordTrace]
  refine ⟨70893985505173042037290271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47262657003448694691526847 70893985505173042037290271)
  ·
    refine ⟨106340978257759563055935407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70893985505173042037290271 106340978257759563055935407)
    ·
      refine ⟨159511467386639344583903111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106340978257759563055935407 159511467386639344583903111)
      ·
        refine ⟨239267201079959016875854667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159511467386639344583903111 239267201079959016875854667)
        ·
          refine ⟨358900801619938525313782001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239267201079959016875854667 358900801619938525313782001)
          ·
            refine ⟨269175601214953893985336501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358900801619938525313782001 269175601214953893985336501)
            ·
              refine ⟨25235212613901927561125297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269175601214953893985336501 25235212613901927561125297)
              ·
                refine ⟨18926409460426445670843973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25235212613901927561125297 18926409460426445670843973)
                ·
                  refine ⟨3548701773829958563283245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18926409460426445670843973 3548701773829958563283245)
                  ·
                    refine ⟨1330763165186234461231217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3548701773829958563283245 1330763165186234461231217)
                    ·
                      refine ⟨998072373889675845923413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330763165186234461231217 998072373889675845923413)
                      ·
                        rfl

theorem cell23_1943739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 3, 2].length) (baseStart_1943739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943739 prefixEnd_1943739 := by exact prefixLift 1943739
  have htrace : WordTrace (prefixWord ++ tailWord_1943739) baseStart_1943739 baseEnd_1943739 := by
    simpa [prefixWord, tailWord_1943739, baseEnd_1943739] using wordTrace_append hprefix tailTrace_1943739
  have hstable : (prefixWord ++ tailWord_1943739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943739).length < 2 ^ (prefixWord ++ tailWord_1943739).sum := by decide
  have hdescent : baseEnd_1943739 < baseStart_1943739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943749 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 1, 5]
def baseStart_1943749 : Nat := 118140960795 + 1943749 * 2 ^ 59
def prefixEnd_1943749 : Nat := 4983230072969 + 3 ^ 40 * 1943749 * 2
def baseEnd_1943749 : Nat := 332692502898740268932789

theorem tailTrace_1943749 : CollatzResearch.WordTrace tailWord_1943749 prefixEnd_1943749 332692502898740268932789 := by
  unfold tailWord_1943749
  simp only [CollatzResearch.WordTrace]
  refine ⟨70894350235136813745154301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47262900156757875830102867 70894350235136813745154301)
  ·
    refine ⟨26585381338176305154432863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70894350235136813745154301 26585381338176305154432863)
    ·
      refine ⟨39878072007264457731649295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26585381338176305154432863 39878072007264457731649295)
      ·
        refine ⟨59817108010896686597473943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39878072007264457731649295 59817108010896686597473943)
        ·
          refine ⟨89725662016345029896210915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59817108010896686597473943 89725662016345029896210915)
          ·
            refine ⟨134588493024517544844316373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89725662016345029896210915 134588493024517544844316373)
            ·
              refine ⟨3154417805262129957288665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 134588493024517544844316373 3154417805262129957288665)
              ·
                refine ⟨2365813353946597467966499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3154417805262129957288665 2365813353946597467966499)
                ·
                  refine ⟨3548720030919896201949749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365813353946597467966499 3548720030919896201949749)
                  ·
                    refine ⟨332692502898740268932789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3548720030919896201949749 332692502898740268932789)
                    ·
                      rfl

theorem cell23_1943749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_1943749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943749 prefixEnd_1943749 := by exact prefixLift 1943749
  have htrace : WordTrace (prefixWord ++ tailWord_1943749) baseStart_1943749 baseEnd_1943749 := by
    simpa [prefixWord, tailWord_1943749, baseEnd_1943749] using wordTrace_append hprefix tailTrace_1943749
  have hstable : (prefixWord ++ tailWord_1943749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943749).length < 2 ^ (prefixWord ++ tailWord_1943749).sum := by decide
  have hdescent : baseEnd_1943749 < baseStart_1943749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943769 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 4]
def baseStart_1943769 : Nat := 118140960795 + 1943769 * 2 ^ 59
def prefixEnd_1943769 : Nat := 4983230072969 + 3 ^ 40 * 1943769 * 2
def baseEnd_1943769 : Nat := 998087778309310728548275

theorem tailTrace_1943769 : CollatzResearch.WordTrace tailWord_1943769 prefixEnd_1943769 998087778309310728548275 := by
  unfold tailWord_1943769
  simp only [CollatzResearch.WordTrace]
  refine ⟨70895079695064357160882361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47263386463376238107254907 70895079695064357160882361)
  ·
    refine ⟨53171309771298267870661771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70895079695064357160882361 53171309771298267870661771)
    ·
      refine ⟨79756964656947401805992657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53171309771298267870661771 79756964656947401805992657)
      ·
        refine ⟨59817723492710551354494493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79756964656947401805992657 59817723492710551354494493)
        ·
          refine ⟨22431646309766456757935435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59817723492710551354494493 22431646309766456757935435)
          ·
            refine ⟨33647469464649685136903153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22431646309766456757935435 33647469464649685136903153)
            ·
              refine ⟨25235602098487263852677365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33647469464649685136903153 25235602098487263852677365)
              ·
                refine ⟨2365837696733180986188503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25235602098487263852677365 2365837696733180986188503)
                ·
                  refine ⟨3548756545099771479282755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365837696733180986188503 3548756545099771479282755)
                  ·
                    refine ⟨5323134817649657218924133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3548756545099771479282755 5323134817649657218924133)
                    ·
                      refine ⟨998087778309310728548275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5323134817649657218924133 998087778309310728548275)
                      ·
                        rfl

theorem cell23_1943769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_1943769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943769 prefixEnd_1943769 := by exact prefixLift 1943769
  have htrace : WordTrace (prefixWord ++ tailWord_1943769) baseStart_1943769 baseEnd_1943769 := by
    simpa [prefixWord, tailWord_1943769, baseEnd_1943769] using wordTrace_append hprefix tailTrace_1943769
  have hstable : (prefixWord ++ tailWord_1943769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943769).length < 2 ^ (prefixWord ++ tailWord_1943769).sum := by decide
  have hdescent : baseEnd_1943769 < baseStart_1943769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943773 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1943773 : Nat := 118140960795 + 1943773 * 2 ^ 59
def prefixEnd_1943773 : Nat := 4983230072969 + 3 ^ 40 * 1943773 * 2
def baseEnd_1943773 : Nat := 998089832231928712898257

theorem tailTrace_1943773 : CollatzResearch.WordTrace tailWord_1943773 prefixEnd_1943773 998089832231928712898257 := by
  unfold tailWord_1943773
  simp only [CollatzResearch.WordTrace]
  refine ⟨70895225587049865844027973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47263483724699910562685315 70895225587049865844027973)
  ·
    refine ⟨13292854797571849845755245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70895225587049865844027973 13292854797571849845755245)
    ·
      refine ⟨4984820549089443692158217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13292854797571849845755245 4984820549089443692158217)
      ·
        refine ⟨3738615411817082769118663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4984820549089443692158217 3738615411817082769118663)
        ·
          refine ⟨5607923117725624153677995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738615411817082769118663 5607923117725624153677995)
          ·
            refine ⟨8411884676588436230516993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5607923117725624153677995 8411884676588436230516993)
            ·
              refine ⟨6308913507441327172887745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8411884676588436230516993 6308913507441327172887745)
              ·
                refine ⟨4731685130580995379665809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6308913507441327172887745 4731685130580995379665809)
                ·
                  refine ⟨3548763847935746534749357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4731685130580995379665809 3548763847935746534749357)
                  ·
                    refine ⟨1330786442975904950531009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3548763847935746534749357 1330786442975904950531009)
                    ·
                      refine ⟨998089832231928712898257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330786442975904950531009 998089832231928712898257)
                      ·
                        rfl

theorem cell23_1943773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1943773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943773 prefixEnd_1943773 := by exact prefixLift 1943773
  have htrace : WordTrace (prefixWord ++ tailWord_1943773) baseStart_1943773 baseEnd_1943773 := by
    simpa [prefixWord, tailWord_1943773, baseEnd_1943773] using wordTrace_append hprefix tailTrace_1943773
  have hstable : (prefixWord ++ tailWord_1943773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943773).length < 2 ^ (prefixWord ++ tailWord_1943773).sum := by decide
  have hdescent : baseEnd_1943773 < baseStart_1943773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943806 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1943806 : Nat := 118140960795 + 1943806 * 2 ^ 59
def prefixEnd_1943806 : Nat := 4983230072969 + 3 ^ 40 * 1943806 * 2
def baseEnd_1943806 : Nat := 998106777093527083785605

theorem tailTrace_1943806 : CollatzResearch.WordTrace tailWord_1943806 prefixEnd_1943806 998106777093527083785605 := by
  unfold tailWord_1943806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8862053649491289059997409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47264286130620208319986181 8862053649491289059997409)
  ·
    refine ⟨6646540237118466794998057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8862053649491289059997409 6646540237118466794998057)
    ·
      refine ⟨4984905177838850096248543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6646540237118466794998057 4984905177838850096248543)
      ·
        refine ⟨7477357766758275144372815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4984905177838850096248543 7477357766758275144372815)
        ·
          refine ⟨11216036650137412716559223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7477357766758275144372815 11216036650137412716559223)
          ·
            refine ⟨16824054975206119074838835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11216036650137412716559223 16824054975206119074838835)
            ·
              refine ⟨25236082462809178612258253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16824054975206119074838835 25236082462809178612258253)
              ·
                refine ⟨9463530923553441979596845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25236082462809178612258253 9463530923553441979596845)
                ·
                  refine ⟨3548824096332540742348817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9463530923553441979596845 3548824096332540742348817)
                  ·
                    refine ⟨2661618072249405556761613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3548824096332540742348817 2661618072249405556761613)
                    ·
                      refine ⟨998106777093527083785605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2661618072249405556761613 998106777093527083785605)
                      ·
                        rfl

theorem cell23_1943806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1943806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943806 prefixEnd_1943806 := by exact prefixLift 1943806
  have htrace : WordTrace (prefixWord ++ tailWord_1943806) baseStart_1943806 baseEnd_1943806 := by
    simpa [prefixWord, tailWord_1943806, baseEnd_1943806] using wordTrace_append hprefix tailTrace_1943806
  have hstable : (prefixWord ++ tailWord_1943806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943806).length < 2 ^ (prefixWord ++ tailWord_1943806).sum := by decide
  have hdescent : baseEnd_1943806 < baseStart_1943806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943809 : List Nat := [1, 2, 4, 1, 1, 2, 5, 7]
def baseStart_1943809 : Nat := 118140960795 + 1943809 * 2 ^ 59
def prefixEnd_1943809 : Nat := 4983230072969 + 3 ^ 40 * 1943809 * 2
def baseEnd_1943809 : Nat := 36966974723536687853633

theorem tailTrace_1943809 : CollatzResearch.WordTrace tailWord_1943809 prefixEnd_1943809 36966974723536687853633 := by
  unfold tailWord_1943809
  simp only [CollatzResearch.WordTrace]
  refine ⟨70896538614919443992338481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47264359076612962661558987 70896538614919443992338481)
  ·
    refine ⟨53172403961189582994253861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70896538614919443992338481 53172403961189582994253861)
    ·
      refine ⟨9969825742723046811422599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53172403961189582994253861 9969825742723046811422599)
      ·
        refine ⟨14954738614084570217133899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9969825742723046811422599 14954738614084570217133899)
        ·
          refine ⟨22432107921126855325700849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14954738614084570217133899 22432107921126855325700849)
          ·
            refine ⟨16824080940845141494275637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22432107921126855325700849 16824080940845141494275637)
            ·
              refine ⟨1577257588204232015088341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16824080940845141494275637 1577257588204232015088341)
              ·
                refine ⟨36966974723536687853633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1577257588204232015088341 36966974723536687853633)
                ·
                  rfl

theorem cell23_1943809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 7].length) (baseStart_1943809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943809 prefixEnd_1943809 := by exact prefixLift 1943809
  have htrace : WordTrace (prefixWord ++ tailWord_1943809) baseStart_1943809 baseEnd_1943809 := by
    simpa [prefixWord, tailWord_1943809, baseEnd_1943809] using wordTrace_append hprefix tailTrace_1943809
  have hstable : (prefixWord ++ tailWord_1943809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943809).length < 2 ^ (prefixWord ++ tailWord_1943809).sum := by decide
  have hdescent : baseEnd_1943809 < baseStart_1943809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943819 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 3]
def baseStart_1943819 : Nat := 118140960795 + 1943819 * 2 ^ 59
def prefixEnd_1943819 : Nat := 4983230072969 + 3 ^ 40 * 1943819 * 2
def baseEnd_1943819 : Nat := 998113452342035532923045

theorem tailTrace_1943819 : CollatzResearch.WordTrace tailWord_1943819 prefixEnd_1943819 998113452342035532923045 := by
  unfold tailWord_1943819
  simp only [CollatzResearch.WordTrace]
  refine ⟨70896903344883215700202511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47264602229922143800135007 70896903344883215700202511)
  ·
    refine ⟨106345355017324823550303767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70896903344883215700202511 106345355017324823550303767)
    ·
      refine ⟨159518032525987235325455651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106345355017324823550303767 159518032525987235325455651)
      ·
        refine ⟨239277048788980852988183477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159518032525987235325455651 239277048788980852988183477)
        ·
          refine ⟨22432223323966954967642201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239277048788980852988183477 22432223323966954967642201)
          ·
            refine ⟨16824167492975216225731651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22432223323966954967642201 16824167492975216225731651)
            ·
              refine ⟨25236251239462824338597477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16824167492975216225731651 25236251239462824338597477)
              ·
                refine ⟨4731797107399279563487027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25236251239462824338597477 4731797107399279563487027)
                ·
                  refine ⟨7097695661098919345230541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731797107399279563487027 7097695661098919345230541)
                  ·
                    refine ⟨2661635872912094754461453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7097695661098919345230541 2661635872912094754461453)
                    ·
                      refine ⟨998113452342035532923045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2661635872912094754461453 998113452342035532923045)
                      ·
                        rfl

theorem cell23_1943819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 3].length) (baseStart_1943819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943819 prefixEnd_1943819 := by exact prefixLift 1943819
  have htrace : WordTrace (prefixWord ++ tailWord_1943819) baseStart_1943819 baseEnd_1943819 := by
    simpa [prefixWord, tailWord_1943819, baseEnd_1943819] using wordTrace_append hprefix tailTrace_1943819
  have hstable : (prefixWord ++ tailWord_1943819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943819).length < 2 ^ (prefixWord ++ tailWord_1943819).sum := by decide
  have hdescent : baseEnd_1943819 < baseStart_1943819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943820 : List Nat := [2, 2, 1, 2, 2, 2, 4, 3, 1, 2, 2]
def baseStart_1943820 : Nat := 118140960795 + 1943820 * 2 ^ 59
def prefixEnd_1943820 : Nat := 4983230072969 + 3 ^ 40 * 1943820 * 2
def baseEnd_1943820 : Nat := 998113965822690029010541

theorem tailTrace_1943820 : CollatzResearch.WordTrace tailWord_1943820 prefixEnd_1943820 998113965822690029010541 := by
  unfold tailWord_1943820
  simp only [CollatzResearch.WordTrace]
  refine ⟨35448469908939796435494457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47264626545253061913992609 35448469908939796435494457)
  ·
    refine ⟨26586352431704847326620843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35448469908939796435494457 26586352431704847326620843)
    ·
      refine ⟨39879528647557270989931265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26586352431704847326620843 39879528647557270989931265)
      ·
        refine ⟨29909646485667953242448449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39879528647557270989931265 29909646485667953242448449)
        ·
          refine ⟨22432234864250964931836337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29909646485667953242448449 22432234864250964931836337)
          ·
            refine ⟨16824176148188223698877253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22432234864250964931836337 16824176148188223698877253)
            ·
              refine ⟨3154533027785291943539485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16824176148188223698877253 3154533027785291943539485)
              ·
                refine ⟨1182949885419484478827307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3154533027785291943539485 1182949885419484478827307)
                ·
                  refine ⟨1774424828129226718240961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1182949885419484478827307 1774424828129226718240961)
                  ·
                    refine ⟨1330818621096920038680721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1774424828129226718240961 1330818621096920038680721)
                    ·
                      refine ⟨998113965822690029010541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330818621096920038680721 998113965822690029010541)
                      ·
                        rfl

theorem cell23_1943820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_1943820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943820 prefixEnd_1943820 := by exact prefixLift 1943820
  have htrace : WordTrace (prefixWord ++ tailWord_1943820) baseStart_1943820 baseEnd_1943820 := by
    simpa [prefixWord, tailWord_1943820, baseEnd_1943820] using wordTrace_append hprefix tailTrace_1943820
  have hstable : (prefixWord ++ tailWord_1943820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943820).length < 2 ^ (prefixWord ++ tailWord_1943820).sum := by decide
  have hdescent : baseEnd_1943820 < baseStart_1943820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943847 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1943847 : Nat := 118140960795 + 1943847 * 2 ^ 59
def prefixEnd_1943847 : Nat := 4983230072969 + 3 ^ 40 * 1943847 * 2
def baseEnd_1943847 : Nat := 332709276600120474457639

theorem tailTrace_1943847 : CollatzResearch.WordTrace tailWord_1943847 prefixEnd_1943847 332709276600120474457639 := by
  unfold tailWord_1943847
  simp only [CollatzResearch.WordTrace]
  refine ⟨70897924588781776482221795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47265283059187850988147863 70897924588781776482221795)
  ·
    refine ⟨106346886883172664723332693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70897924588781776482221795 106346886883172664723332693)
    ·
      refine ⟨1246252580662179664726555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 106346886883172664723332693 1246252580662179664726555)
      ·
        refine ⟨1869378870993269497089833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246252580662179664726555 1869378870993269497089833)
        ·
          refine ⟨1402034153244952122817375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1869378870993269497089833 1402034153244952122817375)
          ·
            refine ⟨2103051229867428184226063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402034153244952122817375 2103051229867428184226063)
            ·
              refine ⟨3154576844801142276339095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103051229867428184226063 3154576844801142276339095)
              ·
                refine ⟨4731865267201713414508643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154576844801142276339095 4731865267201713414508643)
                ·
                  refine ⟨7097797900802570121762965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731865267201713414508643 7097797900802570121762965)
                  ·
                    refine ⟨332709276600120474457639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7097797900802570121762965 332709276600120474457639)
                    ·
                      rfl

theorem cell23_1943847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1943847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943847 prefixEnd_1943847 := by exact prefixLift 1943847
  have htrace : WordTrace (prefixWord ++ tailWord_1943847) baseStart_1943847 baseEnd_1943847 := by
    simpa [prefixWord, tailWord_1943847, baseEnd_1943847] using wordTrace_append hprefix tailTrace_1943847
  have hstable : (prefixWord ++ tailWord_1943847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943847).length < 2 ^ (prefixWord ++ tailWord_1943847).sum := by decide
  have hdescent : baseEnd_1943847 < baseStart_1943847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943850 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1943850 : Nat := 118140960795 + 1943850 * 2 ^ 59
def prefixEnd_1943850 : Nat := 4983230072969 + 3 ^ 40 * 1943850 * 2
def baseEnd_1943850 : Nat := 998129370242324911635403

theorem tailTrace_1943850 : CollatzResearch.WordTrace tailWord_1943850 prefixEnd_1943850 998129370242324911635403 := by
  unfold tailWord_1943850
  simp only [CollatzResearch.WordTrace]
  refine ⟨17724508501942726998645251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47265356005180605329720669 17724508501942726998645251)
  ·
    refine ⟨26586762752914090497967877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17724508501942726998645251 26586762752914090497967877)
    ·
      refine ⟨4985018016171391968368977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26586762752914090497967877 4985018016171391968368977)
      ·
        refine ⟨3738763512128543976276733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4985018016171391968368977 3738763512128543976276733)
        ·
          refine ⟨1402036317048203991103775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3738763512128543976276733 1402036317048203991103775)
          ·
            refine ⟨2103054475572305986655663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402036317048203991103775 2103054475572305986655663)
            ·
              refine ⟨3154581713358458979983495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103054475572305986655663 3154581713358458979983495)
              ·
                refine ⟨4731872570037688469975243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154581713358458979983495 4731872570037688469975243)
                ·
                  refine ⟨7097808855056532704962865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731872570037688469975243 7097808855056532704962865)
                  ·
                    refine ⟨5323356641292399528722149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7097808855056532704962865 5323356641292399528722149)
                    ·
                      refine ⟨998129370242324911635403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5323356641292399528722149 998129370242324911635403)
                      ·
                        rfl

theorem cell23_1943850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1943850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943850 prefixEnd_1943850 := by exact prefixLift 1943850
  have htrace : WordTrace (prefixWord ++ tailWord_1943850) baseStart_1943850 baseEnd_1943850 := by
    simpa [prefixWord, tailWord_1943850, baseEnd_1943850] using wordTrace_append hprefix tailTrace_1943850
  have hstable : (prefixWord ++ tailWord_1943850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943850).length < 2 ^ (prefixWord ++ tailWord_1943850).sum := by decide
  have hdescent : baseEnd_1943850 < baseStart_1943850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943879 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1943879 : Nat := 118140960795 + 1943879 * 2 ^ 59
def prefixEnd_1943879 : Nat := 4983230072969 + 3 ^ 40 * 1943879 * 2
def baseEnd_1943879 : Nat := 998144261181305298172769

theorem tailTrace_1943879 : CollatzResearch.WordTrace tailWord_1943879 prefixEnd_1943879 998144261181305298172769 := by
  unfold tailWord_1943879
  simp only [CollatzResearch.WordTrace]
  refine ⟨70899091724665845947386691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47266061149777230631591127 70899091724665845947386691)
  ·
    refine ⟨106348637586998768921080037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70899091724665845947386691 106348637586998768921080037)
    ·
      refine ⟨19940369547562269172702507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106348637586998768921080037 19940369547562269172702507)
      ·
        refine ⟨29910554321343403759053761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19940369547562269172702507 29910554321343403759053761)
        ·
          refine ⟨22432915741007552819290321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29910554321343403759053761 22432915741007552819290321)
          ·
            refine ⟨16824686805755664614467741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22432915741007552819290321 16824686805755664614467741)
            ·
              refine ⟨6309257552158374230425403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16824686805755664614467741 6309257552158374230425403)
              ·
                refine ⟨9463886328237561345638105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309257552158374230425403 9463886328237561345638105)
                ·
                  refine ⟨7097914746178171009228579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9463886328237561345638105 7097914746178171009228579)
                  ·
                    refine ⟨10646872119267256513842869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7097914746178171009228579 10646872119267256513842869)
                    ·
                      refine ⟨998144261181305298172769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10646872119267256513842869 998144261181305298172769)
                      ·
                        rfl

theorem cell23_1943879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1943879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943879 prefixEnd_1943879 := by exact prefixLift 1943879
  have htrace : WordTrace (prefixWord ++ tailWord_1943879) baseStart_1943879 baseEnd_1943879 := by
    simpa [prefixWord, tailWord_1943879, baseEnd_1943879] using wordTrace_append hprefix tailTrace_1943879
  have hstable : (prefixWord ++ tailWord_1943879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943879).length < 2 ^ (prefixWord ++ tailWord_1943879).sum := by decide
  have hdescent : baseEnd_1943879 < baseStart_1943879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943950 : List Nat := [4, 1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_1943950 : Nat := 118140960795 + 1943950 * 2 ^ 59
def prefixEnd_1943950 : Nat := 4983230072969 + 3 ^ 40 * 1943950 * 2
def baseEnd_1943950 : Nat := 110908968700863835598327

theorem tailTrace_1943950 : CollatzResearch.WordTrace tailWord_1943950 prefixEnd_1943950 110908968700863835598327 := by
  unfold tailWord_1943950
  simp only [CollatzResearch.WordTrace]
  refine ⟨8862710163426078134152663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47267787538272416715480869 8862710163426078134152663)
  ·
    refine ⟨13294065245139117201228995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8862710163426078134152663 13294065245139117201228995)
    ·
      refine ⟨19941097867708675801843493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13294065245139117201228995 19941097867708675801843493)
      ·
        refine ⟨3738955850195376712845655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19941097867708675801843493 3738955850195376712845655)
        ·
          refine ⟨5608433775293065069268483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738955850195376712845655 5608433775293065069268483)
          ·
            refine ⟨8412650662939597603902725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608433775293065069268483 8412650662939597603902725)
            ·
              refine ⟨1577371999301174550731761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8412650662939597603902725 1577371999301174550731761)
              ·
                refine ⟨1183028999475880913048821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577371999301174550731761 1183028999475880913048821)
                ·
                  refine ⟨110908968700863835598327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1183028999475880913048821 110908968700863835598327)
                  ·
                    rfl

theorem cell23_1943950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_1943950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943950 prefixEnd_1943950 := by exact prefixLift 1943950
  have htrace : WordTrace (prefixWord ++ tailWord_1943950) baseStart_1943950 baseEnd_1943950 := by
    simpa [prefixWord, tailWord_1943950, baseEnd_1943950] using wordTrace_append hprefix tailTrace_1943950
  have hstable : (prefixWord ++ tailWord_1943950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943950).length < 2 ^ (prefixWord ++ tailWord_1943950).sum := by decide
  have hdescent : baseEnd_1943950 < baseStart_1943950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943986 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_1943986 : Nat := 118140960795 + 1943986 * 2 ^ 59
def prefixEnd_1943986 : Nat := 4983230072969 + 3 ^ 40 * 1943986 * 2
def baseEnd_1943986 : Nat := 998199203611336379534777

theorem tailTrace_1943986 : CollatzResearch.WordTrace tailWord_1943986 prefixEnd_1943986 998199203611336379534777 := by
  unfold tailWord_1943986
  simp only [CollatzResearch.WordTrace]
  refine ⟨17725748583819550805382953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47268662890185468814354541 17725748583819550805382953)
  ·
    refine ⟨13294311437864663104037215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17725748583819550805382953 13294311437864663104037215)
    ·
      refine ⟨19941467156796994656055823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13294311437864663104037215 19941467156796994656055823)
      ·
        refine ⟨29912200735195491984083735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19941467156796994656055823 29912200735195491984083735)
        ·
          refine ⟨44868301102793237976125603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29912200735195491984083735 44868301102793237976125603)
          ·
            refine ⟨67302451654189856964188405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44868301102793237976125603 67302451654189856964188405)
            ·
              refine ⟨6309604842580299090392663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67302451654189856964188405 6309604842580299090392663)
              ·
                refine ⟨9464407263870448635588995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309604842580299090392663 9464407263870448635588995)
                ·
                  refine ⟨14196610895805672953383493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9464407263870448635588995 14196610895805672953383493)
                  ·
                    refine ⟨2661864542963563678759405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14196610895805672953383493 2661864542963563678759405)
                    ·
                      refine ⟨998199203611336379534777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2661864542963563678759405 998199203611336379534777)
                      ·
                        rfl

theorem cell23_1943986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_1943986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943986 prefixEnd_1943986 := by exact prefixLift 1943986
  have htrace : WordTrace (prefixWord ++ tailWord_1943986) baseStart_1943986 baseEnd_1943986 := by
    simpa [prefixWord, tailWord_1943986, baseEnd_1943986] using wordTrace_append hprefix tailTrace_1943986
  have hstable : (prefixWord ++ tailWord_1943986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943986).length < 2 ^ (prefixWord ++ tailWord_1943986).sum := by decide
  have hdescent : baseEnd_1943986 < baseStart_1943986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1943996 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1943996 : Nat := 118140960795 + 1943996 * 2 ^ 59
def prefixEnd_1943996 : Nat := 4983230072969 + 3 ^ 40 * 1943996 * 2
def baseEnd_1943996 : Nat := 998204338417881340409731

theorem tailTrace_1943996 : CollatzResearch.WordTrace tailWord_1943996 prefixEnd_1943996 998204338417881340409731 := by
  unfold tailWord_1943996
  simp only [CollatzResearch.WordTrace]
  refine ⟨35451679532620987464697921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47268906043494649952930561 35451679532620987464697921)
  ·
    refine ⟨26588759649465740598523441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35451679532620987464697921 26588759649465740598523441)
    ·
      refine ⟨19941569737099305448892581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26588759649465740598523441 19941569737099305448892581)
      ·
        refine ⟨3739044325706119771667359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19941569737099305448892581 3739044325706119771667359)
        ·
          refine ⟨5608566488559179657501039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3739044325706119771667359 5608566488559179657501039)
          ·
            refine ⟨8412849732838769486251559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608566488559179657501039 8412849732838769486251559)
            ·
              refine ⟨12619274599258154229377339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8412849732838769486251559 12619274599258154229377339)
              ·
                refine ⟨18928911898887231344066009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12619274599258154229377339 18928911898887231344066009)
                ·
                  refine ⟨14196683924165423508049507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18928911898887231344066009 14196683924165423508049507)
                  ·
                    refine ⟨21295025886248135262074261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14196683924165423508049507 21295025886248135262074261)
                    ·
                      refine ⟨998204338417881340409731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21295025886248135262074261 998204338417881340409731)
                      ·
                        rfl

theorem cell23_1943996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1943996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1943996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1943996 prefixEnd_1943996 := by exact prefixLift 1943996
  have htrace : WordTrace (prefixWord ++ tailWord_1943996) baseStart_1943996 baseEnd_1943996 := by
    simpa [prefixWord, tailWord_1943996, baseEnd_1943996] using wordTrace_append hprefix tailTrace_1943996
  have hstable : (prefixWord ++ tailWord_1943996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1943996).length < 2 ^ (prefixWord ++ tailWord_1943996).sum := by decide
  have hdescent : baseEnd_1943996 < baseStart_1943996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1943996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944009 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_1944009 : Nat := 118140960795 + 1944009 * 2 ^ 59
def prefixEnd_1944009 : Nat := 4983230072969 + 3 ^ 40 * 1944009 * 2
def baseEnd_1944009 : Nat := 998211013666389789547171

theorem tailTrace_1944009 : CollatzResearch.WordTrace tailWord_1944009 prefixEnd_1944009 998211013666389789547171 := by
  unfold tailWord_1944009
  simp only [CollatzResearch.WordTrace]
  refine ⟨70903833214194878149619081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47269222142796585433079387 70903833214194878149619081)
  ·
    refine ⟨53177874910646158612214311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70903833214194878149619081 53177874910646158612214311)
    ·
      refine ⟨79766812365969237918321467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53177874910646158612214311 79766812365969237918321467)
      ·
        refine ⟨119650218548953856877482201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79766812365969237918321467 119650218548953856877482201)
        ·
          refine ⟨89737663911715392658111651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119650218548953856877482201 89737663911715392658111651)
          ·
            refine ⟨134606495867573088987167477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89737663911715392658111651 134606495867573088987167477)
            ·
              refine ⟨12619358987584977092546951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134606495867573088987167477 12619358987584977092546951)
              ·
                refine ⟨18929038481377465638820427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12619358987584977092546951 18929038481377465638820427)
                ·
                  refine ⟨28393557722066198458230641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18929038481377465638820427 28393557722066198458230641)
                  ·
                    refine ⟨21295168291549648843672981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28393557722066198458230641 21295168291549648843672981)
                    ·
                      refine ⟨998211013666389789547171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21295168291549648843672981 998211013666389789547171)
                      ·
                        rfl

theorem cell23_1944009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_1944009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944009 prefixEnd_1944009 := by exact prefixLift 1944009
  have htrace : WordTrace (prefixWord ++ tailWord_1944009) baseStart_1944009 baseEnd_1944009 := by
    simpa [prefixWord, tailWord_1944009, baseEnd_1944009] using wordTrace_append hprefix tailTrace_1944009
  have hstable : (prefixWord ++ tailWord_1944009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944009).length < 2 ^ (prefixWord ++ tailWord_1944009).sum := by decide
  have hdescent : baseEnd_1944009 < baseStart_1944009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944033 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_1944033 : Nat := 118140960795 + 1944033 * 2 ^ 59
def prefixEnd_1944033 : Nat := 4983230072969 + 3 ^ 40 * 1944033 * 2
def baseEnd_1944033 : Nat := 998223337202097695647061

theorem tailTrace_1944033 : CollatzResearch.WordTrace tailWord_1944033 prefixEnd_1944033 998223337202097695647061 := by
  unfold tailWord_1944033
  simp only [CollatzResearch.WordTrace]
  refine ⟨70904708566107930248492753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47269805710738620165661835 70904708566107930248492753)
  ·
    refine ⟨53178531424580947686369565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70904708566107930248492753 53178531424580947686369565)
    ·
      refine ⟨19941949284217855382388587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53178531424580947686369565 19941949284217855382388587)
      ·
        refine ⟨29912923926326783073582881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19941949284217855382388587 29912923926326783073582881)
        ·
          refine ⟨22434692944745087305187161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29912923926326783073582881 22434692944745087305187161)
          ·
            refine ⟨16826019708558815478890371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22434692944745087305187161 16826019708558815478890371)
            ·
              refine ⟨25239029562838223218335557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16826019708558815478890371 25239029562838223218335557)
              ·
                refine ⟨4732318043032166853437917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25239029562838223218335557 4732318043032166853437917)
                ·
                  refine ⟨1774619266137062570039219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4732318043032166853437917 1774619266137062570039219)
                  ·
                    refine ⟨2661928899205593855058829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1774619266137062570039219 2661928899205593855058829)
                    ·
                      refine ⟨998223337202097695647061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2661928899205593855058829 998223337202097695647061)
                      ·
                        rfl

theorem cell23_1944033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_1944033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944033 prefixEnd_1944033 := by exact prefixLift 1944033
  have htrace : WordTrace (prefixWord ++ tailWord_1944033) baseStart_1944033 baseEnd_1944033 := by
    simpa [prefixWord, tailWord_1944033, baseEnd_1944033] using wordTrace_append hprefix tailTrace_1944033
  have hstable : (prefixWord ++ tailWord_1944033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944033).length < 2 ^ (prefixWord ++ tailWord_1944033).sum := by decide
  have hdescent : baseEnd_1944033 < baseStart_1944033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944043 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 2, 3, 2]
def baseStart_1944043 : Nat := 118140960795 + 1944043 * 2 ^ 59
def prefixEnd_1944043 : Nat := 4983230072969 + 3 ^ 40 * 1944043 * 2
def baseEnd_1944043 : Nat := 998228472008642656522015

theorem tailTrace_1944043 : CollatzResearch.WordTrace tailWord_1944043 prefixEnd_1944043 998228472008642656522015 := by
  unfold tailWord_1944043
  simp only [CollatzResearch.WordTrace]
  refine ⟨70905073296071701956356783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47270048864047801304237855 70905073296071701956356783)
  ·
    refine ⟨106357609944107552934535175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70905073296071701956356783 106357609944107552934535175)
    ·
      refine ⟨159536414916161329401802763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106357609944107552934535175 159536414916161329401802763)
      ·
        refine ⟨239304622374241994102704145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159536414916161329401802763 239304622374241994102704145)
        ·
          refine ⟨179478466780681495577028109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239304622374241994102704145 179478466780681495577028109)
          ·
            refine ⟨67304425042755560841385541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179478466780681495577028109 67304425042755560841385541)
            ·
              refine ⟨12619579695516667657759789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67304425042755560841385541 12619579695516667657759789)
              ·
                refine ⟨4732342385818750371659921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12619579695516667657759789 4732342385818750371659921)
                ·
                  refine ⟨3549256789364062778744941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4732342385818750371659921 3549256789364062778744941)
                  ·
                    refine ⟨1330971296011523542029353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3549256789364062778744941 1330971296011523542029353)
                    ·
                      refine ⟨998228472008642656522015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1330971296011523542029353 998228472008642656522015)
                      ·
                        rfl

theorem cell23_1944043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 3, 2].length) (baseStart_1944043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944043 prefixEnd_1944043 := by exact prefixLift 1944043
  have htrace : WordTrace (prefixWord ++ tailWord_1944043) baseStart_1944043 baseEnd_1944043 := by
    simpa [prefixWord, tailWord_1944043, baseEnd_1944043] using wordTrace_append hprefix tailTrace_1944043
  have hstable : (prefixWord ++ tailWord_1944043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944043).length < 2 ^ (prefixWord ++ tailWord_1944043).sum := by decide
  have hdescent : baseEnd_1944043 < baseStart_1944043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944067 : List Nat := [1, 1, 1, 3, 2, 1, 7, 2, 1, 1, 3]
def baseStart_1944067 : Nat := 118140960795 + 1944067 * 2 ^ 59
def prefixEnd_1944067 : Nat := 4983230072969 + 3 ^ 40 * 1944067 * 2
def baseEnd_1944067 : Nat := 998240795544350562621905

theorem tailTrace_1944067 : CollatzResearch.WordTrace tailWord_1944067 prefixEnd_1944067 998240795544350562621905 := by
  unfold tailWord_1944067
  simp only [CollatzResearch.WordTrace]
  refine ⟨70905948647984754055230455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47270632431989836036820303 70905948647984754055230455)
  ·
    refine ⟨106358922971977131082845683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70905948647984754055230455 106358922971977131082845683)
    ·
      refine ⟨159538384457965696624268525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106358922971977131082845683 159538384457965696624268525)
      ·
        refine ⟨59826894171737136234100697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159538384457965696624268525 59826894171737136234100697)
        ·
          refine ⟨44870170628802852175575523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59826894171737136234100697 44870170628802852175575523)
          ·
            refine ⟨67305255943204278263363285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44870170628802852175575523 67305255943204278263363285)
            ·
              refine ⟨1577466936168850271797577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 67305255943204278263363285 1577466936168850271797577)
              ·
                refine ⟨1183100202126637703848183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1577466936168850271797577 1183100202126637703848183)
                ·
                  refine ⟨1774650303189956555772275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183100202126637703848183 1774650303189956555772275)
                  ·
                    refine ⟨2661975454784934833658413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1774650303189956555772275 2661975454784934833658413)
                    ·
                      refine ⟨998240795544350562621905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2661975454784934833658413 998240795544350562621905)
                      ·
                        rfl

theorem cell23_1944067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 1, 1, 3].length) (baseStart_1944067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944067 prefixEnd_1944067 := by exact prefixLift 1944067
  have htrace : WordTrace (prefixWord ++ tailWord_1944067) baseStart_1944067 baseEnd_1944067 := by
    simpa [prefixWord, tailWord_1944067, baseEnd_1944067] using wordTrace_append hprefix tailTrace_1944067
  have hstable : (prefixWord ++ tailWord_1944067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944067).length < 2 ^ (prefixWord ++ tailWord_1944067).sum := by decide
  have hdescent : baseEnd_1944067 < baseStart_1944067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944079 : List Nat := [1, 1, 2, 1, 1, 1, 2, 14]
def baseStart_1944079 : Nat := 118140960795 + 1944079 * 2 ^ 59
def prefixEnd_1944079 : Nat := 4983230072969 + 3 ^ 40 * 1944079 * 2
def baseEnd_1944079 : Nat := 36972109530081648728587

theorem tailTrace_1944079 : CollatzResearch.WordTrace tailWord_1944079 prefixEnd_1944079 36972109530081648728587 := by
  unfold tailWord_1944079
  simp only [CollatzResearch.WordTrace]
  refine ⟨70906386323941280104667291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47270924215960853403111527 70906386323941280104667291)
  ·
    refine ⟨106359579485911920157000937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70906386323941280104667291 106359579485911920157000937)
    ·
      refine ⟨79769684614433940117750703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106359579485911920157000937 79769684614433940117750703)
      ·
        refine ⟨119654526921650910176626055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79769684614433940117750703 119654526921650910176626055)
        ·
          refine ⟨179481790382476365264939083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119654526921650910176626055 179481790382476365264939083)
          ·
            refine ⟨269222685573714547897408625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179481790382476365264939083 269222685573714547897408625)
            ·
              refine ⟨201917014180285910923056469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269222685573714547897408625 201917014180285910923056469)
              ·
                refine ⟨36972109530081648728587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 201917014180285910923056469 36972109530081648728587)
                ·
                  rfl

theorem cell23_1944079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 14].length) (baseStart_1944079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944079 prefixEnd_1944079 := by exact prefixLift 1944079
  have htrace : WordTrace (prefixWord ++ tailWord_1944079) baseStart_1944079 baseEnd_1944079 := by
    simpa [prefixWord, tailWord_1944079, baseEnd_1944079] using wordTrace_append hprefix tailTrace_1944079
  have hstable : (prefixWord ++ tailWord_1944079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944079).length < 2 ^ (prefixWord ++ tailWord_1944079).sum := by decide
  have hdescent : baseEnd_1944079 < baseStart_1944079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944083 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 2, 4]
def baseStart_1944083 : Nat := 118140960795 + 1944083 * 2 ^ 59
def prefixEnd_1944083 : Nat := 4983230072969 + 3 ^ 40 * 1944083 * 2
def baseEnd_1944083 : Nat := 332749670411607500007277

theorem tailTrace_1944083 : CollatzResearch.WordTrace tailWord_1944083 prefixEnd_1944083 332749670411607500007277 := by
  unfold tailWord_1944083
  simp only [CollatzResearch.WordTrace]
  refine ⟨70906532215926788787812903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47271021477284525858541935 70906532215926788787812903)
  ·
    refine ⟨106359798323890183181719355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70906532215926788787812903 106359798323890183181719355)
    ·
      refine ⟨159539697485835274772579033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106359798323890183181719355 159539697485835274772579033)
      ·
        refine ⟨119654773114376456079434275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159539697485835274772579033 119654773114376456079434275)
        ·
          refine ⟨179482159671564684119151413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119654773114376456079434275 179482159671564684119151413)
          ·
            refine ⟨16826452469209189136170445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179482159671564684119151413 16826452469209189136170445)
            ·
              refine ⟨6309919675953445926063917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16826452469209189136170445 6309919675953445926063917)
              ·
                refine ⟨2366219878482542222273969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6309919675953445926063917 2366219878482542222273969)
                ·
                  refine ⟨1774664908861906666705477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2366219878482542222273969 1774664908861906666705477)
                  ·
                    refine ⟨332749670411607500007277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1774664908861906666705477 332749670411607500007277)
                    ·
                      rfl

theorem cell23_1944083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 4].length) (baseStart_1944083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944083 prefixEnd_1944083 := by exact prefixLift 1944083
  have htrace : WordTrace (prefixWord ++ tailWord_1944083) baseStart_1944083 baseEnd_1944083 := by
    simpa [prefixWord, tailWord_1944083, baseEnd_1944083] using wordTrace_append hprefix tailTrace_1944083
  have hstable : (prefixWord ++ tailWord_1944083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944083).length < 2 ^ (prefixWord ++ tailWord_1944083).sum := by decide
  have hdescent : baseEnd_1944083 < baseStart_1944083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944087 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 1, 5]
def baseStart_1944087 : Nat := 118140960795 + 1944087 * 2 ^ 59
def prefixEnd_1944087 : Nat := 4983230072969 + 3 ^ 40 * 1944087 * 2
def baseEnd_1944087 : Nat := 332750355052480161457271

theorem tailTrace_1944087 : CollatzResearch.WordTrace tailWord_1944087 prefixEnd_1944087 332750355052480161457271 := by
  unfold tailWord_1944087
  simp only [CollatzResearch.WordTrace]
  refine ⟨70906678107912297470958515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47271118738608198313972343 70906678107912297470958515)
  ·
    refine ⟨106360017161868446206437773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70906678107912297470958515 106360017161868446206437773)
    ·
      refine ⟨39885006435700667327414165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106360017161868446206437773 39885006435700667327414165)
      ·
        refine ⟨1869609676673468780972539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39885006435700667327414165 1869609676673468780972539)
        ·
          refine ⟨2804414515010203171458809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869609676673468780972539 2804414515010203171458809)
          ·
            refine ⟨2103310886257652378594107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2804414515010203171458809 2103310886257652378594107)
            ·
              refine ⟨3154966329386478567891161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103310886257652378594107 3154966329386478567891161)
              ·
                refine ⟨2366224747039858925918371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3154966329386478567891161 2366224747039858925918371)
                ·
                  refine ⟨3549337120559788388877557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366224747039858925918371 3549337120559788388877557)
                  ·
                    refine ⟨332750355052480161457271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3549337120559788388877557 332750355052480161457271)
                    ·
                      rfl

theorem cell23_1944087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_1944087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944087 prefixEnd_1944087 := by exact prefixLift 1944087
  have htrace : WordTrace (prefixWord ++ tailWord_1944087) baseStart_1944087 baseEnd_1944087 := by
    simpa [prefixWord, tailWord_1944087, baseEnd_1944087] using wordTrace_append hprefix tailTrace_1944087
  have hstable : (prefixWord ++ tailWord_1944087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944087).length < 2 ^ (prefixWord ++ tailWord_1944087).sum := by decide
  have hdescent : baseEnd_1944087 < baseStart_1944087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944090 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2]
def baseStart_1944090 : Nat := 118140960795 + 1944090 * 2 ^ 59
def prefixEnd_1944090 : Nat := 4983230072969 + 3 ^ 40 * 1944090 * 2
def baseEnd_1944090 : Nat := 998252605599403972634299

theorem tailTrace_1944090 : CollatzResearch.WordTrace tailWord_1944090 prefixEnd_1944090 998252605599403972634299 := by
  unfold tailWord_1944090
  simp only [CollatzResearch.WordTrace]
  refine ⟨17726696881725357245829431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47271191684600952655545149 17726696881725357245829431)
  ·
    refine ⟨26590045322588035868744147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17726696881725357245829431 26590045322588035868744147)
    ·
      refine ⟨39885067983882053803116221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26590045322588035868744147 39885067983882053803116221)
      ·
        refine ⟨14956900493955770176168583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39885067983882053803116221 14956900493955770176168583)
        ·
          refine ⟨22435350740933655264252875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14956900493955770176168583 22435350740933655264252875)
          ·
            refine ⟨33653026111400482896379313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22435350740933655264252875 33653026111400482896379313)
            ·
              refine ⟨25239769583550362172284485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33653026111400482896379313 25239769583550362172284485)
              ·
                refine ⟨4732456796915692907303341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25239769583550362172284485 4732456796915692907303341)
                ·
                  refine ⟨1774671298843384840238753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4732456796915692907303341 1774671298843384840238753)
                  ·
                    refine ⟨1331003474132538630179065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1774671298843384840238753 1331003474132538630179065)
                    ·
                      refine ⟨998252605599403972634299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1331003474132538630179065 998252605599403972634299)
                      ·
                        rfl

theorem cell23_1944090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_1944090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944090 prefixEnd_1944090 := by exact prefixLift 1944090
  have htrace : WordTrace (prefixWord ++ tailWord_1944090) baseStart_1944090 baseEnd_1944090 := by
    simpa [prefixWord, tailWord_1944090, baseEnd_1944090] using wordTrace_append hprefix tailTrace_1944090
  have hstable : (prefixWord ++ tailWord_1944090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944090).length < 2 ^ (prefixWord ++ tailWord_1944090).sum := by decide
  have hdescent : baseEnd_1944090 < baseStart_1944090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944100 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_1944100 : Nat := 118140960795 + 1944100 * 2 ^ 59
def prefixEnd_1944100 : Nat := 4983230072969 + 3 ^ 40 * 1944100 * 2
def baseEnd_1944100 : Nat := 332752580135316311169751

theorem tailTrace_1944100 : CollatzResearch.WordTrace tailWord_1944100 prefixEnd_1944100 332752580135316311169751 := by
  unfold tailWord_1944100
  simp only [CollatzResearch.WordTrace]
  refine ⟨35453576128432600345590877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47271434837910133794121169 35453576128432600345590877)
  ·
    refine ⟨13295091048162225129596579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35453576128432600345590877 13295091048162225129596579)
    ·
      refine ⟨19942636572243337694394869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13295091048162225129596579 19942636572243337694394869)
      ·
        refine ⟨1869622178647812908849519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19942636572243337694394869 1869622178647812908849519)
        ·
          refine ⟨2804433267971719363274279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869622178647812908849519 2804433267971719363274279)
          ·
            refine ⟨4206649901957579044911419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804433267971719363274279 4206649901957579044911419)
            ·
              refine ⟨6309974852936368567367129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206649901957579044911419 6309974852936368567367129)
              ·
                refine ⟨4732481139702276425525347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6309974852936368567367129 4732481139702276425525347)
                ·
                  refine ⟨7098721709553414638288021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732481139702276425525347 7098721709553414638288021)
                  ·
                    refine ⟨332752580135316311169751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7098721709553414638288021 332752580135316311169751)
                    ·
                      rfl

theorem cell23_1944100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_1944100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944100 prefixEnd_1944100 := by exact prefixLift 1944100
  have htrace : WordTrace (prefixWord ++ tailWord_1944100) baseStart_1944100 baseEnd_1944100 := by
    simpa [prefixWord, tailWord_1944100, baseEnd_1944100] using wordTrace_append hprefix tailTrace_1944100
  have hstable : (prefixWord ++ tailWord_1944100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944100).length < 2 ^ (prefixWord ++ tailWord_1944100).sum := by decide
  have hdescent : baseEnd_1944100 < baseStart_1944100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944124 : List Nat := [2, 2, 2, 2, 3, 2, 1, 4, 1, 2, 2]
def baseStart_1944124 : Nat := 118140960795 + 1944124 * 2 ^ 59
def prefixEnd_1944124 : Nat := 4983230072969 + 3 ^ 40 * 1944124 * 2
def baseEnd_1944124 : Nat := 998270063941656839609143

theorem tailTrace_1944124 : CollatzResearch.WordTrace tailWord_1944124 prefixEnd_1944124 998270063941656839609143 := by
  unfold tailWord_1944124
  simp only [CollatzResearch.WordTrace]
  refine ⟨35454013804389126395027713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47272018405852168526703617 35454013804389126395027713)
  ·
    refine ⟨26590510353291844796270785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35454013804389126395027713 26590510353291844796270785)
    ·
      refine ⟨19942882764968883597203089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26590510353291844796270785 19942882764968883597203089)
      ·
        refine ⟨14957162073726662697902317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19942882764968883597203089 14957162073726662697902317)
        ·
          refine ⟨5608935777647498511713369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14957162073726662697902317 5608935777647498511713369)
          ·
            refine ⟨4206701833235623883785027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5608935777647498511713369 4206701833235623883785027)
            ·
              refine ⟨6310052749853435825677541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206701833235623883785027 6310052749853435825677541)
              ·
                refine ⟨1183134890597519217314539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6310052749853435825677541 1183134890597519217314539)
                ·
                  refine ⟨1774702335896278825971809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1183134890597519217314539 1774702335896278825971809)
                  ·
                    refine ⟨1331026751922209119478857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1774702335896278825971809 1331026751922209119478857)
                    ·
                      refine ⟨998270063941656839609143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1331026751922209119478857 998270063941656839609143)
                      ·
                        rfl

theorem cell23_1944124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_1944124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944124 prefixEnd_1944124 := by exact prefixLift 1944124
  have htrace : WordTrace (prefixWord ++ tailWord_1944124) baseStart_1944124 baseEnd_1944124 := by
    simpa [prefixWord, tailWord_1944124, baseEnd_1944124] using wordTrace_append hprefix tailTrace_1944124
  have hstable : (prefixWord ++ tailWord_1944124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944124).length < 2 ^ (prefixWord ++ tailWord_1944124).sum := by decide
  have hdescent : baseEnd_1944124 < baseStart_1944124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944140 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 2, 1, 3]
def baseStart_1944140 : Nat := 118140960795 + 1944140 * 2 ^ 59
def prefixEnd_1944140 : Nat := 4983230072969 + 3 ^ 40 * 1944140 * 2
def baseEnd_1944140 : Nat := 998278279632128777009069

theorem tailTrace_1944140 : CollatzResearch.WordTrace tailWord_1944140 prefixEnd_1944140 998278279632128777009069 := by
  unfold tailWord_1944140
  simp only [CollatzResearch.WordTrace]
  refine ⟨35454305588360143761318937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47272407451146858348425249 35454305588360143761318937)
  ·
    refine ⟨26590729191270107820989203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35454305588360143761318937 26590729191270107820989203)
    ·
      refine ⟨39886093786905161731483805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26590729191270107820989203 39886093786905161731483805)
      ·
        refine ⟨14957285170089435649306427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39886093786905161731483805 14957285170089435649306427)
        ·
          refine ⟨22435927755134153473959641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14957285170089435649306427 22435927755134153473959641)
          ·
            refine ⟨16826945816350615105469731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22435927755134153473959641 16826945816350615105469731)
            ·
              refine ⟨25240418724525922658204597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16826945816350615105469731 25240418724525922658204597)
              ·
                refine ⟨2366289255424305249206681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25240418724525922658204597 2366289255424305249206681)
                ·
                  refine ⟨1774716941568228936905011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2366289255424305249206681 1774716941568228936905011)
                  ·
                    refine ⟨2662075412352343405357517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1774716941568228936905011 2662075412352343405357517)
                    ·
                      refine ⟨998278279632128777009069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2662075412352343405357517 998278279632128777009069)
                      ·
                        rfl

theorem cell23_1944140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_1944140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944140 prefixEnd_1944140 := by exact prefixLift 1944140
  have htrace : WordTrace (prefixWord ++ tailWord_1944140) baseStart_1944140 baseEnd_1944140 := by
    simpa [prefixWord, tailWord_1944140, baseEnd_1944140] using wordTrace_append hprefix tailTrace_1944140
  have hstable : (prefixWord ++ tailWord_1944140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944140).length < 2 ^ (prefixWord ++ tailWord_1944140).sum := by decide
  have hdescent : baseEnd_1944140 < baseStart_1944140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944158 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_1944158 : Nat := 118140960795 + 1944158 * 2 ^ 59
def prefixEnd_1944158 : Nat := 4983230072969 + 3 ^ 40 * 1944158 * 2
def baseEnd_1944158 : Nat := 998287522283909706583987

theorem tailTrace_1944158 : CollatzResearch.WordTrace tailWord_1944158 prefixEnd_1944158 998287522283909706583987 := by
  unfold tailWord_1944158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863658461331884574599141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47272845127103384397862085 8863658461331884574599141)
  ·
    refine ⟨1661935961499728357737339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8863658461331884574599141 1661935961499728357737339)
    ·
      refine ⟨2492903942249592536606009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661935961499728357737339 2492903942249592536606009)
      ·
        refine ⟨1869677956687194402454507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2492903942249592536606009 1869677956687194402454507)
        ·
          refine ⟨2804516935030791603681761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1869677956687194402454507 2804516935030791603681761)
          ·
            refine ⟨2103387701273093702761321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2804516935030791603681761 2103387701273093702761321)
            ·
              refine ⟨1577540775954820277070991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2103387701273093702761321 1577540775954820277070991)
              ·
                refine ⟨2366311163932230415606487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577540775954820277070991 2366311163932230415606487)
                ·
                  refine ⟨3549466745898345623409731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366311163932230415606487 3549466745898345623409731)
                  ·
                    refine ⟨5324200118847518435114597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3549466745898345623409731 5324200118847518435114597)
                    ·
                      refine ⟨998287522283909706583987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5324200118847518435114597 998287522283909706583987)
                      ·
                        rfl

theorem cell23_1944158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_1944158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944158 prefixEnd_1944158 := by exact prefixLift 1944158
  have htrace : WordTrace (prefixWord ++ tailWord_1944158) baseStart_1944158 baseEnd_1944158 := by
    simpa [prefixWord, tailWord_1944158, baseEnd_1944158] using wordTrace_append hprefix tailTrace_1944158
  have hstable : (prefixWord ++ tailWord_1944158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944158).length < 2 ^ (prefixWord ++ tailWord_1944158).sum := by decide
  have hdescent : baseEnd_1944158 < baseStart_1944158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944173 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_1944173 : Nat := 118140960795 + 1944173 * 2 ^ 59
def prefixEnd_1944173 : Nat := 4983230072969 + 3 ^ 40 * 1944173 * 2
def baseEnd_1944173 : Nat := 332765074831242382632139

theorem tailTrace_1944173 : CollatzResearch.WordTrace tailWord_1944173 prefixEnd_1944173 332765074831242382632139 := by
  unfold tailWord_1944173
  simp only [CollatzResearch.WordTrace]
  refine ⟨70909814785600734158589173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47273209857067156105726115 70909814785600734158589173)
  ·
    refine ⟨6647795136150068827367735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70909814785600734158589173 6647795136150068827367735)
    ·
      refine ⟨9971692704225103241051603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6647795136150068827367735 9971692704225103241051603)
      ·
        refine ⟨14957539056337654861577405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9971692704225103241051603 14957539056337654861577405)
        ·
          refine ⟨5609077146126620573091527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14957539056337654861577405 5609077146126620573091527)
          ·
            refine ⟨8413615719189930859637291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5609077146126620573091527 8413615719189930859637291)
            ·
              refine ⟨12620423578784896289455937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8413615719189930859637291 12620423578784896289455937)
              ·
                refine ⟨9465317684088672217091953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12620423578784896289455937 9465317684088672217091953)
                ·
                  refine ⟨7098988263066504162818965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9465317684088672217091953 7098988263066504162818965)
                  ·
                    refine ⟨332765074831242382632139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7098988263066504162818965 332765074831242382632139)
                    ·
                      rfl

theorem cell23_1944173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_1944173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944173 prefixEnd_1944173 := by exact prefixLift 1944173
  have htrace : WordTrace (prefixWord ++ tailWord_1944173) baseStart_1944173 baseEnd_1944173 := by
    simpa [prefixWord, tailWord_1944173, baseEnd_1944173] using wordTrace_append hprefix tailTrace_1944173
  have hstable : (prefixWord ++ tailWord_1944173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944173).length < 2 ^ (prefixWord ++ tailWord_1944173).sum := by decide
  have hdescent : baseEnd_1944173 < baseStart_1944173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944174 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_1944174 : Nat := 118140960795 + 1944174 * 2 ^ 59
def prefixEnd_1944174 : Nat := 4983230072969 + 3 ^ 40 * 1944174 * 2
def baseEnd_1944174 : Nat := 998295737974381643983913

theorem tailTrace_1944174 : CollatzResearch.WordTrace tailWord_1944174 prefixEnd_1944174 998295737974381643983913 := by
  unfold tailWord_1944174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863731407324638916171947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47273234172398074219583717 8863731407324638916171947)
  ·
    refine ⟨13295597110986958374257921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8863731407324638916171947 13295597110986958374257921)
    ·
      refine ⟨9971697833240218780693441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13295597110986958374257921 9971697833240218780693441)
      ·
        refine ⟨7478773374930164085520081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9971697833240218780693441 7478773374930164085520081)
        ·
          refine ⟨5609080031197623064140061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7478773374930164085520081 5609080031197623064140061)
          ·
            refine ⟨2103405011699108649052523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5609080031197623064140061 2103405011699108649052523)
            ·
              refine ⟨3155107517548662973578785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103405011699108649052523 3155107517548662973578785)
              ·
                refine ⟨2366330638161497230184089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3155107517548662973578785 2366330638161497230184089)
                ·
                  refine ⟨1774747978621122922638067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2366330638161497230184089 1774747978621122922638067)
                  ·
                    refine ⟨2662121967931684383957101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1774747978621122922638067 2662121967931684383957101)
                    ·
                      refine ⟨998295737974381643983913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2662121967931684383957101 998295737974381643983913)
                      ·
                        rfl

theorem cell23_1944174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_1944174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944174 prefixEnd_1944174 := by exact prefixLift 1944174
  have htrace : WordTrace (prefixWord ++ tailWord_1944174) baseStart_1944174 baseEnd_1944174 := by
    simpa [prefixWord, tailWord_1944174, baseEnd_1944174] using wordTrace_append hprefix tailTrace_1944174
  have hstable : (prefixWord ++ tailWord_1944174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944174).length < 2 ^ (prefixWord ++ tailWord_1944174).sum := by decide
  have hdescent : baseEnd_1944174 < baseStart_1944174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944193 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1944193 : Nat := 118140960795 + 1944193 * 2 ^ 59
def prefixEnd_1944193 : Nat := 4983230072969 + 3 ^ 40 * 1944193 * 2
def baseEnd_1944193 : Nat := 998305494106817069646325

theorem tailTrace_1944193 : CollatzResearch.WordTrace tailWord_1944193 prefixEnd_1944193 998305494106817069646325 := by
  unfold tailWord_1944193
  simp only [CollatzResearch.WordTrace]
  refine ⟨70910544245528277574317233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47273696163685518382878155 70910544245528277574317233)
  ·
    refine ⟨53182908184146208180737925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70910544245528277574317233 53182908184146208180737925)
    ·
      refine ⟨9971795284527414033888361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53182908184146208180737925 9971795284527414033888361)
      ·
        refine ⟨7478846463395560525416271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9971795284527414033888361 7478846463395560525416271)
        ·
          refine ⟨11218269695093340788124407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7478846463395560525416271 11218269695093340788124407)
          ·
            refine ⟨16827404542640011182186611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11218269695093340788124407 16827404542640011182186611)
            ·
              refine ⟨25241106813960016773279917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16827404542640011182186611 25241106813960016773279917)
              ·
                refine ⟨9465415055235006289979969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25241106813960016773279917 9465415055235006289979969)
                ·
                  refine ⟨7099061291426254717484977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9465415055235006289979969 7099061291426254717484977)
                  ·
                    refine ⟨5324295968569691038113733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7099061291426254717484977 5324295968569691038113733)
                    ·
                      refine ⟨998305494106817069646325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5324295968569691038113733 998305494106817069646325)
                      ·
                        rfl

theorem cell23_1944193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1944193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944193 prefixEnd_1944193 := by exact prefixLift 1944193
  have htrace : WordTrace (prefixWord ++ tailWord_1944193) baseStart_1944193 baseEnd_1944193 := by
    simpa [prefixWord, tailWord_1944193, baseEnd_1944193] using wordTrace_append hprefix tailTrace_1944193
  have hstable : (prefixWord ++ tailWord_1944193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944193).length < 2 ^ (prefixWord ++ tailWord_1944193).sum := by decide
  have hdescent : baseEnd_1944193 < baseStart_1944193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944197 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 1, 4, 2]
def baseStart_1944197 : Nat := 118140960795 + 1944197 * 2 ^ 59
def prefixEnd_1944197 : Nat := 4983230072969 + 3 ^ 40 * 1944197 * 2
def baseEnd_1944197 : Nat := 998307548029435053996307

theorem tailTrace_1944197 : CollatzResearch.WordTrace tailWord_1944197 prefixEnd_1944197 998307548029435053996307 := by
  unfold tailWord_1944197
  simp only [CollatzResearch.WordTrace]
  refine ⟨70910690137513786257462845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47273793425009190838308563 70910690137513786257462845)
  ·
    refine ⟨26591508801567669846548567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70910690137513786257462845 26591508801567669846548567)
    ·
      refine ⟨39887263202351504769822851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26591508801567669846548567 39887263202351504769822851)
      ·
        refine ⟨59830894803527257154734277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39887263202351504769822851 59830894803527257154734277)
        ·
          refine ⟨11218292775661360716512677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59830894803527257154734277 11218292775661360716512677)
          ·
            refine ⟨2103429895436505134346127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11218292775661360716512677 2103429895436505134346127)
            ·
              refine ⟨3155144843154757701519191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103429895436505134346127 3155144843154757701519191)
              ·
                refine ⟨4732717264732136552278787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155144843154757701519191 4732717264732136552278787)
                ·
                  refine ⟨7099075897098204828418181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732717264732136552278787 7099075897098204828418181)
                  ·
                    refine ⟨1331076730705913405328409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7099075897098204828418181 1331076730705913405328409)
                    ·
                      refine ⟨998307548029435053996307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1331076730705913405328409 998307548029435053996307)
                      ·
                        rfl

theorem cell23_1944197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 4, 2].length) (baseStart_1944197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944197 prefixEnd_1944197 := by exact prefixLift 1944197
  have htrace : WordTrace (prefixWord ++ tailWord_1944197) baseStart_1944197 baseEnd_1944197 := by
    simpa [prefixWord, tailWord_1944197, baseEnd_1944197] using wordTrace_append hprefix tailTrace_1944197
  have hstable : (prefixWord ++ tailWord_1944197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944197).length < 2 ^ (prefixWord ++ tailWord_1944197).sum := by decide
  have hdescent : baseEnd_1944197 < baseStart_1944197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944236 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_1944236 : Nat := 118140960795 + 1944236 * 2 ^ 59
def prefixEnd_1944236 : Nat := 4983230072969 + 3 ^ 40 * 1944236 * 2
def baseEnd_1944236 : Nat := 998327573774960401408627

theorem tailTrace_1944236 : CollatzResearch.WordTrace tailWord_1944236 prefixEnd_1944236 998327573774960401408627 := by
  unfold tailWord_1944236
  simp only [CollatzResearch.WordTrace]
  refine ⟨35456056292186247959066281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47274741722914997278755041 35456056292186247959066281)
  ·
    refine ⟨26592042219139685969299711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35456056292186247959066281 26592042219139685969299711)
    ·
      refine ⟨39888063328709528953949567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26592042219139685969299711 39888063328709528953949567)
      ·
        refine ⟨59832094993064293430924351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39888063328709528953949567 59832094993064293430924351)
        ·
          refine ⟨89748142489596440146386527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59832094993064293430924351 89748142489596440146386527)
          ·
            refine ⟨134622213734394660219579791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89748142489596440146386527 134622213734394660219579791)
            ·
              refine ⟨201933320601591990329369687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134622213734394660219579791 201933320601591990329369687)
              ·
                refine ⟨302899980902387985494054531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201933320601591990329369687 302899980902387985494054531)
                ·
                  refine ⟨454349971353581978241081797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302899980902387985494054531 454349971353581978241081797)
                  ·
                    refine ⟨85190619628796620920202837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454349971353581978241081797 85190619628796620920202837)
                    ·
                      refine ⟨998327573774960401408627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 85190619628796620920202837 998327573774960401408627)
                      ·
                        rfl

theorem cell23_1944236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_1944236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944236 prefixEnd_1944236 := by exact prefixLift 1944236
  have htrace : WordTrace (prefixWord ++ tailWord_1944236) baseStart_1944236 baseEnd_1944236 := by
    simpa [prefixWord, tailWord_1944236, baseEnd_1944236] using wordTrace_append hprefix tailTrace_1944236
  have hstable : (prefixWord ++ tailWord_1944236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944236).length < 2 ^ (prefixWord ++ tailWord_1944236).sum := by decide
  have hdescent : baseEnd_1944236 < baseStart_1944236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944243 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 5]
def baseStart_1944243 : Nat := 118140960795 + 1944243 * 2 ^ 59
def prefixEnd_1944243 : Nat := 4983230072969 + 3 ^ 40 * 1944243 * 2
def baseEnd_1944243 : Nat := 998331168139541874021095

theorem tailTrace_1944243 : CollatzResearch.WordTrace tailWord_1944243 prefixEnd_1944243 998331168139541874021095 := by
  unfold tailWord_1944243
  simp only [CollatzResearch.WordTrace]
  refine ⟨70912367895347136113637383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47274911930231424075758255 70912367895347136113637383)
  ·
    refine ⟨106368551843020704170456075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70912367895347136113637383 106368551843020704170456075)
    ·
      refine ⟨159552827764531056255684113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106368551843020704170456075 159552827764531056255684113)
      ·
        refine ⟨119664620823398292191763085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159552827764531056255684113 119664620823398292191763085)
        ·
          refine ⟨44874232808774359571911157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119664620823398292191763085 44874232808774359571911157)
          ·
            refine ⟨4206959325822596209866671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44874232808774359571911157 4206959325822596209866671)
            ·
              refine ⟨6310438988733894314800007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206959325822596209866671 6310438988733894314800007)
              ·
                refine ⟨9465658483100841472200011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6310438988733894314800007 9465658483100841472200011)
                ·
                  refine ⟨14198487724651262208300017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9465658483100841472200011 14198487724651262208300017)
                  ·
                    refine ⟨10648865793488446656225013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14198487724651262208300017 10648865793488446656225013)
                    ·
                      refine ⟨998331168139541874021095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10648865793488446656225013 998331168139541874021095)
                      ·
                        rfl

theorem cell23_1944243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_1944243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944243 prefixEnd_1944243 := by exact prefixLift 1944243
  have htrace : WordTrace (prefixWord ++ tailWord_1944243) baseStart_1944243 baseEnd_1944243 := by
    simpa [prefixWord, tailWord_1944243, baseEnd_1944243] using wordTrace_append hprefix tailTrace_1944243
  have hstable : (prefixWord ++ tailWord_1944243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944243).length < 2 ^ (prefixWord ++ tailWord_1944243).sum := by decide
  have hdescent : baseEnd_1944243 < baseStart_1944243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944270 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_1944270 : Nat := 118140960795 + 1944270 * 2 ^ 59
def prefixEnd_1944270 : Nat := 4983230072969 + 3 ^ 40 * 1944270 * 2
def baseEnd_1944270 : Nat := 998345032117213268383471

theorem tailTrace_1944270 : CollatzResearch.WordTrace tailWord_1944270 prefixEnd_1944270 998345032117213268383471 := by
  unfold tailWord_1944270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8864169083281164965608783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47275568444166213149913509 8864169083281164965608783)
  ·
    refine ⟨13296253624921747448413175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8864169083281164965608783 13296253624921747448413175)
    ·
      refine ⟨19944380437382621172619763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13296253624921747448413175 19944380437382621172619763)
      ·
        refine ⟨29916570656073931758929645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19944380437382621172619763 29916570656073931758929645)
        ·
          refine ⟨11218713996027724409598617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29916570656073931758929645 11218713996027724409598617)
          ·
            refine ⟨8414035497020793307198963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11218713996027724409598617 8414035497020793307198963)
            ·
              refine ⟨12621053245531189960798445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8414035497020793307198963 12621053245531189960798445)
              ·
                refine ⟨4732894967074196235299417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12621053245531189960798445 4732894967074196235299417)
                ·
                  refine ⟨3549671225305647176474563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4732894967074196235299417 3549671225305647176474563)
                  ·
                    refine ⟨5324506837958470764711845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3549671225305647176474563 5324506837958470764711845)
                    ·
                      refine ⟨998345032117213268383471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5324506837958470764711845 998345032117213268383471)
                      ·
                        rfl

theorem cell23_1944270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_1944270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944270 prefixEnd_1944270 := by exact prefixLift 1944270
  have htrace : WordTrace (prefixWord ++ tailWord_1944270) baseStart_1944270 baseEnd_1944270 := by
    simpa [prefixWord, tailWord_1944270, baseEnd_1944270] using wordTrace_append hprefix tailTrace_1944270
  have hstable : (prefixWord ++ tailWord_1944270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944270).length < 2 ^ (prefixWord ++ tailWord_1944270).sum := by decide
  have hdescent : baseEnd_1944270 < baseStart_1944270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944310 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_1944310 : Nat := 118140960795 + 1944310 * 2 ^ 59
def prefixEnd_1944310 : Nat := 4983230072969 + 3 ^ 40 * 1944310 * 2
def baseEnd_1944310 : Nat := 110929507927043679098143

theorem tailTrace_1944310 : CollatzResearch.WordTrace tailWord_1944310 prefixEnd_1944310 110929507927043679098143 := by
  unfold tailWord_1944310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432175724131525409770399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47276541057402937704217589 4432175724131525409770399)
  ·
    refine ⟨6648263586197288114655599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4432175724131525409770399 6648263586197288114655599)
    ·
      refine ⟨9972395379295932171983399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6648263586197288114655599 9972395379295932171983399)
      ·
        refine ⟨14958593068943898257975099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9972395379295932171983399 14958593068943898257975099)
        ·
          refine ⟨22437889603415847386962649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14958593068943898257975099 22437889603415847386962649)
          ·
            refine ⟨16828417202561885540221987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22437889603415847386962649 16828417202561885540221987)
            ·
              refine ⟨25242625803842828310332981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16828417202561885540221987 25242625803842828310332981)
              ·
                refine ⟨2366496169110265154093717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25242625803842828310332981 2366496169110265154093717)
                ·
                  refine ⟨110929507927043679098143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2366496169110265154093717 110929507927043679098143)
                  ·
                    rfl

theorem cell23_1944310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_1944310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944310 prefixEnd_1944310 := by exact prefixLift 1944310
  have htrace : WordTrace (prefixWord ++ tailWord_1944310) baseStart_1944310 baseEnd_1944310 := by
    simpa [prefixWord, tailWord_1944310, baseEnd_1944310] using wordTrace_append hprefix tailTrace_1944310
  have hstable : (prefixWord ++ tailWord_1944310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944310).length < 2 ^ (prefixWord ++ tailWord_1944310).sum := by decide
  have hdescent : baseEnd_1944310 < baseStart_1944310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944354 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_1944354 : Nat := 118140960795 + 1944354 * 2 ^ 59
def prefixEnd_1944354 : Nat := 4983230072969 + 3 ^ 40 * 1944354 * 2
def baseEnd_1944354 : Nat := 998388164492190939733085

theorem tailTrace_1944354 : CollatzResearch.WordTrace tailWord_1944354 prefixEnd_1944354 998388164492190939733085 := by
  unfold tailWord_1944354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17729104099486250517732029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47277610931963334713952077 17729104099486250517732029)
  ·
    refine ⟨6648414037307343944149511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17729104099486250517732029 6648414037307343944149511)
    ·
      refine ⟨9972621055961015916224267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6648414037307343944149511 9972621055961015916224267)
      ·
        refine ⟨14958931583941523874336401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9972621055961015916224267 14958931583941523874336401)
        ·
          refine ⟨11219198687956142905752301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14958931583941523874336401 11219198687956142905752301)
          ·
            refine ⟨4207199507983553589657113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11219198687956142905752301 4207199507983553589657113)
            ·
              refine ⟨3155399630987665192242835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4207199507983553589657113 3155399630987665192242835)
              ·
                refine ⟨4733099446481497788364253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155399630987665192242835 4733099446481497788364253)
                ·
                  refine ⟨1774912292430561670636595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4733099446481497788364253 1774912292430561670636595)
                  ·
                    refine ⟨2662368438645842505954893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1774912292430561670636595 2662368438645842505954893)
                    ·
                      refine ⟨998388164492190939733085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2662368438645842505954893 998388164492190939733085)
                      ·
                        rfl

theorem cell23_1944354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_1944354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944354 prefixEnd_1944354 := by exact prefixLift 1944354
  have htrace : WordTrace (prefixWord ++ tailWord_1944354) baseStart_1944354 baseEnd_1944354 := by
    simpa [prefixWord, tailWord_1944354, baseEnd_1944354] using wordTrace_append hprefix tailTrace_1944354
  have hstable : (prefixWord ++ tailWord_1944354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944354).length < 2 ^ (prefixWord ++ tailWord_1944354).sum := by decide
  have hdescent : baseEnd_1944354 < baseStart_1944354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944363 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 5]
def baseStart_1944363 : Nat := 118140960795 + 1944363 * 2 ^ 59
def prefixEnd_1944363 : Nat := 4983230072969 + 3 ^ 40 * 1944363 * 2
def baseEnd_1944363 : Nat := 998392785818081404520543

theorem tailTrace_1944363 : CollatzResearch.WordTrace tailWord_1944363 prefixEnd_1944363 998392785818081404520543 := by
  unfold tailWord_1944363
  simp only [CollatzResearch.WordTrace]
  refine ⟨70916744654912396608005743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47277829769941597738670495 70916744654912396608005743)
  ·
    refine ⟨106375116982368594912008615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70916744654912396608005743 106375116982368594912008615)
    ·
      refine ⟨159562675473552892368012923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106375116982368594912008615 159562675473552892368012923)
      ·
        refine ⟨239344013210329338552019385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159562675473552892368012923 239344013210329338552019385)
        ·
          refine ⟨179508009907747003914014539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239344013210329338552019385 179508009907747003914014539)
          ·
            refine ⟨269262014861620505871021809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179508009907747003914014539 269262014861620505871021809)
            ·
              refine ⟨201946511146215379403266357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269262014861620505871021809 201946511146215379403266357)
              ·
                refine ⟨18932485419957691819056221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201946511146215379403266357 18932485419957691819056221)
                ·
                  refine ⟨7099682032484134432146083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18932485419957691819056221 7099682032484134432146083)
                  ·
                    refine ⟨10649523048726201648219125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7099682032484134432146083 10649523048726201648219125)
                    ·
                      refine ⟨998392785818081404520543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10649523048726201648219125 998392785818081404520543)
                      ·
                        rfl

theorem cell23_1944363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 5].length) (baseStart_1944363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944363 prefixEnd_1944363 := by exact prefixLift 1944363
  have htrace : WordTrace (prefixWord ++ tailWord_1944363) baseStart_1944363 baseEnd_1944363 := by
    simpa [prefixWord, tailWord_1944363, baseEnd_1944363] using wordTrace_append hprefix tailTrace_1944363
  have hstable : (prefixWord ++ tailWord_1944363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944363).length < 2 ^ (prefixWord ++ tailWord_1944363).sum := by decide
  have hdescent : baseEnd_1944363 < baseStart_1944363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944480 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1944480 : Nat := 118140960795 + 1944480 * 2 ^ 59
def prefixEnd_1944480 : Nat := 4983230072969 + 3 ^ 40 * 1944480 * 2
def baseEnd_1944480 : Nat := 998452863054657446757505

theorem tailTrace_1944480 : CollatzResearch.WordTrace tailWord_1944480 prefixEnd_1944480 998452863054657446757505 := by
  unfold tailWord_1944480
  simp only [CollatzResearch.WordTrace]
  refine ⟨35460505997744262795007447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47280674663659017060009929 35460505997744262795007447)
  ·
    refine ⟨53190758996616394192511171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35460505997744262795007447 53190758996616394192511171)
    ·
      refine ⟨79786138494924591288766757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53190758996616394192511171 79786138494924591288766757)
      ·
        refine ⟨14959900967798360866643767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79786138494924591288766757 14959900967798360866643767)
        ·
          refine ⟨22439851451697541299965651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14959900967798360866643767 22439851451697541299965651)
          ·
            refine ⟨33659777177546311949948477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22439851451697541299965651 33659777177546311949948477)
            ·
              refine ⟨12622416441579866981230679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33659777177546311949948477 12622416441579866981230679)
              ·
                refine ⟨18933624662369800471846019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12622416441579866981230679 18933624662369800471846019)
                ·
                  refine ⟨28400436993554700707769029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18933624662369800471846019 28400436993554700707769029)
                  ·
                    refine ⟨5325081936291506382706693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28400436993554700707769029 5325081936291506382706693)
                    ·
                      refine ⟨998452863054657446757505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5325081936291506382706693 998452863054657446757505)
                      ·
                        rfl

theorem cell23_1944480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1944480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944480 prefixEnd_1944480 := by exact prefixLift 1944480
  have htrace : WordTrace (prefixWord ++ tailWord_1944480) baseStart_1944480 baseEnd_1944480 := by
    simpa [prefixWord, tailWord_1944480, baseEnd_1944480] using wordTrace_append hprefix tailTrace_1944480
  have hstable : (prefixWord ++ tailWord_1944480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944480).length < 2 ^ (prefixWord ++ tailWord_1944480).sum := by decide
  have hdescent : baseEnd_1944480 < baseStart_1944480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944484 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 1, 4, 2]
def baseStart_1944484 : Nat := 118140960795 + 1944484 * 2 ^ 59
def prefixEnd_1944484 : Nat := 4983230072969 + 3 ^ 40 * 1944484 * 2
def baseEnd_1944484 : Nat := 998454916977275431107487

theorem tailTrace_1944484 : CollatzResearch.WordTrace tailWord_1944484 prefixEnd_1944484 998454916977275431107487 := by
  unfold tailWord_1944484
  simp only [CollatzResearch.WordTrace]
  refine ⟨35460578943737017136580253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47280771924982689515440337 35460578943737017136580253)
  ·
    refine ⟨13297717103901381426217595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35460578943737017136580253 13297717103901381426217595)
    ·
      refine ⟨19946575655852072139326393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13297717103901381426217595 19946575655852072139326393)
      ·
        refine ⟨14959931741889054104494795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19946575655852072139326393 14959931741889054104494795)
        ·
          refine ⟨22439897612833581156742193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14959931741889054104494795 22439897612833581156742193)
          ·
            refine ⟨16829923209625185867556645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22439897612833581156742193 16829923209625185867556645)
            ·
              refine ⟨3155610601804722350166871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16829923209625185867556645 3155610601804722350166871)
              ·
                refine ⟨4733415902707083525250307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155610601804722350166871 4733415902707083525250307)
                ·
                  refine ⟨7100123854060625287875461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733415902707083525250307 7100123854060625287875461)
                  ·
                    refine ⟨1331273222636367241476649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7100123854060625287875461 1331273222636367241476649)
                    ·
                      refine ⟨998454916977275431107487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1331273222636367241476649 998454916977275431107487)
                      ·
                        rfl

theorem cell23_1944484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_1944484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944484 prefixEnd_1944484 := by exact prefixLift 1944484
  have htrace : WordTrace (prefixWord ++ tailWord_1944484) baseStart_1944484 baseEnd_1944484 := by
    simpa [prefixWord, tailWord_1944484, baseEnd_1944484] using wordTrace_append hprefix tailTrace_1944484
  have hstable : (prefixWord ++ tailWord_1944484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944484).length < 2 ^ (prefixWord ++ tailWord_1944484).sum := by decide
  have hdescent : baseEnd_1944484 < baseStart_1944484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944558 : List Nat := [4, 1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_1944558 : Nat := 118140960795 + 1944558 * 2 ^ 59
def prefixEnd_1944558 : Nat := 4983230072969 + 3 ^ 40 * 1944558 * 2
def baseEnd_1944558 : Nat := 110943657171745349064683

theorem tailTrace_1944558 : CollatzResearch.WordTrace tailWord_1944558 prefixEnd_1944558 110943657171745349064683 := by
  unfold tailWord_1944558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865482111150743113919291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47282571259470629940902885 8865482111150743113919291)
  ·
    refine ⟨13298223166726114670878937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8865482111150743113919291 13298223166726114670878937)
    ·
      refine ⟨9973667375044586003159203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13298223166726114670878937 9973667375044586003159203)
      ·
        refine ⟨14960501062566879004738805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9973667375044586003159203 14960501062566879004738805)
        ·
          refine ⟨1402546974615644906694263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14960501062566879004738805 1402546974615644906694263)
          ·
            refine ⟨2103820461923467360041395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402546974615644906694263 2103820461923467360041395)
            ·
              refine ⟨3155730692885201040062093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103820461923467360041395 3155730692885201040062093)
              ·
                refine ⟨1183399009831950390023285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3155730692885201040062093 1183399009831950390023285)
                ·
                  refine ⟨110943657171745349064683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1183399009831950390023285 110943657171745349064683)
                  ·
                    rfl

theorem cell23_1944558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_1944558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944558 prefixEnd_1944558 := by exact prefixLift 1944558
  have htrace : WordTrace (prefixWord ++ tailWord_1944558) baseStart_1944558 baseEnd_1944558 := by
    simpa [prefixWord, tailWord_1944558, baseEnd_1944558] using wordTrace_append hprefix tailTrace_1944558
  have hstable : (prefixWord ++ tailWord_1944558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944558).length < 2 ^ (prefixWord ++ tailWord_1944558).sum := by decide
  have hdescent : baseEnd_1944558 < baseStart_1944558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944560 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_1944560 : Nat := 118140960795 + 1944560 * 2 ^ 59
def prefixEnd_1944560 : Nat := 4983230072969 + 3 ^ 40 * 1944560 * 2
def baseEnd_1944560 : Nat := 998493941507017133757137

theorem tailTrace_1944560 : CollatzResearch.WordTrace tailWord_1944560 prefixEnd_1944560 998493941507017133757137 := by
  unfold tailWord_1944560
  simp only [CollatzResearch.WordTrace]
  refine ⟨35461964917599349626463567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47282619890132466168618089 35461964917599349626463567)
  ·
    refine ⟨53192947376399024439695351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35461964917599349626463567 53192947376399024439695351)
    ·
      refine ⟨79789421064598536659543027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53192947376399024439695351 79789421064598536659543027)
      ·
        refine ⟨119684131596897804989314541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79789421064598536659543027 119684131596897804989314541)
        ·
          refine ⟨44881549348836676870992953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119684131596897804989314541 44881549348836676870992953)
          ·
            refine ⟨33661162011627507653244715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44881549348836676870992953 33661162011627507653244715)
            ·
              refine ⟨50491743017441261479867073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33661162011627507653244715 50491743017441261479867073)
              ·
                refine ⟨37868807263080946109900305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50491743017441261479867073 37868807263080946109900305)
                ·
                  refine ⟨28401605447310709582425229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37868807263080946109900305 28401605447310709582425229)
                  ·
                    refine ⟨10650602042741516093409461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28401605447310709582425229 10650602042741516093409461)
                    ·
                      refine ⟨998493941507017133757137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10650602042741516093409461 998493941507017133757137)
                      ·
                        rfl

theorem cell23_1944560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_1944560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944560 prefixEnd_1944560 := by exact prefixLift 1944560
  have htrace : WordTrace (prefixWord ++ tailWord_1944560) baseStart_1944560 baseEnd_1944560 := by
    simpa [prefixWord, tailWord_1944560, baseEnd_1944560] using wordTrace_append hprefix tailTrace_1944560
  have hstable : (prefixWord ++ tailWord_1944560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944560).length < 2 ^ (prefixWord ++ tailWord_1944560).sum := by decide
  have hdescent : baseEnd_1944560 < baseStart_1944560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944570 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_1944570 : Nat := 118140960795 + 1944570 * 2 ^ 59
def prefixEnd_1944570 : Nat := 4983230072969 + 3 ^ 40 * 1944570 * 2
def baseEnd_1944570 : Nat := 998499076313562094632091

theorem tailTrace_1944570 : CollatzResearch.WordTrace tailWord_1944570 prefixEnd_1944570 998499076313562094632091 := by
  unfold tailWord_1944570
  simp only [CollatzResearch.WordTrace]
  refine ⟨17731073641290617740197791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47282863043441647307194109 17731073641290617740197791)
  ·
    refine ⟨26596610461935926610296687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17731073641290617740197791 26596610461935926610296687)
    ·
      refine ⟨39894915692903889915445031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26596610461935926610296687 39894915692903889915445031)
      ·
        refine ⟨59842373539355834873167547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39894915692903889915445031 59842373539355834873167547)
        ·
          refine ⟨89763560309033752309751321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59842373539355834873167547 89763560309033752309751321)
          ·
            refine ⟨67322670231775314232313491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89763560309033752309751321 67322670231775314232313491)
            ·
              refine ⟨100984005347662971348470237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67322670231775314232313491 100984005347662971348470237)
              ·
                refine ⟨37869002005373614255676339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100984005347662971348470237 37869002005373614255676339)
                ·
                  refine ⟨56803503008060421383514509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37869002005373614255676339 56803503008060421383514509)
                  ·
                    refine ⟨21301313628022658018817941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56803503008060421383514509 21301313628022658018817941)
                    ·
                      refine ⟨998499076313562094632091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21301313628022658018817941 998499076313562094632091)
                      ·
                        rfl

theorem cell23_1944570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_1944570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944570 prefixEnd_1944570 := by exact prefixLift 1944570
  have htrace : WordTrace (prefixWord ++ tailWord_1944570) baseStart_1944570 baseEnd_1944570 := by
    simpa [prefixWord, tailWord_1944570, baseEnd_1944570] using wordTrace_append hprefix tailTrace_1944570
  have hstable : (prefixWord ++ tailWord_1944570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944570).length < 2 ^ (prefixWord ++ tailWord_1944570).sum := by decide
  have hdescent : baseEnd_1944570 < baseStart_1944570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944584 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 3, 4]
def baseStart_1944584 : Nat := 118140960795 + 1944584 * 2 ^ 59
def prefixEnd_1944584 : Nat := 4983230072969 + 3 ^ 40 * 1944584 * 2
def baseEnd_1944584 : Nat := 332835421680908346619009

theorem tailTrace_1944584 : CollatzResearch.WordTrace tailWord_1944584 prefixEnd_1944584 332835421680908346619009 := by
  unfold tailWord_1944584
  simp only [CollatzResearch.WordTrace]
  refine ⟨35462402593555875675900403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47283203458074500901200537 35462402593555875675900403)
  ·
    refine ⟨53193603890333813513850605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35462402593555875675900403 53193603890333813513850605)
    ·
      refine ⟨19947601458875180067693977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53193603890333813513850605 19947601458875180067693977)
      ·
        refine ⟨14960701094156385050770483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19947601458875180067693977 14960701094156385050770483)
        ·
          refine ⟨22441051641234577576155725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14960701094156385050770483 22441051641234577576155725)
          ·
            refine ⟨8415394365462966591058397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22441051641234577576155725 8415394365462966591058397)
            ·
              refine ⟨3155772887048612471646899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8415394365462966591058397 3155772887048612471646899)
              ·
                refine ⟨4733659330572918707470349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155772887048612471646899 4733659330572918707470349)
                ·
                  refine ⟨1775122248964844515301381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4733659330572918707470349 1775122248964844515301381)
                  ·
                    refine ⟨332835421680908346619009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1775122248964844515301381 332835421680908346619009)
                    ·
                      rfl

theorem cell23_1944584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_1944584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944584 prefixEnd_1944584 := by exact prefixLift 1944584
  have htrace : WordTrace (prefixWord ++ tailWord_1944584) baseStart_1944584 baseEnd_1944584 := by
    simpa [prefixWord, tailWord_1944584, baseEnd_1944584] using wordTrace_append hprefix tailTrace_1944584
  have hstable : (prefixWord ++ tailWord_1944584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944584).length < 2 ^ (prefixWord ++ tailWord_1944584).sum := by decide
  have hdescent : baseEnd_1944584 < baseStart_1944584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1944657 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 1, 6]
def baseStart_1944657 : Nat := 118140960795 + 1944657 * 2 ^ 59
def prefixEnd_1944657 : Nat := 4983230072969 + 3 ^ 40 * 1944657 * 2
def baseEnd_1944657 : Nat := 332847916376834418081397

theorem tailTrace_1944657 : CollatzResearch.WordTrace tailWord_1944657 prefixEnd_1944657 332847916376834418081397 := by
  unfold tailWord_1944657
  simp only [CollatzResearch.WordTrace]
  refine ⟨70927467715847284819208225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47284978477231523212805483 70927467715847284819208225)
  ·
    refine ⟨53195600786885463614406169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70927467715847284819208225 53195600786885463614406169)
    ·
      refine ⟨39896700590164097710804627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53195600786885463614406169 39896700590164097710804627)
      ·
        refine ⟨59845050885246146566206941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39896700590164097710804627 59845050885246146566206941)
        ·
          refine ⟨22441894081967304962327603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59845050885246146566206941 22441894081967304962327603)
          ·
            refine ⟨33662841122950957443491405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22441894081967304962327603 33662841122950957443491405)
            ·
              refine ⟨12623565421106609041309277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33662841122950957443491405 12623565421106609041309277)
              ·
                refine ⟨4733837032914978390490979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12623565421106609041309277 4733837032914978390490979)
                ·
                  refine ⟨7100755549372467585736469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733837032914978390490979 7100755549372467585736469)
                  ·
                    refine ⟨332847916376834418081397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7100755549372467585736469 332847916376834418081397)
                    ·
                      rfl

theorem cell23_1944657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_1944657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1944657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1944657 prefixEnd_1944657 := by exact prefixLift 1944657
  have htrace : WordTrace (prefixWord ++ tailWord_1944657) baseStart_1944657 baseEnd_1944657 := by
    simpa [prefixWord, tailWord_1944657, baseEnd_1944657] using wordTrace_append hprefix tailTrace_1944657
  have hstable : (prefixWord ++ tailWord_1944657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1944657).length < 2 ^ (prefixWord ++ tailWord_1944657).sum := by decide
  have hdescent : baseEnd_1944657 < baseStart_1944657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1944657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
