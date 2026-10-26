import V185TrunkScan23Chunk0193

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1148678 : List Nat := [6, 2, 2, 1, 2, 1, 2, 7]
def baseStart_1148678 : Nat := 118140960795 + 1148678 * 2 ^ 59
def prefixEnd_1148678 : Nat := 4983230072969 + 3 ^ 40 * 1148678 * 2
def baseEnd_1148678 : Nat := 21845330786865260212679

theorem tailTrace_1148678 : CollatzResearch.WordTrace tailWord_1148678 prefixEnd_1148678 21845330786865260212679 := by
  unfold tailWord_1148678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1309241516641976857154209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27930485688362172952623125 1309241516641976857154209)
  ·
    refine ⟨981931137481482642865657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1309241516641976857154209 981931137481482642865657)
    ·
      refine ⟨736448353111111982149243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 981931137481482642865657 736448353111111982149243)
      ·
        refine ⟨1104672529666667973223865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736448353111111982149243 1104672529666667973223865)
        ·
          refine ⟨828504397250000979917899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1104672529666667973223865 828504397250000979917899)
          ·
            refine ⟨1242756595875001469876849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828504397250000979917899 1242756595875001469876849)
            ·
              refine ⟨932067446906251102407637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1242756595875001469876849 932067446906251102407637)
              ·
                refine ⟨21845330786865260212679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 932067446906251102407637 21845330786865260212679)
                ·
                  rfl

theorem cell23_1148678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_1148678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148678 prefixEnd_1148678 := by exact prefixLift 1148678
  have htrace : WordTrace (prefixWord ++ tailWord_1148678) baseStart_1148678 baseEnd_1148678 := by
    simpa [prefixWord, tailWord_1148678, baseEnd_1148678] using wordTrace_append hprefix tailTrace_1148678
  have hstable : (prefixWord ++ tailWord_1148678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148678).length < 2 ^ (prefixWord ++ tailWord_1148678).sum := by decide
  have hdescent : baseEnd_1148678 < baseStart_1148678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148696 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 1, 7]
def baseStart_1148696 : Nat := 118140960795 + 1148696 * 2 ^ 59
def prefixEnd_1148696 : Nat := 4983230072969 + 3 ^ 40 * 1148696 * 2
def baseEnd_1148696 : Nat := 196611057965714318439083

theorem tailTrace_1148696 : CollatzResearch.WordTrace tailWord_1148696 prefixEnd_1148696 196611057965714318439083 := by
  unfold tailWord_1148696
  simp only [CollatzResearch.WordTrace]
  refine ⟨20948192523239024251544971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27930923364318699002059961 20948192523239024251544971)
  ·
    refine ⟨31422288784858536377317457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20948192523239024251544971 31422288784858536377317457)
    ·
      refine ⟨23566716588643902282988093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31422288784858536377317457 23566716588643902282988093)
      ·
        refine ⟨8837518720741463356120535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23566716588643902282988093 8837518720741463356120535)
        ·
          refine ⟨13256278081112195034180803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8837518720741463356120535 13256278081112195034180803)
          ·
            refine ⟨19884417121668292551271205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13256278081112195034180803 19884417121668292551271205)
            ·
              refine ⟨3728328210312804853363351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19884417121668292551271205 3728328210312804853363351)
              ·
                refine ⟨5592492315469207280045027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3728328210312804853363351 5592492315469207280045027)
                ·
                  refine ⟨8388738473203810920067541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5592492315469207280045027 8388738473203810920067541)
                  ·
                    refine ⟨196611057965714318439083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8388738473203810920067541 196611057965714318439083)
                    ·
                      rfl

theorem cell23_1148696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_1148696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148696 prefixEnd_1148696 := by exact prefixLift 1148696
  have htrace : WordTrace (prefixWord ++ tailWord_1148696) baseStart_1148696 baseEnd_1148696 := by
    simpa [prefixWord, tailWord_1148696, baseEnd_1148696] using wordTrace_append hprefix tailTrace_1148696
  have hstable : (prefixWord ++ tailWord_1148696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148696).length < 2 ^ (prefixWord ++ tailWord_1148696).sum := by decide
  have hdescent : baseEnd_1148696 < baseStart_1148696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148723 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 5]
def baseStart_1148723 : Nat := 118140960795 + 1148723 * 2 ^ 59
def prefixEnd_1148723 : Nat := 4983230072969 + 3 ^ 40 * 1148723 * 2
def baseEnd_1148723 : Nat := 589847037874814349679625

theorem tailTrace_1148723 : CollatzResearch.WordTrace tailWord_1148723 prefixEnd_1148723 589847037874814349679625 := by
  unfold tailWord_1148723
  simp only [CollatzResearch.WordTrace]
  refine ⟨41897369817380232114322823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27931579878253488076215215 41897369817380232114322823)
  ·
    refine ⟨62846054726070348171484235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41897369817380232114322823 62846054726070348171484235)
    ·
      refine ⟨94269082089105522257226353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62846054726070348171484235 94269082089105522257226353)
      ·
        refine ⟨70701811566829141692919765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94269082089105522257226353 70701811566829141692919765)
        ·
          refine ⟨1657073708597558008427807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 70701811566829141692919765 1657073708597558008427807)
          ·
            refine ⟨2485610562896337012641711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657073708597558008427807 2485610562896337012641711)
            ·
              refine ⟨3728415844344505518962567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485610562896337012641711 3728415844344505518962567)
              ·
                refine ⟨5592623766516758278443851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3728415844344505518962567 5592623766516758278443851)
                ·
                  refine ⟨8388935649775137417665777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5592623766516758278443851 8388935649775137417665777)
                  ·
                    refine ⟨6291701737331353063249333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8388935649775137417665777 6291701737331353063249333)
                    ·
                      refine ⟨589847037874814349679625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6291701737331353063249333 589847037874814349679625)
                      ·
                        rfl

theorem cell23_1148723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 5].length) (baseStart_1148723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148723 prefixEnd_1148723 := by exact prefixLift 1148723
  have htrace : WordTrace (prefixWord ++ tailWord_1148723) baseStart_1148723 baseEnd_1148723 := by
    simpa [prefixWord, tailWord_1148723, baseEnd_1148723] using wordTrace_append hprefix tailTrace_1148723
  have hstable : (prefixWord ++ tailWord_1148723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148723).length < 2 ^ (prefixWord ++ tailWord_1148723).sum := by decide
  have hdescent : baseEnd_1148723 < baseStart_1148723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148743 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 3, 4]
def baseStart_1148743 : Nat := 118140960795 + 1148743 * 2 ^ 59
def prefixEnd_1148743 : Nat := 4983230072969 + 3 ^ 40 * 1148743 * 2
def baseEnd_1148743 : Nat := 196619102495968090476511

theorem tailTrace_1148743 : CollatzResearch.WordTrace tailWord_1148743 prefixEnd_1148743 196619102495968090476511 := by
  unfold tailWord_1148743
  simp only [CollatzResearch.WordTrace]
  refine ⟨41898099277307775530050883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27932066184871850353367255 41898099277307775530050883)
  ·
    refine ⟨62847148915961663295076325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41898099277307775530050883 62847148915961663295076325)
    ·
      refine ⟨11783840421742811867826811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62847148915961663295076325 11783840421742811867826811)
      ·
        refine ⟨17675760632614217801740217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11783840421742811867826811 17675760632614217801740217)
        ·
          refine ⟨13256820474460663351305163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17675760632614217801740217 13256820474460663351305163)
          ·
            refine ⟨19885230711690995026957745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13256820474460663351305163 19885230711690995026957745)
            ·
              refine ⟨14913923033768246270218309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19885230711690995026957745 14913923033768246270218309)
              ·
                refine ⟨2796360568831546175665933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14913923033768246270218309 2796360568831546175665933)
                ·
                  refine ⟨1048635213311829815874725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2796360568831546175665933 1048635213311829815874725)
                  ·
                    refine ⟨196619102495968090476511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1048635213311829815874725 196619102495968090476511)
                    ·
                      rfl

theorem cell23_1148743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_1148743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148743 prefixEnd_1148743 := by exact prefixLift 1148743
  have htrace : WordTrace (prefixWord ++ tailWord_1148743) baseStart_1148743 baseEnd_1148743 := by
    simpa [prefixWord, tailWord_1148743, baseEnd_1148743] using wordTrace_append hprefix tailTrace_1148743
  have hstable : (prefixWord ++ tailWord_1148743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148743).length < 2 ^ (prefixWord ++ tailWord_1148743).sum := by decide
  have hdescent : baseEnd_1148743 < baseStart_1148743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148800 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 3, 1, 3]
def baseStart_1148800 : Nat := 118140960795 + 1148800 * 2 ^ 59
def prefixEnd_1148800 : Nat := 4983230072969 + 3 ^ 40 * 1148800 * 2
def baseEnd_1148800 : Nat := 589886575885210548416771

theorem tailTrace_1148800 : CollatzResearch.WordTrace tailWord_1148800 prefixEnd_1148800 589886575885210548416771 := by
  unfold tailWord_1148800
  simp only [CollatzResearch.WordTrace]
  refine ⟨20950089119050637132437927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27933452158734182843250569 20950089119050637132437927)
  ·
    refine ⟨31425133678575955698656891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20950089119050637132437927 31425133678575955698656891)
    ·
      refine ⟨47137700517863933547985337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31425133678575955698656891 47137700517863933547985337)
      ·
        refine ⟨35353275388397950160989003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47137700517863933547985337 35353275388397950160989003)
        ·
          refine ⟨53029913082596925241483505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35353275388397950160989003 53029913082596925241483505)
          ·
            refine ⟨39772434811947693931112629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53029913082596925241483505 39772434811947693931112629)
            ·
              refine ⟨3728665763620096306041809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39772434811947693931112629 3728665763620096306041809)
              ·
                refine ⟨2796499322715072229531357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3728665763620096306041809 2796499322715072229531357)
                ·
                  refine ⟨1048687246018152086074259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2796499322715072229531357 1048687246018152086074259)
                  ·
                    refine ⟨1573030869027228129111389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1048687246018152086074259 1573030869027228129111389)
                    ·
                      refine ⟨589886575885210548416771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1573030869027228129111389 589886575885210548416771)
                      ·
                        rfl

theorem cell23_1148800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_1148800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148800 prefixEnd_1148800 := by exact prefixLift 1148800
  have htrace : WordTrace (prefixWord ++ tailWord_1148800) baseStart_1148800 baseEnd_1148800 := by
    simpa [prefixWord, tailWord_1148800, baseEnd_1148800] using wordTrace_append hprefix tailTrace_1148800
  have hstable : (prefixWord ++ tailWord_1148800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148800).length < 2 ^ (prefixWord ++ tailWord_1148800).sum := by decide
  have hdescent : baseEnd_1148800 < baseStart_1148800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148803 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 3, 5]
def baseStart_1148803 : Nat := 118140960795 + 1148803 * 2 ^ 59
def prefixEnd_1148803 : Nat := 4983230072969 + 3 ^ 40 * 1148803 * 2
def baseEnd_1148803 : Nat := 196629372109058012226419

theorem tailTrace_1148803 : CollatzResearch.WordTrace tailWord_1148803 prefixEnd_1148803 196629372109058012226419 := by
  unfold tailWord_1148803
  simp only [CollatzResearch.WordTrace]
  refine ⟨41900287657090405777235063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27933525104726937184823375 41900287657090405777235063)
  ·
    refine ⟨62850431485635608665852595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41900287657090405777235063 62850431485635608665852595)
    ·
      refine ⟨94275647228453412998778893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62850431485635608665852595 94275647228453412998778893)
      ·
        refine ⟨35353367710670029874542085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94275647228453412998778893 35353367710670029874542085)
        ·
          refine ⟨6628756445750630601476641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35353367710670029874542085 6628756445750630601476641)
          ·
            refine ⟨4971567334312972951107481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6628756445750630601476641 4971567334312972951107481)
            ·
              refine ⟨3728675500734729713330611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4971567334312972951107481 3728675500734729713330611)
              ·
                refine ⟨5593013251102094569995917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3728675500734729713330611 5593013251102094569995917)
                ·
                  refine ⟨2097379969163285463748469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5593013251102094569995917 2097379969163285463748469)
                  ·
                    refine ⟨196629372109058012226419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2097379969163285463748469 196629372109058012226419)
                    ·
                      rfl

theorem cell23_1148803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 5].length) (baseStart_1148803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148803 prefixEnd_1148803 := by exact prefixLift 1148803
  have htrace : WordTrace (prefixWord ++ tailWord_1148803) baseStart_1148803 baseEnd_1148803 := by
    simpa [prefixWord, tailWord_1148803, baseEnd_1148803] using wordTrace_append hprefix tailTrace_1148803
  have hstable : (prefixWord ++ tailWord_1148803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148803).length < 2 ^ (prefixWord ++ tailWord_1148803).sum := by decide
  have hdescent : baseEnd_1148803 < baseStart_1148803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148817 : List Nat := [1, 2, 2, 1, 1, 1, 5, 5, 1, 1, 3]
def baseStart_1148817 : Nat := 118140960795 + 1148817 * 2 ^ 59
def prefixEnd_1148817 : Nat := 4983230072969 + 3 ^ 40 * 1148817 * 2
def baseEnd_1148817 : Nat := 589895305056336981904193

theorem tailTrace_1148817 : CollatzResearch.WordTrace tailWord_1148817 prefixEnd_1148817 589895305056336981904193 := by
  unfold tailWord_1148817
  simp only [CollatzResearch.WordTrace]
  refine ⟨41900798279039686168244705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27933865519359790778829803 41900798279039686168244705)
  ·
    refine ⟨31425598709279764626183529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41900798279039686168244705 31425598709279764626183529)
    ·
      refine ⟨23569199031959823469637647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31425598709279764626183529 23569199031959823469637647)
      ·
        refine ⟨35353798547939735204456471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23569199031959823469637647 35353798547939735204456471)
        ·
          refine ⟨53030697821909602806684707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35353798547939735204456471 53030697821909602806684707)
          ·
            refine ⟨79546046732864404210027061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53030697821909602806684707 79546046732864404210027061)
            ·
              refine ⟨7457441881206037894690037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79546046732864404210027061 7457441881206037894690037)
              ·
                refine ⟨699135176363066052627191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7457441881206037894690037 699135176363066052627191)
                ·
                  refine ⟨1048702764544599078940787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699135176363066052627191 1048702764544599078940787)
                  ·
                    refine ⟨1573054146816898618411181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1048702764544599078940787 1573054146816898618411181)
                    ·
                      refine ⟨589895305056336981904193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1573054146816898618411181 589895305056336981904193)
                      ·
                        rfl

theorem cell23_1148817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 1, 1, 3].length) (baseStart_1148817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148817 prefixEnd_1148817 := by exact prefixLift 1148817
  have htrace : WordTrace (prefixWord ++ tailWord_1148817) baseStart_1148817 baseEnd_1148817 := by
    simpa [prefixWord, tailWord_1148817, baseEnd_1148817] using wordTrace_append hprefix tailTrace_1148817
  have hstable : (prefixWord ++ tailWord_1148817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148817).length < 2 ^ (prefixWord ++ tailWord_1148817).sum := by decide
  have hdescent : baseEnd_1148817 < baseStart_1148817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148824 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 6]
def baseStart_1148824 : Nat := 118140960795 + 1148824 * 2 ^ 59
def prefixEnd_1148824 : Nat := 4983230072969 + 3 ^ 40 * 1148824 * 2
def baseEnd_1148824 : Nat := 65544322157879828279629

theorem tailTrace_1148824 : CollatzResearch.WordTrace tailWord_1148824 prefixEnd_1148824 65544322157879828279629 := by
  unfold tailWord_1148824
  simp only [CollatzResearch.WordTrace]
  refine ⟨20950526795007163181874763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27934035726676217575833017 20950526795007163181874763)
  ·
    refine ⟨31425790192510744772812145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20950526795007163181874763 31425790192510744772812145)
    ·
      refine ⟨23569342644383058579609109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31425790192510744772812145 23569342644383058579609109)
      ·
        refine ⟨1104812936455455870919177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23569342644383058579609109 1104812936455455870919177)
        ·
          refine ⟨828609702341591903189383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1104812936455455870919177 828609702341591903189383)
          ·
            refine ⟨1242914553512387854784075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828609702341591903189383 1242914553512387854784075)
            ·
              refine ⟨1864371830268581782176113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242914553512387854784075 1864371830268581782176113)
              ·
                refine ⟨1398278872701436336632085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864371830268581782176113 1398278872701436336632085)
                ·
                  refine ⟨65544322157879828279629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1398278872701436336632085 65544322157879828279629)
                  ·
                    rfl

theorem cell23_1148824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 6].length) (baseStart_1148824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148824 prefixEnd_1148824 := by exact prefixLift 1148824
  have htrace : WordTrace (prefixWord ++ tailWord_1148824) baseStart_1148824 baseEnd_1148824 := by
    simpa [prefixWord, tailWord_1148824, baseEnd_1148824] using wordTrace_append hprefix tailTrace_1148824
  have hstable : (prefixWord ++ tailWord_1148824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148824).length < 2 ^ (prefixWord ++ tailWord_1148824).sum := by decide
  have hdescent : baseEnd_1148824 < baseStart_1148824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148834 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_1148834 : Nat := 118140960795 + 1148834 * 2 ^ 59
def prefixEnd_1148834 : Nat := 4983230072969 + 3 ^ 40 * 1148834 * 2
def baseEnd_1148834 : Nat := 589904034227463415391615

theorem tailTrace_1148834 : CollatzResearch.WordTrace tailWord_1148834 prefixEnd_1148834 589904034227463415391615 := by
  unfold tailWord_1148834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10475354579994524517903389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27934278879985398714409037 10475354579994524517903389)
  ·
    refine ⟨3928257967497946694213771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10475354579994524517903389 3928257967497946694213771)
    ·
      refine ⟨5892386951246920041320657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3928257967497946694213771 5892386951246920041320657)
      ·
        refine ⟨4419290213435190030990493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5892386951246920041320657 4419290213435190030990493)
        ·
          refine ⟨1657233830038196261621435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4419290213435190030990493 1657233830038196261621435)
          ·
            refine ⟨2485850745057294392432153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657233830038196261621435 2485850745057294392432153)
            ·
              refine ⟨1864388058792970794324115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2485850745057294392432153 1864388058792970794324115)
              ·
                refine ⟨2796582088189456191486173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864388058792970794324115 2796582088189456191486173)
                ·
                  refine ⟨1048718283071046071807315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2796582088189456191486173 1048718283071046071807315)
                  ·
                    refine ⟨1573077424606569107710973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1048718283071046071807315 1573077424606569107710973)
                    ·
                      refine ⟨589904034227463415391615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1573077424606569107710973 589904034227463415391615)
                      ·
                        rfl

theorem cell23_1148834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_1148834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148834 prefixEnd_1148834 := by exact prefixLift 1148834
  have htrace : WordTrace (prefixWord ++ tailWord_1148834) baseStart_1148834 baseEnd_1148834 := by
    simpa [prefixWord, tailWord_1148834, baseEnd_1148834] using wordTrace_append hprefix tailTrace_1148834
  have hstable : (prefixWord ++ tailWord_1148834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148834).length < 2 ^ (prefixWord ++ tailWord_1148834).sum := by decide
  have hdescent : baseEnd_1148834 < baseStart_1148834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148850 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_1148850 : Nat := 118140960795 + 1148850 * 2 ^ 59
def prefixEnd_1148850 : Nat := 4983230072969 + 3 ^ 40 * 1148850 * 2
def baseEnd_1148850 : Nat := 196637416639311784263847

theorem tailTrace_1148850 : CollatzResearch.WordTrace tailWord_1148850 prefixEnd_1148850 196637416639311784263847 := by
  unfold tailWord_1148850
  simp only [CollatzResearch.WordTrace]
  refine ⟨10475500471980033201049001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27934667925280088536130669 10475500471980033201049001)
  ·
    refine ⟨7856625353985024900786751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10475500471980033201049001 7856625353985024900786751)
    ·
      refine ⟨11784938030977537351180127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7856625353985024900786751 11784938030977537351180127)
      ·
        refine ⟨17677407046466306026770191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11784938030977537351180127 17677407046466306026770191)
        ·
          refine ⟨26516110569699459040155287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17677407046466306026770191 26516110569699459040155287)
          ·
            refine ⟨39774165854549188560232931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26516110569699459040155287 39774165854549188560232931)
            ·
              refine ⟨59661248781823782840349397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39774165854549188560232931 59661248781823782840349397)
              ·
                refine ⟨1398310518323994910320689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 59661248781823782840349397 1398310518323994910320689)
                ·
                  refine ⟨1048732888742996182740517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1398310518323994910320689 1048732888742996182740517)
                  ·
                    refine ⟨196637416639311784263847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1048732888742996182740517 196637416639311784263847)
                    ·
                      rfl

theorem cell23_1148850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_1148850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148850 prefixEnd_1148850 := by exact prefixLift 1148850
  have htrace : WordTrace (prefixWord ++ tailWord_1148850) baseStart_1148850 baseEnd_1148850 := by
    simpa [prefixWord, tailWord_1148850, baseEnd_1148850] using wordTrace_append hprefix tailTrace_1148850
  have hstable : (prefixWord ++ tailWord_1148850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148850).length < 2 ^ (prefixWord ++ tailWord_1148850).sum := by decide
  have hdescent : baseEnd_1148850 < baseStart_1148850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148857 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 3, 2, 2]
def baseStart_1148857 : Nat := 118140960795 + 1148857 * 2 ^ 59
def prefixEnd_1148857 : Nat := 4983230072969 + 3 ^ 40 * 1148857 * 2
def baseEnd_1148857 : Nat := 589915844282516825404009

theorem tailTrace_1148857 : CollatzResearch.WordTrace tailWord_1148857 prefixEnd_1148857 589915844282516825404009 := by
  unfold tailWord_1148857
  simp only [CollatzResearch.WordTrace]
  refine ⟨41902257198894772999700825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27934838132596515333133883 41902257198894772999700825)
  ·
    refine ⟨31426692899171079749775619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41902257198894772999700825 31426692899171079749775619)
    ·
      refine ⟨47140039348756619624663429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31426692899171079749775619 47140039348756619624663429)
      ·
        refine ⟨8838757377891866179624393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47140039348756619624663429 8838757377891866179624393)
        ·
          refine ⟨6629068033418899634718295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8838757377891866179624393 6629068033418899634718295)
          ·
            refine ⟨9943602050128349452077443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6629068033418899634718295 9943602050128349452077443)
            ·
              refine ⟨14915403075192524178116165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9943602050128349452077443 14915403075192524178116165)
              ·
                refine ⟨2796638076598598283396781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14915403075192524178116165 2796638076598598283396781)
                ·
                  refine ⟨1048739278724474356273793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2796638076598598283396781 1048739278724474356273793)
                  ·
                    refine ⟨786554459043355767205345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1048739278724474356273793 786554459043355767205345)
                    ·
                      refine ⟨589915844282516825404009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 786554459043355767205345 589915844282516825404009)
                      ·
                        rfl

theorem cell23_1148857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_1148857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148857 prefixEnd_1148857 := by exact prefixLift 1148857
  have htrace : WordTrace (prefixWord ++ tailWord_1148857) baseStart_1148857 baseEnd_1148857 := by
    simpa [prefixWord, tailWord_1148857, baseEnd_1148857] using wordTrace_append hprefix tailTrace_1148857
  have hstable : (prefixWord ++ tailWord_1148857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148857).length < 2 ^ (prefixWord ++ tailWord_1148857).sum := by decide
  have hdescent : baseEnd_1148857 < baseStart_1148857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148947 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 4, 2, 2]
def baseStart_1148947 : Nat := 118140960795 + 1148947 * 2 ^ 59
def prefixEnd_1148947 : Nat := 4983230072969 + 3 ^ 40 * 1148947 * 2
def baseEnd_1148947 : Nat := 589962057541421473278595

theorem tailTrace_1148947 : CollatzResearch.WordTrace tailWord_1148947 prefixEnd_1148947 589962057541421473278595 := by
  unfold tailWord_1148947
  simp only [CollatzResearch.WordTrace]
  refine ⟨41905539768568718370477095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27937026512379145580318063 41905539768568718370477095)
  ·
    refine ⟨62858309652853077555715643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41905539768568718370477095 62858309652853077555715643)
    ·
      refine ⟨94287464479279616333573465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62858309652853077555715643 94287464479279616333573465)
      ·
        refine ⟨70715598359459712250180099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94287464479279616333573465 70715598359459712250180099)
        ·
          refine ⟨106073397539189568375270149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70715598359459712250180099 106073397539189568375270149)
          ·
            refine ⟨19888762038598044070363153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106073397539189568375270149 19888762038598044070363153)
            ·
              refine ⟨14916571528948533052772365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19888762038598044070363153 14916571528948533052772365)
              ·
                refine ⟨5593714323355699894789637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14916571528948533052772365 5593714323355699894789637)
                ·
                  refine ⟨1048821435629193730273057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5593714323355699894789637 1048821435629193730273057)
                  ·
                    refine ⟨786616076721895297704793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1048821435629193730273057 786616076721895297704793)
                    ·
                      refine ⟨589962057541421473278595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 786616076721895297704793 589962057541421473278595)
                      ·
                        rfl

theorem cell23_1148947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 2, 2].length) (baseStart_1148947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148947 prefixEnd_1148947 := by exact prefixLift 1148947
  have htrace : WordTrace (prefixWord ++ tailWord_1148947) baseStart_1148947 baseEnd_1148947 := by
    simpa [prefixWord, tailWord_1148947, baseEnd_1148947] using wordTrace_append hprefix tailTrace_1148947
  have hstable : (prefixWord ++ tailWord_1148947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148947).length < 2 ^ (prefixWord ++ tailWord_1148947).sum := by decide
  have hdescent : baseEnd_1148947 < baseStart_1148947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148953 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 7]
def baseStart_1148953 : Nat := 118140960795 + 1148953 * 2 ^ 59
def prefixEnd_1148953 : Nat := 4983230072969 + 3 ^ 40 * 1148953 * 2
def baseEnd_1148953 : Nat := 65551682047260938867063

theorem tailTrace_1148953 : CollatzResearch.WordTrace tailWord_1148953 prefixEnd_1148953 65551682047260938867063 := by
  unfold tailWord_1148953
  simp only [CollatzResearch.WordTrace]
  refine ⟨41905758606546981395195513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27937172404364654263463675 41905758606546981395195513)
  ·
    refine ⟨31429318954910236046396635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41905758606546981395195513 31429318954910236046396635)
    ·
      refine ⟨47143978432365354069594953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31429318954910236046396635 47143978432365354069594953)
      ·
        refine ⟨35357983824274015552196215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47143978432365354069594953 35357983824274015552196215)
        ·
          refine ⟨53036975736411023328294323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35357983824274015552196215 53036975736411023328294323)
          ·
            refine ⟨79555463604616534992441485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53036975736411023328294323 79555463604616534992441485)
            ·
              refine ⟨29833298851731200622165557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79555463604616534992441485 29833298851731200622165557)
              ·
                refine ⟨2796871767349800058328021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29833298851731200622165557 2796871767349800058328021)
                ·
                  refine ⟨65551682047260938867063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2796871767349800058328021 65551682047260938867063)
                  ·
                    rfl

theorem cell23_1148953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 7].length) (baseStart_1148953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148953 prefixEnd_1148953 := by exact prefixLift 1148953
  have htrace : WordTrace (prefixWord ++ tailWord_1148953) baseStart_1148953 baseEnd_1148953 := by
    simpa [prefixWord, tailWord_1148953, baseEnd_1148953] using wordTrace_append hprefix tailTrace_1148953
  have hstable : (prefixWord ++ tailWord_1148953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148953).length < 2 ^ (prefixWord ++ tailWord_1148953).sum := by decide
  have hdescent : baseEnd_1148953 < baseStart_1148953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148970 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 9]
def baseStart_1148970 : Nat := 118140960795 + 1148970 * 2 ^ 59
def prefixEnd_1148970 : Nat := 4983230072969 + 3 ^ 40 * 1148970 * 2
def baseEnd_1148970 : Nat := 65552651955163875921221

theorem tailTrace_1148970 : CollatzResearch.WordTrace tailWord_1148970 prefixEnd_1148970 65552651955163875921221 := by
  unfold tailWord_1148970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10476594661871348324641091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27937585764990262199042909 10476594661871348324641091)
  ·
    refine ⟨15714891992807022486961637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10476594661871348324641091 15714891992807022486961637)
    ·
      refine ⟨2946542248651316716305307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15714891992807022486961637 2946542248651316716305307)
      ·
        refine ⟨4419813372976975074457961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2946542248651316716305307 4419813372976975074457961)
        ·
          refine ⟨3314860029732731305843471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4419813372976975074457961 3314860029732731305843471)
          ·
            refine ⟨4972290044599096958765207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3314860029732731305843471 4972290044599096958765207)
            ·
              refine ⟨7458435066898645438147811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4972290044599096958765207 7458435066898645438147811)
              ·
                refine ⟨11187652600347968157221717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7458435066898645438147811 11187652600347968157221717)
                ·
                  refine ⟨65552651955163875921221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11187652600347968157221717 65552651955163875921221)
                  ·
                    rfl

theorem cell23_1148970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_1148970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148970 prefixEnd_1148970 := by exact prefixLift 1148970
  have htrace : WordTrace (prefixWord ++ tailWord_1148970) baseStart_1148970 baseEnd_1148970 := by
    simpa [prefixWord, tailWord_1148970, baseEnd_1148970] using wordTrace_append hprefix tailTrace_1148970
  have hstable : (prefixWord ++ tailWord_1148970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148970).length < 2 ^ (prefixWord ++ tailWord_1148970).sum := by decide
  have hdescent : baseEnd_1148970 < baseStart_1148970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149037 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1149037 : Nat := 118140960795 + 1149037 * 2 ^ 59
def prefixEnd_1149037 : Nat := 4983230072969 + 3 ^ 40 * 1149037 * 2
def baseEnd_1149037 : Nat := 590008270800326121153181

theorem tailTrace_1149037 : CollatzResearch.WordTrace tailWord_1149037 prefixEnd_1149037 590008270800326121153181 := by
  unfold tailWord_1149037
  simp only [CollatzResearch.WordTrace]
  refine ⟨41908822338242663741253365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27939214892161775827502243 41908822338242663741253365)
  ·
    refine ⟨3928952094210249725742503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41908822338242663741253365 3928952094210249725742503)
    ·
      refine ⟨5893428141315374588613755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3928952094210249725742503 5893428141315374588613755)
      ·
        refine ⟨8840142211973061882920633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5893428141315374588613755 8840142211973061882920633)
        ·
          refine ⟨6630106658979796412190475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8840142211973061882920633 6630106658979796412190475)
          ·
            refine ⟨9945159988469694618285713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6630106658979796412190475 9945159988469694618285713)
            ·
              refine ⟨7458869991352270963714285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9945159988469694618285713 7458869991352270963714285)
              ·
                refine ⟨2797076246757101611392857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7458869991352270963714285 2797076246757101611392857)
                ·
                  refine ⟨2097807185067826208544643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2797076246757101611392857 2097807185067826208544643)
                  ·
                    refine ⟨3146710777601739312816965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2097807185067826208544643 3146710777601739312816965)
                    ·
                      refine ⟨590008270800326121153181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3146710777601739312816965 590008270800326121153181)
                      ·
                        rfl

theorem cell23_1149037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1149037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149037 prefixEnd_1149037 := by exact prefixLift 1149037
  have htrace : WordTrace (prefixWord ++ tailWord_1149037) baseStart_1149037 baseEnd_1149037 := by
    simpa [prefixWord, tailWord_1149037, baseEnd_1149037] using wordTrace_append hprefix tailTrace_1149037
  have hstable : (prefixWord ++ tailWord_1149037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149037).length < 2 ^ (prefixWord ++ tailWord_1149037).sum := by decide
  have hdescent : baseEnd_1149037 < baseStart_1149037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149060 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 8]
def baseStart_1149060 : Nat := 118140960795 + 1149060 * 2 ^ 59
def prefixEnd_1149060 : Nat := 4983230072969 + 3 ^ 40 * 1149060 * 2
def baseEnd_1149060 : Nat := 65557786761708836796175

theorem tailTrace_1149060 : CollatzResearch.WordTrace tailWord_1149060 prefixEnd_1149060 65557786761708836796175 := by
  unfold tailWord_1149060
  simp only [CollatzResearch.WordTrace]
  refine ⟨20954830608579669334670317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27939774144772892446227089 20954830608579669334670317)
  ·
    refine ⟨7858061478217376000501369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20954830608579669334670317 7858061478217376000501369)
    ·
      refine ⟨5893546108663032000376027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7858061478217376000501369 5893546108663032000376027)
      ·
        refine ⟨8840319162994548000564041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5893546108663032000376027 8840319162994548000564041)
        ·
          refine ⟨6630239372245911000423031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8840319162994548000564041 6630239372245911000423031)
          ·
            refine ⟨9945359058368866500634547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6630239372245911000423031 9945359058368866500634547)
            ·
              refine ⟨14918038587553299750951821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9945359058368866500634547 14918038587553299750951821)
              ·
                refine ⟨5594264470332487406606933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14918038587553299750951821 5594264470332487406606933)
                ·
                  refine ⟨65557786761708836796175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5594264470332487406606933 65557786761708836796175)
                  ·
                    rfl

theorem cell23_1149060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_1149060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149060 prefixEnd_1149060 := by exact prefixLift 1149060
  have htrace : WordTrace (prefixWord ++ tailWord_1149060) baseStart_1149060 baseEnd_1149060 := by
    simpa [prefixWord, tailWord_1149060, baseEnd_1149060] using wordTrace_append hprefix tailTrace_1149060
  have hstable : (prefixWord ++ tailWord_1149060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149060).length < 2 ^ (prefixWord ++ tailWord_1149060).sum := by decide
  have hdescent : baseEnd_1149060 < baseStart_1149060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149064 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 3, 4]
def baseStart_1149064 : Nat := 118140960795 + 1149064 * 2 ^ 59
def prefixEnd_1149064 : Nat := 4983230072969 + 3 ^ 40 * 1149064 * 2
def baseEnd_1149064 : Nat := 196674044925999171838519

theorem tailTrace_1149064 : CollatzResearch.WordTrace tailWord_1149064 prefixEnd_1149064 196674044925999171838519 := by
  unfold tailWord_1149064
  simp only [CollatzResearch.WordTrace]
  refine ⟨20954903554572423676243123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27939871406096564901657497 20954903554572423676243123)
  ·
    refine ⟨31432355331858635514364685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20954903554572423676243123 31432355331858635514364685)
    ·
      refine ⟨11787133249446988317886757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31432355331858635514364685 11787133249446988317886757)
      ·
        refine ⟨2210087484271310309603767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11787133249446988317886757 2210087484271310309603767)
        ·
          refine ⟨3315131226406965464405651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2210087484271310309603767 3315131226406965464405651)
          ·
            refine ⟨4972696839610448196608477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3315131226406965464405651 4972696839610448196608477)
            ·
              refine ⟨1864761314853918073728179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4972696839610448196608477 1864761314853918073728179)
              ·
                refine ⟨2797141972280877110592269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864761314853918073728179 2797141972280877110592269)
                ·
                  refine ⟨1048928239605328916472101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2797141972280877110592269 1048928239605328916472101)
                  ·
                    refine ⟨196674044925999171838519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1048928239605328916472101 196674044925999171838519)
                    ·
                      rfl

theorem cell23_1149064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_1149064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149064 prefixEnd_1149064 := by exact prefixLift 1149064
  have htrace : WordTrace (prefixWord ++ tailWord_1149064) baseStart_1149064 baseEnd_1149064 := by
    simpa [prefixWord, tailWord_1149064, baseEnd_1149064] using wordTrace_append hprefix tailTrace_1149064
  have hstable : (prefixWord ++ tailWord_1149064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149064).length < 2 ^ (prefixWord ++ tailWord_1149064).sum := by decide
  have hdescent : baseEnd_1149064 < baseStart_1149064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149114 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2]
def baseStart_1149114 : Nat := 118140960795 + 1149114 * 2 ^ 59
def prefixEnd_1149114 : Nat := 4983230072969 + 3 ^ 40 * 1149114 * 2
def baseEnd_1149114 : Nat := 590047808810722319890327

theorem tailTrace_1149114 : CollatzResearch.WordTrace tailWord_1149114 prefixEnd_1149114 590047808810722319890327 := by
  unfold tailWord_1149114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10477907689740926472951599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27941087172642470594537597 10477907689740926472951599)
  ·
    refine ⟨15716861534611389709427399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10477907689740926472951599 15716861534611389709427399)
    ·
      refine ⟨23575292301917084564141099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15716861534611389709427399 23575292301917084564141099)
      ·
        refine ⟨35362938452875626846211649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23575292301917084564141099 35362938452875626846211649)
        ·
          refine ⟨26522203839656720134658737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35362938452875626846211649 26522203839656720134658737)
          ·
            refine ⟨19891652879742540100994053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26522203839656720134658737 19891652879742540100994053)
            ·
              refine ⟨3729684914951726268936385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19891652879742540100994053 3729684914951726268936385)
              ·
                refine ⟨2797263686213794701702289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3729684914951726268936385 2797263686213794701702289)
                ·
                  refine ⟨2097947764660346026276717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2797263686213794701702289 2097947764660346026276717)
                  ·
                    refine ⟨786730411747629759853769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2097947764660346026276717 786730411747629759853769)
                    ·
                      refine ⟨590047808810722319890327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 786730411747629759853769 590047808810722319890327)
                      ·
                        rfl

theorem cell23_1149114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2].length) (baseStart_1149114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149114 prefixEnd_1149114 := by exact prefixLift 1149114
  have htrace : WordTrace (prefixWord ++ tailWord_1149114) baseStart_1149114 baseEnd_1149114 := by
    simpa [prefixWord, tailWord_1149114, baseEnd_1149114] using wordTrace_append hprefix tailTrace_1149114
  have hstable : (prefixWord ++ tailWord_1149114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149114).length < 2 ^ (prefixWord ++ tailWord_1149114).sum := by decide
  have hdescent : baseEnd_1149114 < baseStart_1149114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149127 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 4, 6, 2]
def baseStart_1149127 : Nat := 118140960795 + 1149127 * 2 ^ 59
def prefixEnd_1149127 : Nat := 4983230072969 + 3 ^ 40 * 1149127 * 2
def baseEnd_1149127 : Nat := 590054484059230769027767

theorem tailTrace_1149127 : CollatzResearch.WordTrace tailWord_1149127 prefixEnd_1149127 590054484059230769027767 := by
  unfold tailWord_1149127
  simp only [CollatzResearch.WordTrace]
  refine ⟨41912104907916609112029635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27941403271944406074686423 41912104907916609112029635)
  ·
    refine ⟨62868157361874913668044453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41912104907916609112029635 62868157361874913668044453)
    ·
      refine ⟨11787779505351546312758335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62868157361874913668044453 11787779505351546312758335)
      ·
        refine ⟨17681669258027319469137503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11787779505351546312758335 17681669258027319469137503)
        ·
          refine ⟨26522503887040979203706255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17681669258027319469137503 26522503887040979203706255)
          ·
            refine ⟨39783755830561468805559383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26522503887040979203706255 39783755830561468805559383)
            ·
              refine ⟨59675633745842203208339075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39783755830561468805559383 59675633745842203208339075)
              ·
                refine ⟨89513450618763304812508613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59675633745842203208339075 89513450618763304812508613)
                ·
                  refine ⟨16783771991018119652345365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89513450618763304812508613 16783771991018119652345365)
                  ·
                    refine ⟨786739312078974358703689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16783771991018119652345365 786739312078974358703689)
                    ·
                      refine ⟨590054484059230769027767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 786739312078974358703689 590054484059230769027767)
                      ·
                        rfl

theorem cell23_1149127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_1149127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149127 prefixEnd_1149127 := by exact prefixLift 1149127
  have htrace : WordTrace (prefixWord ++ tailWord_1149127) baseStart_1149127 baseEnd_1149127 := by
    simpa [prefixWord, tailWord_1149127, baseEnd_1149127] using wordTrace_append hprefix tailTrace_1149127
  have hstable : (prefixWord ++ tailWord_1149127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149127).length < 2 ^ (prefixWord ++ tailWord_1149127).sum := by decide
  have hdescent : baseEnd_1149127 < baseStart_1149127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149148 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1149148 : Nat := 118140960795 + 1149148 * 2 ^ 59
def prefixEnd_1149148 : Nat := 4983230072969 + 3 ^ 40 * 1149148 * 2
def baseEnd_1149148 : Nat := 590065267152975186865171

theorem tailTrace_1149148 : CollatzResearch.WordTrace tailWord_1149148 prefixEnd_1149148 590065267152975186865171 := by
  unfold tailWord_1149148
  simp only [CollatzResearch.WordTrace]
  refine ⟨20956435420420264849272049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27941913893893686465696065 20956435420420264849272049)
  ·
    refine ⟨15717326565315198636954037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20956435420420264849272049 15717326565315198636954037)
    ·
      refine ⟨1473499365498299872214441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15717326565315198636954037 1473499365498299872214441)
      ·
        refine ⟨1105124524123724904160831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1473499365498299872214441 1105124524123724904160831)
        ·
          refine ⟨1657686786185587356241247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105124524123724904160831 1657686786185587356241247)
          ·
            refine ⟨2486530179278381034361871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657686786185587356241247 2486530179278381034361871)
            ·
              refine ⟨3729795268917571551542807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486530179278381034361871 3729795268917571551542807)
              ·
                refine ⟨5594692903376357327314211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3729795268917571551542807 5594692903376357327314211)
                ·
                  refine ⟨8392039355064535990971317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5594692903376357327314211 8392039355064535990971317)
                  ·
                    refine ⟨786753689537300249153561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8392039355064535990971317 786753689537300249153561)
                    ·
                      refine ⟨590065267152975186865171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 786753689537300249153561 590065267152975186865171)
                      ·
                        rfl

theorem cell23_1149148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1149148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149148 prefixEnd_1149148 := by exact prefixLift 1149148
  have htrace : WordTrace (prefixWord ++ tailWord_1149148) baseStart_1149148 baseEnd_1149148 := by
    simpa [prefixWord, tailWord_1149148, baseEnd_1149148] using wordTrace_append hprefix tailTrace_1149148
  have hstable : (prefixWord ++ tailWord_1149148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149148).length < 2 ^ (prefixWord ++ tailWord_1149148).sum := by decide
  have hdescent : baseEnd_1149148 < baseStart_1149148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149155 : List Nat := [1, 1, 1, 8, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1149155 : Nat := 118140960795 + 1149155 * 2 ^ 59
def prefixEnd_1149155 : Nat := 4983230072969 + 3 ^ 40 * 1149155 * 2
def baseEnd_1149155 : Nat := 590068861517556659477639

theorem tailTrace_1149155 : CollatzResearch.WordTrace tailWord_1149155 prefixEnd_1149155 590068861517556659477639 := by
  unfold tailWord_1149155
  simp only [CollatzResearch.WordTrace]
  refine ⟨41913126151815169894048919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27942084101210113262699279 41913126151815169894048919)
  ·
    refine ⟨62869689227722754841073379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41913126151815169894048919 62869689227722754841073379)
    ·
      refine ⟨94304533841584132261610069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62869689227722754841073379 94304533841584132261610069)
      ·
        refine ⟨1105131255956064049940743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 94304533841584132261610069 1105131255956064049940743)
        ·
          refine ⟨1657696883934096074911115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105131255956064049940743 1657696883934096074911115)
          ·
            refine ⟨2486545325901144112366673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657696883934096074911115 2486545325901144112366673)
            ·
              refine ⟨1864908994425858084275005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486545325901144112366673 1864908994425858084275005)
              ·
                refine ⟨699340872909696781603127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1864908994425858084275005 699340872909696781603127)
                ·
                  refine ⟨1049011309364545172404691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699340872909696781603127 1049011309364545172404691)
                  ·
                    refine ⟨1573516964046817758607037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1049011309364545172404691 1573516964046817758607037)
                    ·
                      refine ⟨590068861517556659477639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1573516964046817758607037 590068861517556659477639)
                      ·
                        rfl

theorem cell23_1149155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1149155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149155 prefixEnd_1149155 := by exact prefixLift 1149155
  have htrace : WordTrace (prefixWord ++ tailWord_1149155) baseStart_1149155 baseEnd_1149155 := by
    simpa [prefixWord, tailWord_1149155, baseEnd_1149155] using wordTrace_append hprefix tailTrace_1149155
  have hstable : (prefixWord ++ tailWord_1149155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149155).length < 2 ^ (prefixWord ++ tailWord_1149155).sum := by decide
  have hdescent : baseEnd_1149155 < baseStart_1149155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149164 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 3]
def baseStart_1149164 : Nat := 118140960795 + 1149164 * 2 ^ 59
def prefixEnd_1149164 : Nat := 4983230072969 + 3 ^ 40 * 1149164 * 2
def baseEnd_1149164 : Nat := 590073482843447124265097

theorem tailTrace_1149164 : CollatzResearch.WordTrace tailWord_1149164 prefixEnd_1149164 590073482843447124265097 := by
  unfold tailWord_1149164
  simp only [CollatzResearch.WordTrace]
  refine ⟨20956727204391282215563273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27942302939188376287417697 20956727204391282215563273)
  ·
    refine ⟨15717545403293461661672455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20956727204391282215563273 15717545403293461661672455)
    ·
      refine ⟨23576318104940192492508683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15717545403293461661672455 23576318104940192492508683)
      ·
        refine ⟨35364477157410288738763025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23576318104940192492508683 35364477157410288738763025)
        ·
          refine ⟨26523357868057716554072269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35364477157410288738763025 26523357868057716554072269)
          ·
            refine ⟨9946259200521643707777101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26523357868057716554072269 9946259200521643707777101)
            ·
              refine ⟨3729847200195616390416413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9946259200521643707777101 3729847200195616390416413)
              ·
                refine ⟨1398692700073356146406155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3729847200195616390416413 1398692700073356146406155)
                ·
                  refine ⟨2098039050110034219609233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398692700073356146406155 2098039050110034219609233)
                  ·
                    refine ⟨1573529287582525664706925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2098039050110034219609233 1573529287582525664706925)
                    ·
                      refine ⟨590073482843447124265097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1573529287582525664706925 590073482843447124265097)
                      ·
                        rfl

theorem cell23_1149164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_1149164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149164 prefixEnd_1149164 := by exact prefixLift 1149164
  have htrace : WordTrace (prefixWord ++ tailWord_1149164) baseStart_1149164 baseEnd_1149164 := by
    simpa [prefixWord, tailWord_1149164, baseEnd_1149164] using wordTrace_append hprefix tailTrace_1149164
  have hstable : (prefixWord ++ tailWord_1149164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149164).length < 2 ^ (prefixWord ++ tailWord_1149164).sum := by decide
  have hdescent : baseEnd_1149164 < baseStart_1149164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149178 : List Nat := [3, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2]
def baseStart_1149178 : Nat := 118140960795 + 1149178 * 2 ^ 59
def prefixEnd_1149178 : Nat := 4983230072969 + 3 ^ 40 * 1149178 * 2
def baseEnd_1149178 : Nat := 590080671572610069490033

theorem tailTrace_1149178 : CollatzResearch.WordTrace tailWord_1149178 prefixEnd_1149178 590080671572610069490033 := by
  unfold tailWord_1149178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10478491257682961205534047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27942643353821229881424125 10478491257682961205534047)
  ·
    refine ⟨15717736886524441808301071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10478491257682961205534047 15717736886524441808301071)
    ·
      refine ⟨23576605329786662712451607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15717736886524441808301071 23576605329786662712451607)
      ·
        refine ⟨35364907994679994068677411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23576605329786662712451607 35364907994679994068677411)
        ·
          refine ⟨53047361992019991103016117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35364907994679994068677411 53047361992019991103016117)
          ·
            refine ⟨4973190186751874165907761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53047361992019991103016117 4973190186751874165907761)
            ·
              refine ⟨3729892640063905624430821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4973190186751874165907761 3729892640063905624430821)
              ·
                refine ⟨699354870011982304580779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3729892640063905624430821 699354870011982304580779)
                ·
                  refine ⟨1049032305017973456871169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699354870011982304580779 1049032305017973456871169)
                  ·
                    refine ⟨786774228763480092653377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1049032305017973456871169 786774228763480092653377)
                    ·
                      refine ⟨590080671572610069490033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 786774228763480092653377 590080671572610069490033)
                      ·
                        rfl

theorem cell23_1149178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2].length) (baseStart_1149178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149178 prefixEnd_1149178 := by exact prefixLift 1149178
  have htrace : WordTrace (prefixWord ++ tailWord_1149178) baseStart_1149178 baseEnd_1149178 := by
    simpa [prefixWord, tailWord_1149178, baseEnd_1149178] using wordTrace_append hprefix tailTrace_1149178
  have hstable : (prefixWord ++ tailWord_1149178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149178).length < 2 ^ (prefixWord ++ tailWord_1149178).sum := by decide
  have hdescent : baseEnd_1149178 < baseStart_1149178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149188 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_1149188 : Nat := 118140960795 + 1149188 * 2 ^ 59
def prefixEnd_1149188 : Nat := 4983230072969 + 3 ^ 40 * 1149188 * 2
def baseEnd_1149188 : Nat := 196695268793051676788329

theorem tailTrace_1149188 : CollatzResearch.WordTrace tailWord_1149188 prefixEnd_1149188 196695268793051676788329 := by
  unfold tailWord_1149188
  simp only [CollatzResearch.WordTrace]
  refine ⟨20957164880347808265000109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27942886507130411020000145 20957164880347808265000109)
  ·
    refine ⟨7858936830130428099375041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20957164880347808265000109 7858936830130428099375041)
    ·
      refine ⟨5894202622597821074531281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7858936830130428099375041 5894202622597821074531281)
      ·
        refine ⟨4420651966948365805898461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5894202622597821074531281 4420651966948365805898461)
        ·
          refine ⟨1657744487605637177211923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4420651966948365805898461 1657744487605637177211923)
          ·
            refine ⟨2486616731408455765817885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657744487605637177211923 2486616731408455765817885)
            ·
              refine ⟨932481274278170912181707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2486616731408455765817885 932481274278170912181707)
              ·
                refine ⟨1398721911417256368272561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932481274278170912181707 1398721911417256368272561)
                ·
                  refine ⟨1049041433562942276204421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1398721911417256368272561 1049041433562942276204421)
                  ·
                    refine ⟨196695268793051676788329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1049041433562942276204421 196695268793051676788329)
                    ·
                      rfl

theorem cell23_1149188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_1149188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149188 prefixEnd_1149188 := by exact prefixLift 1149188
  have htrace : WordTrace (prefixWord ++ tailWord_1149188) baseStart_1149188 baseEnd_1149188 := by
    simpa [prefixWord, tailWord_1149188, baseEnd_1149188] using wordTrace_append hprefix tailTrace_1149188
  have hstable : (prefixWord ++ tailWord_1149188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149188).length < 2 ^ (prefixWord ++ tailWord_1149188).sum := by decide
  have hdescent : baseEnd_1149188 < baseStart_1149188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149194 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1149194 : Nat := 118140960795 + 1149194 * 2 ^ 59
def prefixEnd_1149194 : Nat := 4983230072969 + 3 ^ 40 * 1149194 * 2
def baseEnd_1149194 : Nat := 590088887263082006889959

theorem tailTrace_1149194 : CollatzResearch.WordTrace tailWord_1149194 prefixEnd_1149194 590088887263082006889959 := by
  unfold tailWord_1149194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10478637149668469888679659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27943032399115919703145757 10478637149668469888679659)
  ·
    refine ⟨15717955724502704833019489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10478637149668469888679659 15717955724502704833019489)
    ·
      refine ⟨11788466793377028624764617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15717955724502704833019489 11788466793377028624764617)
      ·
        refine ⟨8841350095032771468573463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11788466793377028624764617 8841350095032771468573463)
        ·
          refine ⟨13262025142549157202860195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8841350095032771468573463 13262025142549157202860195)
          ·
            refine ⟨19893037713823735804290293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13262025142549157202860195 19893037713823735804290293)
            ·
              refine ⟨1864972285670975231652215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19893037713823735804290293 1864972285670975231652215)
              ·
                refine ⟨2797458428506462847478323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864972285670975231652215 2797458428506462847478323)
                ·
                  refine ⟨4196187642759694271217485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2797458428506462847478323 4196187642759694271217485)
                  ·
                    refine ⟨1573570366034885351706557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4196187642759694271217485 1573570366034885351706557)
                    ·
                      refine ⟨590088887263082006889959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1573570366034885351706557 590088887263082006889959)
                      ·
                        rfl

theorem cell23_1149194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1149194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149194 prefixEnd_1149194 := by exact prefixLift 1149194
  have htrace : WordTrace (prefixWord ++ tailWord_1149194) baseStart_1149194 baseEnd_1149194 := by
    simpa [prefixWord, tailWord_1149194, baseEnd_1149194] using wordTrace_append hprefix tailTrace_1149194
  have hstable : (prefixWord ++ tailWord_1149194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149194).length < 2 ^ (prefixWord ++ tailWord_1149194).sum := by decide
  have hdescent : baseEnd_1149194 < baseStart_1149194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149207 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1149207 : Nat := 118140960795 + 1149207 * 2 ^ 59
def prefixEnd_1149207 : Nat := 4983230072969 + 3 ^ 40 * 1149207 * 2
def baseEnd_1149207 : Nat := 590095562511590456027399

theorem tailTrace_1149207 : CollatzResearch.WordTrace tailWord_1149207 prefixEnd_1149207 590095562511590456027399 := by
  unfold tailWord_1149207
  simp only [CollatzResearch.WordTrace]
  refine ⟨41915022747626782774941875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27943348498417855183294583 41915022747626782774941875)
  ·
    refine ⟨62872534121440174162412813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41915022747626782774941875 62872534121440174162412813)
    ·
      refine ⟨23577200295540065310904805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62872534121440174162412813 23577200295540065310904805)
      ·
        refine ⟨4420725055413762245794651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23577200295540065310904805 4420725055413762245794651)
        ·
          refine ⟨6631087583120643368691977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4420725055413762245794651 6631087583120643368691977)
          ·
            refine ⟨4973315687340482526518983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6631087583120643368691977 4973315687340482526518983)
            ·
              refine ⟨7459973531010723789778475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4973315687340482526518983 7459973531010723789778475)
              ·
                refine ⟨11189960296516085684667713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7459973531010723789778475 11189960296516085684667713)
                ·
                  refine ⟨8392470222387064263500785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11189960296516085684667713 8392470222387064263500785)
                  ·
                    refine ⟨6294352666790298197625589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8392470222387064263500785 6294352666790298197625589)
                    ·
                      refine ⟨590095562511590456027399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6294352666790298197625589 590095562511590456027399)
                      ·
                        rfl

theorem cell23_1149207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1149207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149207 prefixEnd_1149207 := by exact prefixLift 1149207
  have htrace : WordTrace (prefixWord ++ tailWord_1149207) baseStart_1149207 baseEnd_1149207 := by
    simpa [prefixWord, tailWord_1149207, baseEnd_1149207] using wordTrace_append hprefix tailTrace_1149207
  have hstable : (prefixWord ++ tailWord_1149207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149207).length < 2 ^ (prefixWord ++ tailWord_1149207).sum := by decide
  have hdescent : baseEnd_1149207 < baseStart_1149207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149229 : List Nat := [1, 5, 3, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_1149229 : Nat := 118140960795 + 1149229 * 2 ^ 59
def prefixEnd_1149229 : Nat := 4983230072969 + 3 ^ 40 * 1149229 * 2
def baseEnd_1149229 : Nat := 590106859085989369952299

theorem tailTrace_1149229 : CollatzResearch.WordTrace tailWord_1149229 prefixEnd_1149229 590106859085989369952299 := by
  unfold tailWord_1149229
  simp only [CollatzResearch.WordTrace]
  refine ⟨41915825153547080532242741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27943883435698053688161827 41915825153547080532242741)
  ·
    refine ⟨3929608608145038799897757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41915825153547080532242741 3929608608145038799897757)
    ·
      refine ⟨1473603228054389549961659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3929608608145038799897757 1473603228054389549961659)
      ·
        refine ⟨2210404842081584324942489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1473603228054389549961659 2210404842081584324942489)
        ·
          refine ⟨1657803631561188243706867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2210404842081584324942489 1657803631561188243706867)
          ·
            refine ⟨2486705447341782365560301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657803631561188243706867 2486705447341782365560301)
            ·
              refine ⟨932514542753168387085113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2486705447341782365560301 932514542753168387085113)
              ·
                refine ⟨699385907064876290313835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 932514542753168387085113 699385907064876290313835)
                ·
                  refine ⟨1049078860597314435470753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699385907064876290313835 1049078860597314435470753)
                  ·
                    refine ⟨786809145447985826603065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1049078860597314435470753 786809145447985826603065)
                    ·
                      refine ⟨590106859085989369952299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 786809145447985826603065 590106859085989369952299)
                      ·
                        rfl

theorem cell23_1149229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_1149229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149229 prefixEnd_1149229 := by exact prefixLift 1149229
  have htrace : WordTrace (prefixWord ++ tailWord_1149229) baseStart_1149229 baseEnd_1149229 := by
    simpa [prefixWord, tailWord_1149229, baseEnd_1149229] using wordTrace_append hprefix tailTrace_1149229
  have hstable : (prefixWord ++ tailWord_1149229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149229).length < 2 ^ (prefixWord ++ tailWord_1149229).sum := by decide
  have hdescent : baseEnd_1149229 < baseStart_1149229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149237 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1149237 : Nat := 118140960795 + 1149237 * 2 ^ 59
def prefixEnd_1149237 : Nat := 4983230072969 + 3 ^ 40 * 1149237 * 2
def baseEnd_1149237 : Nat := 590110966931225338652261

theorem tailTrace_1149237 : CollatzResearch.WordTrace tailWord_1149237 prefixEnd_1149237 590110966931225338652261 := by
  unfold tailWord_1149237
  simp only [CollatzResearch.WordTrace]
  refine ⟨41916116937518097898533965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27944077958345398599022643 41916116937518097898533965)
  ·
    refine ⟨15718543851569286711950237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41916116937518097898533965 15718543851569286711950237)
    ·
      refine ⟨5894453944338482516981339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15718543851569286711950237 5894453944338482516981339)
      ·
        refine ⟨8841680916507723775472009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5894453944338482516981339 8841680916507723775472009)
        ·
          refine ⟨6631260687380792831604007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8841680916507723775472009 6631260687380792831604007)
          ·
            refine ⟨9946891031071189247406011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6631260687380792831604007 9946891031071189247406011)
            ·
              refine ⟨14920336546606783871109017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9946891031071189247406011 14920336546606783871109017)
              ·
                refine ⟨11190252409955087903331763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14920336546606783871109017 11190252409955087903331763)
                ·
                  refine ⟨16785378614932631854997645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11190252409955087903331763 16785378614932631854997645)
                  ·
                    refine ⟨6294516980599736945624117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16785378614932631854997645 6294516980599736945624117)
                    ·
                      refine ⟨590110966931225338652261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6294516980599736945624117 590110966931225338652261)
                      ·
                        rfl

theorem cell23_1149237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1149237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149237 prefixEnd_1149237 := by exact prefixLift 1149237
  have htrace : WordTrace (prefixWord ++ tailWord_1149237) baseStart_1149237 baseEnd_1149237 := by
    simpa [prefixWord, tailWord_1149237, baseEnd_1149237] using wordTrace_append hprefix tailTrace_1149237
  have hstable : (prefixWord ++ tailWord_1149237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149237).length < 2 ^ (prefixWord ++ tailWord_1149237).sum := by decide
  have hdescent : baseEnd_1149237 < baseStart_1149237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149247 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 4]
def baseStart_1149247 : Nat := 118140960795 + 1149247 * 2 ^ 59
def prefixEnd_1149247 : Nat := 4983230072969 + 3 ^ 40 * 1149247 * 2
def baseEnd_1149247 : Nat := 590116101737770299527215

theorem tailTrace_1149247 : CollatzResearch.WordTrace tailWord_1149247 prefixEnd_1149247 590116101737770299527215 := by
  unfold tailWord_1149247
  simp only [CollatzResearch.WordTrace]
  refine ⟨41916481667481869606397995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27944321111654579737598663 41916481667481869606397995)
  ·
    refine ⟨62874722501222804409596993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41916481667481869606397995 62874722501222804409596993)
    ·
      refine ⟨47156041875917103307197745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62874722501222804409596993 47156041875917103307197745)
      ·
        refine ⟨35367031406937827480398309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47156041875917103307197745 35367031406937827480398309)
        ·
          refine ⟨6631318388800842652574683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35367031406937827480398309 6631318388800842652574683)
          ·
            refine ⟨9946977583201263978862025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6631318388800842652574683 9946977583201263978862025)
            ·
              refine ⟨7460233187400947984146519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9946977583201263978862025 7460233187400947984146519)
              ·
                refine ⟨11190349781101421976219779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7460233187400947984146519 11190349781101421976219779)
                ·
                  refine ⟨16785524671652132964329669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11190349781101421976219779 16785524671652132964329669)
                  ·
                    refine ⟨3147285875934774930811813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16785524671652132964329669 3147285875934774930811813)
                    ·
                      refine ⟨590116101737770299527215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3147285875934774930811813 590116101737770299527215)
                      ·
                        rfl

theorem cell23_1149247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_1149247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149247 prefixEnd_1149247 := by exact prefixLift 1149247
  have htrace : WordTrace (prefixWord ++ tailWord_1149247) baseStart_1149247 baseEnd_1149247 := by
    simpa [prefixWord, tailWord_1149247, baseEnd_1149247] using wordTrace_append hprefix tailTrace_1149247
  have hstable : (prefixWord ++ tailWord_1149247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149247).length < 2 ^ (prefixWord ++ tailWord_1149247).sum := by decide
  have hdescent : baseEnd_1149247 < baseStart_1149247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149267 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 3]
def baseStart_1149267 : Nat := 118140960795 + 1149267 * 2 ^ 59
def prefixEnd_1149267 : Nat := 4983230072969 + 3 ^ 40 * 1149267 * 2
def baseEnd_1149267 : Nat := 590126371350860221277123

theorem tailTrace_1149267 : CollatzResearch.WordTrace tailWord_1149267 prefixEnd_1149267 590126371350860221277123 := by
  unfold tailWord_1149267
  simp only [CollatzResearch.WordTrace]
  refine ⟨41917211127409413022126055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27944807418272942014750703 41917211127409413022126055)
  ·
    refine ⟨62875816691114119533189083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41917211127409413022126055 62875816691114119533189083)
    ·
      refine ⟨94313725036671179299783625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62875816691114119533189083 94313725036671179299783625)
      ·
        refine ⟨70735293777503384474837719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94313725036671179299783625 70735293777503384474837719)
        ·
          refine ⟨106102940666255076712256579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70735293777503384474837719 106102940666255076712256579)
          ·
            refine ⟨159154410999382615068384869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106102940666255076712256579 159154410999382615068384869)
            ·
              refine ⟨29841452062384240325322163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159154410999382615068384869 29841452062384240325322163)
              ·
                refine ⟨44762178093576360487983245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29841452062384240325322163 44762178093576360487983245)
                ·
                  refine ⟨16785816785091135182993717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44762178093576360487983245 16785816785091135182993717)
                  ·
                    refine ⟨1573670323602293923405661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16785816785091135182993717 1573670323602293923405661)
                    ·
                      refine ⟨590126371350860221277123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1573670323602293923405661 590126371350860221277123)
                      ·
                        rfl

theorem cell23_1149267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 3].length) (baseStart_1149267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149267 prefixEnd_1149267 := by exact prefixLift 1149267
  have htrace : WordTrace (prefixWord ++ tailWord_1149267) baseStart_1149267 baseEnd_1149267 := by
    simpa [prefixWord, tailWord_1149267, baseEnd_1149267] using wordTrace_append hprefix tailTrace_1149267
  have hstable : (prefixWord ++ tailWord_1149267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149267).length < 2 ^ (prefixWord ++ tailWord_1149267).sum := by decide
  have hdescent : baseEnd_1149267 < baseStart_1149267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149274 : List Nat := [3, 1, 1, 2, 1, 2, 1, 7, 5]
def baseStart_1149274 : Nat := 118140960795 + 1149274 * 2 ^ 59
def prefixEnd_1149274 : Nat := 4983230072969 + 3 ^ 40 * 1149274 * 2
def baseEnd_1149274 : Nat := 65569996190604632654399

theorem tailTrace_1149274 : CollatzResearch.WordTrace tailWord_1149274 prefixEnd_1149274 65569996190604632654399 := by
  unfold tailWord_1149274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10479366609596013304407719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27944977625589368811753917 10479366609596013304407719)
  ·
    refine ⟨15719049914394019956611579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10479366609596013304407719 15719049914394019956611579)
    ·
      refine ⟨23578574871591029934917369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15719049914394019956611579 23578574871591029934917369)
      ·
        refine ⟨17683931153693272451188027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23578574871591029934917369 17683931153693272451188027)
        ·
          refine ⟨26525896730539908676782041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17683931153693272451188027 26525896730539908676782041)
          ·
            refine ⟨19894422547904931507586531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26525896730539908676782041 19894422547904931507586531)
            ·
              refine ⟨29841633821857397261379797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19894422547904931507586531 29841633821857397261379797)
              ·
                refine ⟨699413292699782748313589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29841633821857397261379797 699413292699782748313589)
                ·
                  refine ⟨65569996190604632654399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 699413292699782748313589 65569996190604632654399)
                  ·
                    rfl

theorem cell23_1149274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_1149274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149274 prefixEnd_1149274 := by exact prefixLift 1149274
  have htrace : WordTrace (prefixWord ++ tailWord_1149274) baseStart_1149274 baseEnd_1149274 := by
    simpa [prefixWord, tailWord_1149274, baseEnd_1149274] using wordTrace_append hprefix tailTrace_1149274
  have hstable : (prefixWord ++ tailWord_1149274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149274).length < 2 ^ (prefixWord ++ tailWord_1149274).sum := by decide
  have hdescent : baseEnd_1149274 < baseStart_1149274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149284 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_1149284 : Nat := 118140960795 + 1149284 * 2 ^ 59
def prefixEnd_1149284 : Nat := 4983230072969 + 3 ^ 40 * 1149284 * 2
def baseEnd_1149284 : Nat := 590135100521986654764545

theorem tailTrace_1149284 : CollatzResearch.WordTrace tailWord_1149284 prefixEnd_1149284 590135100521986654764545 := by
  unfold tailWord_1149284
  simp only [CollatzResearch.WordTrace]
  refine ⟨20958915584173912462747453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27945220778898549950329937 20958915584173912462747453)
  ·
    refine ⟨7859593344065217173530295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20958915584173912462747453 7859593344065217173530295)
    ·
      refine ⟨11789390016097825760295443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7859593344065217173530295 11789390016097825760295443)
      ·
        refine ⟨17684085024146738640443165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11789390016097825760295443 17684085024146738640443165)
        ·
          refine ⟨6631531884055026990166187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17684085024146738640443165 6631531884055026990166187)
          ·
            refine ⟨9947297826082540485249281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6631531884055026990166187 9947297826082540485249281)
            ·
              refine ⟨7460473369561905363936961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9947297826082540485249281 7460473369561905363936961)
              ·
                refine ⟨5595355027171429022952721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7460473369561905363936961 5595355027171429022952721)
                ·
                  refine ⟨4196516270378571767214541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5595355027171429022952721 4196516270378571767214541)
                  ·
                    refine ⟨1573693601391964412705453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4196516270378571767214541 1573693601391964412705453)
                    ·
                      refine ⟨590135100521986654764545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1573693601391964412705453 590135100521986654764545)
                      ·
                        rfl

theorem cell23_1149284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_1149284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149284 prefixEnd_1149284 := by exact prefixLift 1149284
  have htrace : WordTrace (prefixWord ++ tailWord_1149284) baseStart_1149284 baseEnd_1149284 := by
    simpa [prefixWord, tailWord_1149284, baseEnd_1149284] using wordTrace_append hprefix tailTrace_1149284
  have hstable : (prefixWord ++ tailWord_1149284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149284).length < 2 ^ (prefixWord ++ tailWord_1149284).sum := by decide
  have hdescent : baseEnd_1149284 < baseStart_1149284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149301 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1149301 : Nat := 118140960795 + 1149301 * 2 ^ 59
def prefixEnd_1149301 : Nat := 4983230072969 + 3 ^ 40 * 1149301 * 2
def baseEnd_1149301 : Nat := 590143829693113088251967

theorem tailTrace_1149301 : CollatzResearch.WordTrace tailWord_1149301 prefixEnd_1149301 590143829693113088251967 := by
  unfold tailWord_1149301
  simp only [CollatzResearch.WordTrace]
  refine ⟨41918451209286236828863757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27945634139524157885909171 41918451209286236828863757)
  ·
    refine ⟨15719419203482338810823909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41918451209286236828863757 15719419203482338810823909)
    ·
      refine ⟨2947391100652938527029483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15719419203482338810823909 2947391100652938527029483)
      ·
        refine ⟨4421086650979407790544225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2947391100652938527029483 4421086650979407790544225)
        ·
          refine ⟨3315814988234555842908169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4421086650979407790544225 3315814988234555842908169)
          ·
            refine ⟨2486861241175916882181127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3315814988234555842908169 2486861241175916882181127)
            ·
              refine ⟨3730291861763875323271691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486861241175916882181127 3730291861763875323271691)
              ·
                refine ⟨5595437792645812984907537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3730291861763875323271691 5595437792645812984907537)
                ·
                  refine ⟨4196578344484359738680653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5595437792645812984907537 4196578344484359738680653)
                  ·
                    refine ⟨1573716879181634902005245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4196578344484359738680653 1573716879181634902005245)
                    ·
                      refine ⟨590143829693113088251967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1573716879181634902005245 590143829693113088251967)
                      ·
                        rfl

theorem cell23_1149301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1149301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149301 prefixEnd_1149301 := by exact prefixLift 1149301
  have htrace : WordTrace (prefixWord ++ tailWord_1149301) baseStart_1149301 baseEnd_1149301 := by
    simpa [prefixWord, tailWord_1149301, baseEnd_1149301] using wordTrace_append hprefix tailTrace_1149301
  have hstable : (prefixWord ++ tailWord_1149301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149301).length < 2 ^ (prefixWord ++ tailWord_1149301).sum := by decide
  have hdescent : baseEnd_1149301 < baseStart_1149301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149321 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 2, 5]
def baseStart_1149321 : Nat := 118140960795 + 1149321 * 2 ^ 59
def prefixEnd_1149321 : Nat := 4983230072969 + 3 ^ 40 * 1149321 * 2
def baseEnd_1149321 : Nat := 196718033102067670000625

theorem tailTrace_1149321 : CollatzResearch.WordTrace tailWord_1149321 prefixEnd_1149321 196718033102067670000625 := by
  unfold tailWord_1149321
  simp only [CollatzResearch.WordTrace]
  refine ⟨41919180669213780244591817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27946120446142520163061211 41919180669213780244591817)
  ·
    refine ⟨31439385501910335183443863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41919180669213780244591817 31439385501910335183443863)
    ·
      refine ⟨47159078252865502775165795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31439385501910335183443863 47159078252865502775165795)
      ·
        refine ⟨70738617379298254162748693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47159078252865502775165795 70738617379298254162748693)
        ·
          refine ⟨3315872689654605663878845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70738617379298254162748693 3315872689654605663878845)
          ·
            refine ⟨1243452258620477123954567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3315872689654605663878845 1243452258620477123954567)
            ·
              refine ⟨1865178387930715685931851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243452258620477123954567 1865178387930715685931851)
              ·
                refine ⟨2797767581896073528897777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865178387930715685931851 2797767581896073528897777)
                ·
                  refine ⟨2098325686422055146673333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2797767581896073528897777 2098325686422055146673333)
                  ·
                    refine ⟨196718033102067670000625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2098325686422055146673333 196718033102067670000625)
                    ·
                      rfl

theorem cell23_1149321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 5].length) (baseStart_1149321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149321 prefixEnd_1149321 := by exact prefixLift 1149321
  have htrace : WordTrace (prefixWord ++ tailWord_1149321) baseStart_1149321 baseEnd_1149321 := by
    simpa [prefixWord, tailWord_1149321, baseEnd_1149321] using wordTrace_append hprefix tailTrace_1149321
  have hstable : (prefixWord ++ tailWord_1149321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149321).length < 2 ^ (prefixWord ++ tailWord_1149321).sum := by decide
  have hdescent : baseEnd_1149321 < baseStart_1149321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149324 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_1149324 : Nat := 118140960795 + 1149324 * 2 ^ 59
def prefixEnd_1149324 : Nat := 4983230072969 + 3 ^ 40 * 1149324 * 2
def baseEnd_1149324 : Nat := 590155639748166498264361

theorem tailTrace_1149324 : CollatzResearch.WordTrace tailWord_1149324 prefixEnd_1149324 590155639748166498264361 := by
  unfold tailWord_1149324
  simp only [CollatzResearch.WordTrace]
  refine ⟨20959645044101455878475513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27946193392135274504634017 20959645044101455878475513)
  ·
    refine ⟨15719733783076091908856635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20959645044101455878475513 15719733783076091908856635)
    ·
      refine ⟨23579600674614137863284953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15719733783076091908856635 23579600674614137863284953)
      ·
        refine ⟨17684700505960603397463715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23579600674614137863284953 17684700505960603397463715)
        ·
          refine ⟨26527050758940905096195573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17684700505960603397463715 26527050758940905096195573)
          ·
            refine ⟨2486911008650709852768335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26527050758940905096195573 2486911008650709852768335)
            ·
              refine ⟨3730366512976064779152503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486911008650709852768335 3730366512976064779152503)
              ·
                refine ⟨5595549769464097168728755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3730366512976064779152503 5595549769464097168728755)
                ·
                  refine ⟨8393324654196145753093133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5595549769464097168728755 8393324654196145753093133)
                  ·
                    refine ⟨3147496745323554657409925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8393324654196145753093133 3147496745323554657409925)
                    ·
                      refine ⟨590155639748166498264361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3147496745323554657409925 590155639748166498264361)
                      ·
                        rfl

theorem cell23_1149324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_1149324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149324 prefixEnd_1149324 := by exact prefixLift 1149324
  have htrace : WordTrace (prefixWord ++ tailWord_1149324) baseStart_1149324 baseEnd_1149324 := by
    simpa [prefixWord, tailWord_1149324, baseEnd_1149324] using wordTrace_append hprefix tailTrace_1149324
  have hstable : (prefixWord ++ tailWord_1149324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149324).length < 2 ^ (prefixWord ++ tailWord_1149324).sum := by decide
  have hdescent : baseEnd_1149324 < baseStart_1149324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149337 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_1149337 : Nat := 118140960795 + 1149337 * 2 ^ 59
def prefixEnd_1149337 : Nat := 4983230072969 + 3 ^ 40 * 1149337 * 2
def baseEnd_1149337 : Nat := 590162314996674947401801

theorem tailTrace_1149337 : CollatzResearch.WordTrace tailWord_1149337 prefixEnd_1149337 590162314996674947401801 := by
  unfold tailWord_1149337
  simp only [CollatzResearch.WordTrace]
  refine ⟨41919764237155814977174265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27946509491437209984782843 41919764237155814977174265)
  ·
    refine ⟨31439823177866861232880699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41919764237155814977174265 31439823177866861232880699)
    ·
      refine ⟨47159734766800291849321049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31439823177866861232880699 47159734766800291849321049)
      ·
        refine ⟨35369801075100218886990787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47159734766800291849321049 35369801075100218886990787)
        ·
          refine ⟨53054701612650328330486181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35369801075100218886990787 53054701612650328330486181)
          ·
            refine ⟨9947756552371936561966159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53054701612650328330486181 9947756552371936561966159)
            ·
              refine ⟨14921634828557904842949239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9947756552371936561966159 14921634828557904842949239)
              ·
                refine ⟨22382452242836857264423859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14921634828557904842949239 22382452242836857264423859)
                ·
                  refine ⟨33573678364255285896635789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22382452242836857264423859 33573678364255285896635789)
                  ·
                    refine ⟨12590129386595732211238421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33573678364255285896635789 12590129386595732211238421)
                    ·
                      refine ⟨590162314996674947401801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12590129386595732211238421 590162314996674947401801)
                      ·
                        rfl

theorem cell23_1149337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_1149337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149337 prefixEnd_1149337 := by exact prefixLift 1149337
  have htrace : WordTrace (prefixWord ++ tailWord_1149337) baseStart_1149337 baseEnd_1149337 := by
    simpa [prefixWord, tailWord_1149337, baseEnd_1149337] using wordTrace_append hprefix tailTrace_1149337
  have hstable : (prefixWord ++ tailWord_1149337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149337).length < 2 ^ (prefixWord ++ tailWord_1149337).sum := by decide
  have hdescent : baseEnd_1149337 < baseStart_1149337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149351 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 3, 4]
def baseStart_1149351 : Nat := 118140960795 + 1149351 * 2 ^ 59
def prefixEnd_1149351 : Nat := 4983230072969 + 3 ^ 40 * 1149351 * 2
def baseEnd_1149351 : Nat := 196723167908612630875579

theorem tailTrace_1149351 : CollatzResearch.WordTrace tailWord_1149351 prefixEnd_1149351 196723167908612630875579 := by
  unfold tailWord_1149351
  simp only [CollatzResearch.WordTrace]
  refine ⟨41920274859105095368183907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27946849906070063578789271 41920274859105095368183907)
  ·
    refine ⟨62880412288657643052275861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41920274859105095368183907 62880412288657643052275861)
    ·
      refine ⟨2947519326030827018075431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62880412288657643052275861 2947519326030827018075431)
      ·
        refine ⟨4421278989046240527113147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2947519326030827018075431 4421278989046240527113147)
        ·
          refine ⟨6631918483569360790669721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4421278989046240527113147 6631918483569360790669721)
          ·
            refine ⟨4973938862677020593002291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6631918483569360790669721 4973938862677020593002291)
            ·
              refine ⟨7460908294015530889503437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4973938862677020593002291 7460908294015530889503437)
              ·
                refine ⟨2797840610255824083563789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7460908294015530889503437 2797840610255824083563789)
                ·
                  refine ⟨1049190228845934031336421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2797840610255824083563789 1049190228845934031336421)
                  ·
                    refine ⟨196723167908612630875579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1049190228845934031336421 196723167908612630875579)
                    ·
                      rfl

theorem cell23_1149351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_1149351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149351 prefixEnd_1149351 := by exact prefixLift 1149351
  have htrace : WordTrace (prefixWord ++ tailWord_1149351) baseStart_1149351 baseEnd_1149351 := by
    simpa [prefixWord, tailWord_1149351, baseEnd_1149351] using wordTrace_append hprefix tailTrace_1149351
  have hstable : (prefixWord ++ tailWord_1149351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149351).length < 2 ^ (prefixWord ++ tailWord_1149351).sum := by decide
  have hdescent : baseEnd_1149351 < baseStart_1149351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149424 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 1, 6]
def baseStart_1149424 : Nat := 118140960795 + 1149424 * 2 ^ 59
def prefixEnd_1149424 : Nat := 4983230072969 + 3 ^ 40 * 1149424 * 2
def baseEnd_1149424 : Nat := 196735662604538702337967

theorem tailTrace_1149424 : CollatzResearch.WordTrace tailWord_1149424 prefixEnd_1149424 196735662604538702337967 := by
  unfold tailWord_1149424
  simp only [CollatzResearch.WordTrace]
  refine ⟨20961468693920314417795663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27948624925227085890394217 20961468693920314417795663)
  ·
    refine ⟨31442203040880471626693495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20961468693920314417795663 31442203040880471626693495)
    ·
      refine ⟨47163304561320707440040243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31442203040880471626693495 47163304561320707440040243)
      ·
        refine ⟨70744956841981061160060365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47163304561320707440040243 70744956841981061160060365)
        ·
          refine ⟨26529358815742897935022637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70744956841981061160060365 26529358815742897935022637)
          ·
            refine ⟨9948509555903586725633489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26529358815742897935022637 9948509555903586725633489)
            ·
              refine ⟨7461382166927690044225117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9948509555903586725633489 7461382166927690044225117)
              ·
                refine ⟨2798018312597883766584419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7461382166927690044225117 2798018312597883766584419)
                ·
                  refine ⟨4197027468896825649876629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798018312597883766584419 4197027468896825649876629)
                  ·
                    refine ⟨196735662604538702337967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4197027468896825649876629 196735662604538702337967)
                    ·
                      rfl

theorem cell23_1149424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_1149424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149424 prefixEnd_1149424 := by exact prefixLift 1149424
  have htrace : WordTrace (prefixWord ++ tailWord_1149424) baseStart_1149424 baseEnd_1149424 := by
    simpa [prefixWord, tailWord_1149424, baseEnd_1149424] using wordTrace_append hprefix tailTrace_1149424
  have hstable : (prefixWord ++ tailWord_1149424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149424).length < 2 ^ (prefixWord ++ tailWord_1149424).sum := by decide
  have hdescent : baseEnd_1149424 < baseStart_1149424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149441 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1149441 : Nat := 118140960795 + 1149441 * 2 ^ 59
def prefixEnd_1149441 : Nat := 4983230072969 + 3 ^ 40 * 1149441 * 2
def baseEnd_1149441 : Nat := 196738572328247513500441

theorem tailTrace_1149441 : CollatzResearch.WordTrace tailWord_1149441 prefixEnd_1149441 196738572328247513500441 := by
  unfold tailWord_1149441
  simp only [CollatzResearch.WordTrace]
  refine ⟨41923557428779040738960177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27949038285852693825973451 41923557428779040738960177)
  ·
    refine ⟨31442668071584280554220133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41923557428779040738960177 31442668071584280554220133)
    ·
      refine ⟨5895500263422052603916275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31442668071584280554220133 5895500263422052603916275)
      ·
        refine ⟨8843250395133078905874413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5895500263422052603916275 8843250395133078905874413)
        ·
          refine ⟨3316218898174904589702905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8843250395133078905874413 3316218898174904589702905)
          ·
            refine ⟨2487164173631178442277179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3316218898174904589702905 2487164173631178442277179)
            ·
              refine ⟨3730746260446767663415769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2487164173631178442277179 3730746260446767663415769)
              ·
                refine ⟨2798059695335075747561827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3730746260446767663415769 2798059695335075747561827)
                ·
                  refine ⟨4197089543002613621342741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798059695335075747561827 4197089543002613621342741)
                  ·
                    refine ⟨196738572328247513500441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4197089543002613621342741 196738572328247513500441)
                    ·
                      rfl

theorem cell23_1149441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1149441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149441 prefixEnd_1149441 := by exact prefixLift 1149441
  have htrace : WordTrace (prefixWord ++ tailWord_1149441) baseStart_1149441 baseEnd_1149441 := by
    simpa [prefixWord, tailWord_1149441, baseEnd_1149441] using wordTrace_append hprefix tailTrace_1149441
  have hstable : (prefixWord ++ tailWord_1149441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149441).length < 2 ^ (prefixWord ++ tailWord_1149441).sum := by decide
  have hdescent : baseEnd_1149441 < baseStart_1149441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149451 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 5]
def baseStart_1149451 : Nat := 118140960795 + 1149451 * 2 ^ 59
def prefixEnd_1149451 : Nat := 4983230072969 + 3 ^ 40 * 1149451 * 2
def baseEnd_1149451 : Nat := 590220851791287501376277

theorem tailTrace_1149451 : CollatzResearch.WordTrace tailWord_1149451 prefixEnd_1149451 590220851791287501376277 := by
  unfold tailWord_1149451
  simp only [CollatzResearch.WordTrace]
  refine ⟨41923922158742812446824207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27949281439161874964549471 41923922158742812446824207)
  ·
    refine ⟨62885883238114218670236311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41923922158742812446824207 62885883238114218670236311)
    ·
      refine ⟨94328824857171328005354467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62885883238114218670236311 94328824857171328005354467)
      ·
        refine ⟨141493237285756992008031701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94328824857171328005354467 141493237285756992008031701)
        ·
          refine ⟨3316247748884929500188243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 141493237285756992008031701 3316247748884929500188243)
          ·
            refine ⟨4974371623327394250282365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316247748884929500188243 4974371623327394250282365)
            ·
              refine ⟨1865389358747772843855887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4974371623327394250282365 1865389358747772843855887)
              ·
                refine ⟨2798084038121659265783831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865389358747772843855887 2798084038121659265783831)
                ·
                  refine ⟨4197126057182488898675747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798084038121659265783831 4197126057182488898675747)
                  ·
                    refine ⟨6295689085773733348013621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4197126057182488898675747 6295689085773733348013621)
                    ·
                      refine ⟨590220851791287501376277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6295689085773733348013621 590220851791287501376277)
                      ·
                        rfl

theorem cell23_1149451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 5].length) (baseStart_1149451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149451 prefixEnd_1149451 := by exact prefixLift 1149451
  have htrace : WordTrace (prefixWord ++ tailWord_1149451) baseStart_1149451 baseEnd_1149451 := by
    simpa [prefixWord, tailWord_1149451, baseEnd_1149451] using wordTrace_append hprefix tailTrace_1149451
  have hstable : (prefixWord ++ tailWord_1149451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149451).length < 2 ^ (prefixWord ++ tailWord_1149451).sum := by decide
  have hdescent : baseEnd_1149451 < baseStart_1149451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149454 : List Nat := [4, 1, 1, 2, 3, 12]
def baseStart_1149454 : Nat := 118140960795 + 1149454 * 2 ^ 59
def prefixEnd_1149454 : Nat := 4983230072969 + 3 ^ 40 * 1149454 * 2
def baseEnd_1149454 : Nat := 2428898733470168681641

theorem tailTrace_1149454 : CollatzResearch.WordTrace tailWord_1149454 prefixEnd_1149454 2428898733470168681641 := by
  unfold tailWord_1149454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5240503947216492994897927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27949354385154629306122277 5240503947216492994897927)
  ·
    refine ⟨7860755920824739492346891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5240503947216492994897927 7860755920824739492346891)
    ·
      refine ⟨11791133881237109238520337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7860755920824739492346891 11791133881237109238520337)
      ·
        refine ⟨8843350410927831928890253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11791133881237109238520337 8843350410927831928890253)
        ·
          refine ⟨3316256404097936973333845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8843350410927831928890253 3316256404097936973333845)
          ·
            refine ⟨2428898733470168681641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3316256404097936973333845 2428898733470168681641)
            ·
              rfl

theorem cell23_1149454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 12].length) (baseStart_1149454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149454 prefixEnd_1149454 := by exact prefixLift 1149454
  have htrace : WordTrace (prefixWord ++ tailWord_1149454) baseStart_1149454 baseEnd_1149454 := by
    simpa [prefixWord, tailWord_1149454, baseEnd_1149454] using wordTrace_append hprefix tailTrace_1149454
  have hstable : (prefixWord ++ tailWord_1149454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149454).length < 2 ^ (prefixWord ++ tailWord_1149454).sum := by decide
  have hdescent : baseEnd_1149454 < baseStart_1149454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149465 : List Nat := [1, 2, 1, 2, 1, 1, 2, 8, 1, 2, 2]
def baseStart_1149465 : Nat := 118140960795 + 1149465 * 2 ^ 59
def prefixEnd_1149465 : Nat := 4983230072969 + 3 ^ 40 * 1149465 * 2
def baseEnd_1149465 : Nat := 590228040520450446601213

theorem tailTrace_1149465 : CollatzResearch.WordTrace tailWord_1149465 prefixEnd_1149465 590228040520450446601213 := by
  unfold tailWord_1149465
  simp only [CollatzResearch.WordTrace]
  refine ⟨41924432780692092837833849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27949621853794728558555899 41924432780692092837833849)
  ·
    refine ⟨31443324585519069628375387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41924432780692092837833849 31443324585519069628375387)
    ·
      refine ⟨47164986878278604442563081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31443324585519069628375387 47164986878278604442563081)
      ·
        refine ⟨35373740158708953331922311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47164986878278604442563081 35373740158708953331922311)
        ·
          refine ⟨53060610238063429997883467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35373740158708953331922311 53060610238063429997883467)
          ·
            refine ⟨79590915357095144996825201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53060610238063429997883467 79590915357095144996825201)
            ·
              refine ⟨59693186517821358747618901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79590915357095144996825201 59693186517821358747618901)
              ·
                refine ⟨699529529505719047823659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 59693186517821358747618901 699529529505719047823659)
                ·
                  refine ⟨1049294294258578571735489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699529529505719047823659 1049294294258578571735489)
                  ·
                    refine ⟨786970720693933928801617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1049294294258578571735489 786970720693933928801617)
                    ·
                      refine ⟨590228040520450446601213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 786970720693933928801617 590228040520450446601213)
                      ·
                        rfl

theorem cell23_1149465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 1, 2, 2].length) (baseStart_1149465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149465 prefixEnd_1149465 := by exact prefixLift 1149465
  have htrace : WordTrace (prefixWord ++ tailWord_1149465) baseStart_1149465 baseEnd_1149465 := by
    simpa [prefixWord, tailWord_1149465, baseEnd_1149465] using wordTrace_append hprefix tailTrace_1149465
  have hstable : (prefixWord ++ tailWord_1149465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149465).length < 2 ^ (prefixWord ++ tailWord_1149465).sum := by decide
  have hdescent : baseEnd_1149465 < baseStart_1149465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149502 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1149502 : Nat := 118140960795 + 1149502 * 2 ^ 59
def prefixEnd_1149502 : Nat := 4983230072969 + 3 ^ 40 * 1149502 * 2
def baseEnd_1149502 : Nat := 590247039304666801838543

theorem tailTrace_1149502 : CollatzResearch.WordTrace tailWord_1149502 prefixEnd_1149502 590247039304666801838543 := by
  unfold tailWord_1149502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5240722785194756019616345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27950521521038698771287173 5240722785194756019616345)
  ·
    refine ⟨3930542088896067014712259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5240722785194756019616345 3930542088896067014712259)
    ·
      refine ⟨5895813133344100522068389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3930542088896067014712259 5895813133344100522068389)
      ·
        refine ⟨1105464962502018847887823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5895813133344100522068389 1105464962502018847887823)
        ·
          refine ⟨1658197443753028271831735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105464962502018847887823 1658197443753028271831735)
          ·
            refine ⟨2487296165629542407747603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1658197443753028271831735 2487296165629542407747603)
            ·
              refine ⟨3730944248444313611621405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2487296165629542407747603 3730944248444313611621405)
              ·
                refine ⟨1399104093166617604358027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3730944248444313611621405 1399104093166617604358027)
                ·
                  refine ⟨2098656139749926406537041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399104093166617604358027 2098656139749926406537041)
                  ·
                    refine ⟨1573992104812444804902781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2098656139749926406537041 1573992104812444804902781)
                    ·
                      refine ⟨590247039304666801838543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1573992104812444804902781 590247039304666801838543)
                      ·
                        rfl

theorem cell23_1149502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1149502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149502 prefixEnd_1149502 := by exact prefixLift 1149502
  have htrace : WordTrace (prefixWord ++ tailWord_1149502) baseStart_1149502 baseEnd_1149502 := by
    simpa [prefixWord, tailWord_1149502, baseEnd_1149502] using wordTrace_append hprefix tailTrace_1149502
  have hstable : (prefixWord ++ tailWord_1149502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149502).length < 2 ^ (prefixWord ++ tailWord_1149502).sum := by decide
  have hdescent : baseEnd_1149502 < baseStart_1149502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149532 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_1149532 : Nat := 118140960795 + 1149532 * 2 ^ 59
def prefixEnd_1149532 : Nat := 4983230072969 + 3 ^ 40 * 1149532 * 2
def baseEnd_1149532 : Nat := 590262443724301684463405

theorem tailTrace_1149532 : CollatzResearch.WordTrace tailWord_1149532 prefixEnd_1149532 590262443724301684463405 := by
  unfold tailWord_1149532
  simp only [CollatzResearch.WordTrace]
  refine ⟨20963438235724681640261425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27951250980966242187015233 20963438235724681640261425)
  ·
    refine ⟨15722578676793511230196069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20963438235724681640261425 15722578676793511230196069)
    ·
      refine ⟨2947983501898783355661763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15722578676793511230196069 2947983501898783355661763)
      ·
        refine ⟨4421975252848175033492645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2947983501898783355661763 4421975252848175033492645)
        ·
          refine ⟨829120359909032818779871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4421975252848175033492645 829120359909032818779871)
          ·
            refine ⟨1243680539863549228169807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829120359909032818779871 1243680539863549228169807)
            ·
              refine ⟨1865520809795323842254711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243680539863549228169807 1865520809795323842254711)
              ·
                refine ⟨2798281214692985763382067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865520809795323842254711 2798281214692985763382067)
                ·
                  refine ⟨4197421822039478645073101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798281214692985763382067 4197421822039478645073101)
                  ·
                    refine ⟨1574033183264804491902413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4197421822039478645073101 1574033183264804491902413)
                    ·
                      refine ⟨590262443724301684463405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1574033183264804491902413 590262443724301684463405)
                      ·
                        rfl

theorem cell23_1149532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_1149532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149532 prefixEnd_1149532 := by exact prefixLift 1149532
  have htrace : WordTrace (prefixWord ++ tailWord_1149532) baseStart_1149532 baseEnd_1149532 := by
    simpa [prefixWord, tailWord_1149532, baseEnd_1149532] using wordTrace_append hprefix tailTrace_1149532
  have hstable : (prefixWord ++ tailWord_1149532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149532).length < 2 ^ (prefixWord ++ tailWord_1149532).sum := by decide
  have hdescent : baseEnd_1149532 < baseStart_1149532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149571 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 3]
def baseStart_1149571 : Nat := 118140960795 + 1149571 * 2 ^ 59
def prefixEnd_1149571 : Nat := 4983230072969 + 3 ^ 40 * 1149571 * 2
def baseEnd_1149571 : Nat := 590282469469827031875725

theorem tailTrace_1149571 : CollatzResearch.WordTrace tailWord_1149571 prefixEnd_1149571 590282469469827031875725 := by
  unfold tailWord_1149571
  simp only [CollatzResearch.WordTrace]
  refine ⟨41928298918308072941192567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27952199278872048627461711 41928298918308072941192567)
  ·
    refine ⟨62892448377462109411788851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41928298918308072941192567 62892448377462109411788851)
    ·
      refine ⟨94338672566193164117683277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62892448377462109411788851 94338672566193164117683277)
      ·
        refine ⟨35377002212322436544131229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94338672566193164117683277 35377002212322436544131229)
        ·
          refine ⟨13266375829620913704049211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35377002212322436544131229 13266375829620913704049211)
          ·
            refine ⟨19899563744431370556073817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13266375829620913704049211 19899563744431370556073817)
            ·
              refine ⟨14924672808323527917055363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19899563744431370556073817 14924672808323527917055363)
              ·
                refine ⟨22387009212485291875583045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14924672808323527917055363 22387009212485291875583045)
                ·
                  refine ⟨4197564227340992226671821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22387009212485291875583045 4197564227340992226671821)
                  ·
                    refine ⟨1574086585252872085001933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4197564227340992226671821 1574086585252872085001933)
                    ·
                      refine ⟨590282469469827031875725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1574086585252872085001933 590282469469827031875725)
                      ·
                        rfl

theorem cell23_1149571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_1149571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149571 prefixEnd_1149571 := by exact prefixLift 1149571
  have htrace : WordTrace (prefixWord ++ tailWord_1149571) baseStart_1149571 baseEnd_1149571 := by
    simpa [prefixWord, tailWord_1149571, baseEnd_1149571] using wordTrace_append hprefix tailTrace_1149571
  have hstable : (prefixWord ++ tailWord_1149571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149571).length < 2 ^ (prefixWord ++ tailWord_1149571).sum := by decide
  have hdescent : baseEnd_1149571 < baseStart_1149571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149591 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 4, 5]
def baseStart_1149591 : Nat := 118140960795 + 1149591 * 2 ^ 59
def prefixEnd_1149591 : Nat := 4983230072969 + 3 ^ 40 * 1149591 * 2
def baseEnd_1149591 : Nat := 196764246360972317875211

theorem tailTrace_1149591 : CollatzResearch.WordTrace tailWord_1149591 prefixEnd_1149591 196764246360972317875211 := by
  unfold tailWord_1149591
  simp only [CollatzResearch.WordTrace]
  refine ⟨41929028378235616356920627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27952685585490410904613751 41929028378235616356920627)
  ·
    refine ⟨62893542567353424535380941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41929028378235616356920627 62893542567353424535380941)
    ·
      refine ⟨23585078462757534200767853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62893542567353424535380941 23585078462757534200767853)
      ·
        refine ⟨8844404423534075325287945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23585078462757534200767853 8844404423534075325287945)
        ·
          refine ⟨6633303317650556493965959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8844404423534075325287945 6633303317650556493965959)
          ·
            refine ⟨9949954976475834740948939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6633303317650556493965959 9949954976475834740948939)
            ·
              refine ⟨14924932464713752111423409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9949954976475834740948939 14924932464713752111423409)
              ·
                refine ⟨11193699348535314083567557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14924932464713752111423409 11193699348535314083567557)
                ·
                  refine ⟨2098818627850371390668917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11193699348535314083567557 2098818627850371390668917)
                  ·
                    refine ⟨196764246360972317875211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2098818627850371390668917 196764246360972317875211)
                    ·
                      rfl

theorem cell23_1149591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_1149591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149591 prefixEnd_1149591 := by exact prefixLift 1149591
  have htrace : WordTrace (prefixWord ++ tailWord_1149591) baseStart_1149591 baseEnd_1149591 := by
    simpa [prefixWord, tailWord_1149591, baseEnd_1149591] using wordTrace_append hprefix tailTrace_1149591
  have hstable : (prefixWord ++ tailWord_1149591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149591).length < 2 ^ (prefixWord ++ tailWord_1149591).sum := by decide
  have hdescent : baseEnd_1149591 < baseStart_1149591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149628 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_1149628 : Nat := 118140960795 + 1149628 * 2 ^ 59
def prefixEnd_1149628 : Nat := 4983230072969 + 3 ^ 40 * 1149628 * 2
def baseEnd_1149628 : Nat := 590311737867133308862963

theorem tailTrace_1149628 : CollatzResearch.WordTrace tailWord_1149628 prefixEnd_1149628 590311737867133308862963 := by
  unfold tailWord_1149628
  simp only [CollatzResearch.WordTrace]
  refine ⟨20965188939550785838008769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27953585252734381117345025 20965188939550785838008769)
  ·
    refine ⟨15723891704663089378506577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20965188939550785838008769 15723891704663089378506577)
    ·
      refine ⟨11792918778497317033879933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15723891704663089378506577 11792918778497317033879933)
      ·
        refine ⟨4422344541936493887704975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11792918778497317033879933 4422344541936493887704975)
        ·
          refine ⟨6633516812904740831557463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4422344541936493887704975 6633516812904740831557463)
          ·
            refine ⟨9950275219357111247336195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6633516812904740831557463 9950275219357111247336195)
            ·
              refine ⟨14925412829035666871004293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9950275219357111247336195 14925412829035666871004293)
              ·
                refine ⟨2798514905444187538313305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14925412829035666871004293 2798514905444187538313305)
                ·
                  refine ⟨2098886179083140653734979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2798514905444187538313305 2098886179083140653734979)
                  ·
                    refine ⟨3148329268624710980602469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2098886179083140653734979 3148329268624710980602469)
                    ·
                      refine ⟨590311737867133308862963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3148329268624710980602469 590311737867133308862963)
                      ·
                        rfl

theorem cell23_1149628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_1149628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149628 prefixEnd_1149628 := by exact prefixLift 1149628
  have htrace : WordTrace (prefixWord ++ tailWord_1149628) baseStart_1149628 baseEnd_1149628 := by
    simpa [prefixWord, tailWord_1149628, baseEnd_1149628] using wordTrace_append hprefix tailTrace_1149628
  have hstable : (prefixWord ++ tailWord_1149628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149628).length < 2 ^ (prefixWord ++ tailWord_1149628).sum := by decide
  have hdescent : baseEnd_1149628 < baseStart_1149628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149665 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_1149665 : Nat := 118140960795 + 1149665 * 2 ^ 59
def prefixEnd_1149665 : Nat := 4983230072969 + 3 ^ 40 * 1149665 * 2
def baseEnd_1149665 : Nat := 590330736651349664100293

theorem tailTrace_1149665 : CollatzResearch.WordTrace tailWord_1149665 prefixEnd_1149665 590330736651349664100293 := by
  unfold tailWord_1149665
  simp only [CollatzResearch.WordTrace]
  refine ⟨41931727379967526995114449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27954484919978351330076299 41931727379967526995114449)
  ·
    refine ⟨31448795534975645246335837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41931727379967526995114449 31448795534975645246335837)
    ·
      refine ⟨11793298325615866967375939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31448795534975645246335837 11793298325615866967375939)
      ·
        refine ⟨17689947488423800451063909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11793298325615866967375939 17689947488423800451063909)
        ·
          refine ⟨3316865154079462584574483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17689947488423800451063909 3316865154079462584574483)
          ·
            refine ⟨4975297731119193876861725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316865154079462584574483 4975297731119193876861725)
            ·
              refine ⟨1865736649169697703823147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4975297731119193876861725 1865736649169697703823147)
              ·
                refine ⟨2798604973754546555734721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865736649169697703823147 2798604973754546555734721)
                ·
                  refine ⟨2098953730315909916801041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2798604973754546555734721 2098953730315909916801041)
                  ·
                    refine ⟨1574215297736932437600781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2098953730315909916801041 1574215297736932437600781)
                    ·
                      refine ⟨590330736651349664100293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1574215297736932437600781 590330736651349664100293)
                      ·
                        rfl

theorem cell23_1149665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_1149665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149665 prefixEnd_1149665 := by exact prefixLift 1149665
  have htrace : WordTrace (prefixWord ++ tailWord_1149665) baseStart_1149665 baseEnd_1149665 := by
    simpa [prefixWord, tailWord_1149665, baseEnd_1149665] using wordTrace_append hprefix tailTrace_1149665
  have hstable : (prefixWord ++ tailWord_1149665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149665).length < 2 ^ (prefixWord ++ tailWord_1149665).sum := by decide
  have hdescent : baseEnd_1149665 < baseStart_1149665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149745 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 2, 4]
def baseStart_1149745 : Nat := 118140960795 + 1149745 * 2 ^ 59
def prefixEnd_1149745 : Nat := 4983230072969 + 3 ^ 40 * 1149745 * 2
def baseEnd_1149745 : Nat := 196790605034569783699975

theorem tailTrace_1149745 : CollatzResearch.WordTrace tailWord_1149745 prefixEnd_1149745 196790605034569783699975 := by
  unfold tailWord_1149745
  simp only [CollatzResearch.WordTrace]
  refine ⟨41934645219677700658026689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27956430146451800438684459 41934645219677700658026689)
  ·
    refine ⟨31450983914758275493520017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41934645219677700658026689 31450983914758275493520017)
    ·
      refine ⟨23588237936068706620140013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31450983914758275493520017 23588237936068706620140013)
      ·
        refine ⟨8845589226025764982552505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23588237936068706620140013 8845589226025764982552505)
        ·
          refine ⟨6634191919519323736914379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8845589226025764982552505 6634191919519323736914379)
          ·
            refine ⟨9951287879278985605371569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6634191919519323736914379 9951287879278985605371569)
            ·
              refine ⟨7463465909459239204028677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9951287879278985605371569 7463465909459239204028677)
              ·
                refine ⟨1399399858023607350755377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7463465909459239204028677 1399399858023607350755377)
                ·
                  refine ⟨1049549893517705513066533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1399399858023607350755377 1049549893517705513066533)
                  ·
                    refine ⟨196790605034569783699975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1049549893517705513066533 196790605034569783699975)
                    ·
                      rfl

theorem cell23_1149745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_1149745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149745 prefixEnd_1149745 := by exact prefixLift 1149745
  have htrace : WordTrace (prefixWord ++ tailWord_1149745) baseStart_1149745 baseEnd_1149745 := by
    simpa [prefixWord, tailWord_1149745, baseEnd_1149745] using wordTrace_append hprefix tailTrace_1149745
  have hstable : (prefixWord ++ tailWord_1149745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149745).length < 2 ^ (prefixWord ++ tailWord_1149745).sum := by decide
  have hdescent : baseEnd_1149745 < baseStart_1149745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149766 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1149766 : Nat := 118140960795 + 1149766 * 2 ^ 59
def prefixEnd_1149766 : Nat := 4983230072969 + 3 ^ 40 * 1149766 * 2
def baseEnd_1149766 : Nat := 196794199399151256312443

theorem tailTrace_1149766 : CollatzResearch.WordTrace tailWord_1149766 prefixEnd_1149766 196794199399151256312443 := by
  unfold tailWord_1149766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1310481598518800663891911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27956940768401080829694101 1310481598518800663891911)
  ·
    refine ⟨1965722397778200995837867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1310481598518800663891911 1965722397778200995837867)
    ·
      refine ⟨2948583596667301493756801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1965722397778200995837867 2948583596667301493756801)
      ·
        refine ⟨2211437697500476120317601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2948583596667301493756801 2211437697500476120317601)
        ·
          refine ⟨1658578273125357090238201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2211437697500476120317601 1658578273125357090238201)
          ·
            refine ⟨1243933704844017817678651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1658578273125357090238201 1243933704844017817678651)
            ·
              refine ⟨1865900557266026726517977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243933704844017817678651 1865900557266026726517977)
              ·
                refine ⟨1399425417949520044888483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1865900557266026726517977 1399425417949520044888483)
                ·
                  refine ⟨2099138126924280067332725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399425417949520044888483 2099138126924280067332725)
                  ·
                    refine ⟨196794199399151256312443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2099138126924280067332725 196794199399151256312443)
                    ·
                      rfl

theorem cell23_1149766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1149766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149766 prefixEnd_1149766 := by exact prefixLift 1149766
  have htrace : WordTrace (prefixWord ++ tailWord_1149766) baseStart_1149766 baseEnd_1149766 := by
    simpa [prefixWord, tailWord_1149766, baseEnd_1149766] using wordTrace_append hprefix tailTrace_1149766
  have hstable : (prefixWord ++ tailWord_1149766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149766).length < 2 ^ (prefixWord ++ tailWord_1149766).sum := by decide
  have hdescent : baseEnd_1149766 < baseStart_1149766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149772 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 1, 2, 3]
def baseStart_1149772 : Nat := 118140960795 + 1149772 * 2 ^ 59
def prefixEnd_1149772 : Nat := 4983230072969 + 3 ^ 40 * 1149772 * 2
def baseEnd_1149772 : Nat := 590385679081380745462301

theorem tailTrace_1149772 : CollatzResearch.WordTrace tailWord_1149772 prefixEnd_1149772 590385679081380745462301 := by
  unfold tailWord_1149772
  simp only [CollatzResearch.WordTrace]
  refine ⟨20967814995289942134629785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27957086660386589512839713 20967814995289942134629785)
  ·
    refine ⟨15725861246467456600972339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20967814995289942134629785 15725861246467456600972339)
    ·
      refine ⟨23588791869701184901458509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15725861246467456600972339 23588791869701184901458509)
      ·
        refine ⟨8845796951137944338046941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23588791869701184901458509 8845796951137944338046941)
        ·
          refine ⟨3317173856676729126767603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8845796951137944338046941 3317173856676729126767603)
          ·
            refine ⟨4975760785015093690151405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317173856676729126767603 4975760785015093690151405)
            ·
              refine ⟨1865910294380660133806777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4975760785015093690151405 1865910294380660133806777)
              ·
                refine ⟨1399432720785495100355083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1865910294380660133806777 1399432720785495100355083)
                ·
                  refine ⟨2099149081178242650532625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399432720785495100355083 2099149081178242650532625)
                  ·
                    refine ⟨1574361810883681987899469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2099149081178242650532625 1574361810883681987899469)
                    ·
                      refine ⟨590385679081380745462301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1574361810883681987899469 590385679081380745462301)
                      ·
                        rfl

theorem cell23_1149772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_1149772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149772 prefixEnd_1149772 := by exact prefixLift 1149772
  have htrace : WordTrace (prefixWord ++ tailWord_1149772) baseStart_1149772 baseEnd_1149772 := by
    simpa [prefixWord, tailWord_1149772, baseEnd_1149772] using wordTrace_append hprefix tailTrace_1149772
  have hstable : (prefixWord ++ tailWord_1149772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149772).length < 2 ^ (prefixWord ++ tailWord_1149772).sum := by decide
  have hdescent : baseEnd_1149772 < baseStart_1149772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149785 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 1, 3, 3]
def baseStart_1149785 : Nat := 118140960795 + 1149785 * 2 ^ 59
def prefixEnd_1149785 : Nat := 4983230072969 + 3 ^ 40 * 1149785 * 2
def baseEnd_1149785 : Nat := 590392354329889194599741

theorem tailTrace_1149785 : CollatzResearch.WordTrace tailWord_1149785 prefixEnd_1149785 590392354329889194599741 := by
  unfold tailWord_1149785
  simp only [CollatzResearch.WordTrace]
  refine ⟨41936104139532787489482809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27957402759688524992988539 41936104139532787489482809)
  ·
    refine ⟨31452078104649590617112107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41936104139532787489482809 31452078104649590617112107)
    ·
      refine ⟨47178117156974385925668161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31452078104649590617112107 47178117156974385925668161)
      ·
        refine ⟨35383587867730789444251121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47178117156974385925668161 35383587867730789444251121)
        ·
          refine ⟨26537690900798092083188341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35383587867730789444251121 26537690900798092083188341)
          ·
            refine ⟨2487908521949821132798907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26537690900798092083188341 2487908521949821132798907)
            ·
              refine ⟨3731862782924731699198361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2487908521949821132798907 3731862782924731699198361)
              ·
                refine ⟨2798897087193548774398771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3731862782924731699198361 2798897087193548774398771)
                ·
                  refine ⟨4198345630790323161598157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798897087193548774398771 4198345630790323161598157)
                  ·
                    refine ⟨1574379611546371185599309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4198345630790323161598157 1574379611546371185599309)
                    ·
                      refine ⟨590392354329889194599741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1574379611546371185599309 590392354329889194599741)
                      ·
                        rfl

theorem cell23_1149785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_1149785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149785 prefixEnd_1149785 := by exact prefixLift 1149785
  have htrace : WordTrace (prefixWord ++ tailWord_1149785) baseStart_1149785 baseEnd_1149785 := by
    simpa [prefixWord, tailWord_1149785, baseEnd_1149785] using wordTrace_append hprefix tailTrace_1149785
  have hstable : (prefixWord ++ tailWord_1149785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149785).length < 2 ^ (prefixWord ++ tailWord_1149785).sum := by decide
  have hdescent : baseEnd_1149785 < baseStart_1149785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149808 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 4]
def baseStart_1149808 : Nat := 118140960795 + 1149808 * 2 ^ 59
def prefixEnd_1149808 : Nat := 4983230072969 + 3 ^ 40 * 1149808 * 2
def baseEnd_1149808 : Nat := 590404164384942604612135

theorem tailTrace_1149808 : CollatzResearch.WordTrace tailWord_1149808 prefixEnd_1149808 590404164384942604612135 := by
  unfold tailWord_1149808
  simp only [CollatzResearch.WordTrace]
  refine ⟨20968471509224731208785039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27957962012299641611713385 20968471509224731208785039)
  ·
    refine ⟨31452707263837096813177559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20968471509224731208785039 31452707263837096813177559)
    ·
      refine ⟨47179060895755645219766339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31452707263837096813177559 47179060895755645219766339)
      ·
        refine ⟨70768591343633467829649509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47179060895755645219766339 70768591343633467829649509)
        ·
          refine ⟨13269110876931275218059283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70768591343633467829649509 13269110876931275218059283)
          ·
            refine ⟨19903666315396912827088925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13269110876931275218059283 19903666315396912827088925)
            ·
              refine ⟨7463874868273842310158347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19903666315396912827088925 7463874868273842310158347)
              ·
                refine ⟨11195812302410763465237521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7463874868273842310158347 11195812302410763465237521)
                ·
                  refine ⟨8396859226808072598928141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11195812302410763465237521 8396859226808072598928141)
                  ·
                    refine ⟨3148822210053027224598053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8396859226808072598928141 3148822210053027224598053)
                    ·
                      refine ⟨590404164384942604612135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3148822210053027224598053 590404164384942604612135)
                      ·
                        rfl

theorem cell23_1149808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_1149808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149808 prefixEnd_1149808 := by exact prefixLift 1149808
  have htrace : WordTrace (prefixWord ++ tailWord_1149808) baseStart_1149808 baseEnd_1149808 := by
    simpa [prefixWord, tailWord_1149808, baseEnd_1149808] using wordTrace_append hprefix tailTrace_1149808
  have hstable : (prefixWord ++ tailWord_1149808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149808).length < 2 ^ (prefixWord ++ tailWord_1149808).sum := by decide
  have hdescent : baseEnd_1149808 < baseStart_1149808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149855 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1149855 : Nat := 118140960795 + 1149855 * 2 ^ 59
def prefixEnd_1149855 : Nat := 4983230072969 + 3 ^ 40 * 1149855 * 2
def baseEnd_1149855 : Nat := 590428297975703920724419

theorem tailTrace_1149855 : CollatzResearch.WordTrace tailWord_1149855 prefixEnd_1149855 590428297975703920724419 := by
  unfold tailWord_1149855
  simp only [CollatzResearch.WordTrace]
  refine ⟨41938657249279189444531019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27959104832852792963020679 41938657249279189444531019)
  ·
    refine ⟨62907985873918784166796529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41938657249279189444531019 62907985873918784166796529)
    ·
      refine ⟨47180989405439088125097397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62907985873918784166796529 47180989405439088125097397)
      ·
        refine ⟨4423217756759914511727881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47180989405439088125097397 4423217756759914511727881)
        ·
          refine ⟨3317413317569935883795911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4423217756759914511727881 3317413317569935883795911)
          ·
            refine ⟨4976119976354903825693867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317413317569935883795911 4976119976354903825693867)
            ·
              refine ⟨7464179964532355738540801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4976119976354903825693867 7464179964532355738540801)
              ·
                refine ⟨5598134973399266803905601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7464179964532355738540801 5598134973399266803905601)
                ·
                  refine ⟨4198601230049450102929201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5598134973399266803905601 4198601230049450102929201)
                  ·
                    refine ⟨3148950922537087577196901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4198601230049450102929201 3148950922537087577196901)
                    ·
                      refine ⟨590428297975703920724419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3148950922537087577196901 590428297975703920724419)
                      ·
                        rfl

theorem cell23_1149855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1149855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149855 prefixEnd_1149855 := by exact prefixLift 1149855
  have htrace : WordTrace (prefixWord ++ tailWord_1149855) baseStart_1149855 baseEnd_1149855 := by
    simpa [prefixWord, tailWord_1149855, baseEnd_1149855] using wordTrace_append hprefix tailTrace_1149855
  have hstable : (prefixWord ++ tailWord_1149855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149855).length < 2 ^ (prefixWord ++ tailWord_1149855).sum := by decide
  have hdescent : baseEnd_1149855 < baseStart_1149855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149859 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 2, 2, 2]
def baseStart_1149859 : Nat := 118140960795 + 1149859 * 2 ^ 59
def prefixEnd_1149859 : Nat := 4983230072969 + 3 ^ 40 * 1149859 * 2
def baseEnd_1149859 : Nat := 590430351898321905074401

theorem tailTrace_1149859 : CollatzResearch.WordTrace tailWord_1149859 prefixEnd_1149859 590430351898321905074401 := by
  unfold tailWord_1149859
  simp only [CollatzResearch.WordTrace]
  refine ⟨41938803141264698127676631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27959202094176465418451087 41938803141264698127676631)
  ·
    refine ⟨62908204711897047191514947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41938803141264698127676631 62908204711897047191514947)
    ·
      refine ⟨94362307067845570787272421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62908204711897047191514947 94362307067845570787272421)
      ·
        refine ⟨17692932575221044522613579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94362307067845570787272421 17692932575221044522613579)
        ·
          refine ⟨26539398862831566783920369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17692932575221044522613579 26539398862831566783920369)
          ·
            refine ⟨19904549147123675087940277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26539398862831566783920369 19904549147123675087940277)
            ·
              refine ⟨1866051482542844539494401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19904549147123675087940277 1866051482542844539494401)
              ·
                refine ⟨1399538611907133404620801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866051482542844539494401 1399538611907133404620801)
                ·
                  refine ⟨1049653958930350053465601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1399538611907133404620801 1049653958930350053465601)
                  ·
                    refine ⟨787240469197762540099201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1049653958930350053465601 787240469197762540099201)
                    ·
                      refine ⟨590430351898321905074401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 787240469197762540099201 590430351898321905074401)
                      ·
                        rfl

theorem cell23_1149859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_1149859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149859 prefixEnd_1149859 := by exact prefixLift 1149859
  have htrace : WordTrace (prefixWord ++ tailWord_1149859) baseStart_1149859 baseEnd_1149859 := by
    simpa [prefixWord, tailWord_1149859, baseEnd_1149859] using wordTrace_append hprefix tailTrace_1149859
  have hstable : (prefixWord ++ tailWord_1149859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149859).length < 2 ^ (prefixWord ++ tailWord_1149859).sum := by decide
  have hdescent : baseEnd_1149859 < baseStart_1149859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149865 : List Nat := [1, 2, 1, 1, 1, 1, 5, 6, 5]
def baseStart_1149865 : Nat := 118140960795 + 1149865 * 2 ^ 59
def prefixEnd_1149865 : Nat := 4983230072969 + 3 ^ 40 * 1149865 * 2
def baseEnd_1149865 : Nat := 65603714753583209066597

theorem tailTrace_1149865 : CollatzResearch.WordTrace tailWord_1149865 prefixEnd_1149865 65603714753583209066597 := by
  unfold tailWord_1149865
  simp only [CollatzResearch.WordTrace]
  refine ⟨41939021979242961152395049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27959347986161974101596699 41939021979242961152395049)
  ·
    refine ⟨31454266484432220864296287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41939021979242961152395049 31454266484432220864296287)
    ·
      refine ⟨47181399726648331296444431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31454266484432220864296287 47181399726648331296444431)
      ·
        refine ⟨70772099589972496944666647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47181399726648331296444431 70772099589972496944666647)
        ·
          refine ⟨106158149384958745416999971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70772099589972496944666647 106158149384958745416999971)
          ·
            refine ⟨159237224077438118125499957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106158149384958745416999971 159237224077438118125499957)
            ·
              refine ⟨14928489757259823574265621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159237224077438118125499957 14928489757259823574265621)
              ·
                refine ⟨699772957371554230043701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14928489757259823574265621 699772957371554230043701)
                ·
                  refine ⟨65603714753583209066597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 699772957371554230043701 65603714753583209066597)
                  ·
                    rfl

theorem cell23_1149865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 5].length) (baseStart_1149865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149865 prefixEnd_1149865 := by exact prefixLift 1149865
  have htrace : WordTrace (prefixWord ++ tailWord_1149865) baseStart_1149865 baseEnd_1149865 := by
    simpa [prefixWord, tailWord_1149865, baseEnd_1149865] using wordTrace_append hprefix tailTrace_1149865
  have hstable : (prefixWord ++ tailWord_1149865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149865).length < 2 ^ (prefixWord ++ tailWord_1149865).sum := by decide
  have hdescent : baseEnd_1149865 < baseStart_1149865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149876 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_1149876 : Nat := 118140960795 + 1149876 * 2 ^ 59
def prefixEnd_1149876 : Nat := 4983230072969 + 3 ^ 40 * 1149876 * 2
def baseEnd_1149876 : Nat := 590439081069448338561823

theorem tailTrace_1149876 : CollatzResearch.WordTrace tailWord_1149876 prefixEnd_1149876 590439081069448338561823 := by
  unfold tailWord_1149876
  simp only [CollatzResearch.WordTrace]
  refine ⟨20969711591101555015522741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27959615454802073354030321 20969711591101555015522741)
  ·
    refine ⟨1965910461665770782705257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20969711591101555015522741 1965910461665770782705257)
    ·
      refine ⟨1474432846249328087028943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1965910461665770782705257 1474432846249328087028943)
      ·
        refine ⟨2211649269373992130543415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474432846249328087028943 2211649269373992130543415)
        ·
          refine ⟨3317473904060988195815123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2211649269373992130543415 3317473904060988195815123)
          ·
            refine ⟨4976210856091482293722685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317473904060988195815123 4976210856091482293722685)
            ·
              refine ⟨1866079071034305860146007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4976210856091482293722685 1866079071034305860146007)
              ·
                refine ⟨2799118606551458790219011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866079071034305860146007 2799118606551458790219011)
                ·
                  refine ⟨4198677909827188185328517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799118606551458790219011 4198677909827188185328517)
                  ·
                    refine ⟨787252108092597784749097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4198677909827188185328517 787252108092597784749097)
                    ·
                      refine ⟨590439081069448338561823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 787252108092597784749097 590439081069448338561823)
                      ·
                        rfl

theorem cell23_1149876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_1149876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149876 prefixEnd_1149876 := by exact prefixLift 1149876
  have htrace : WordTrace (prefixWord ++ tailWord_1149876) baseStart_1149876 baseEnd_1149876 := by
    simpa [prefixWord, tailWord_1149876, baseEnd_1149876] using wordTrace_append hprefix tailTrace_1149876
  have hstable : (prefixWord ++ tailWord_1149876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149876).length < 2 ^ (prefixWord ++ tailWord_1149876).sum := by decide
  have hdescent : baseEnd_1149876 < baseStart_1149876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149922 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1149922 : Nat := 118140960795 + 1149922 * 2 ^ 59
def prefixEnd_1149922 : Nat := 4983230072969 + 3 ^ 40 * 1149922 * 2
def baseEnd_1149922 : Nat := 590462701179555158586611

theorem tailTrace_1149922 : CollatzResearch.WordTrace tailWord_1149922 prefixEnd_1149922 590462701179555158586611 := by
  unfold tailWord_1149922
  simp only [CollatzResearch.WordTrace]
  refine ⟨10485275235009114971805005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27960733960024306591480013 10485275235009114971805005)
  ·
    refine ⟨3931978213128418114426877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10485275235009114971805005 3931978213128418114426877)
    ·
      refine ⟨1474491829923156792910079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3931978213128418114426877 1474491829923156792910079)
      ·
        refine ⟨2211737744884735189365119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474491829923156792910079 2211737744884735189365119)
        ·
          refine ⟨3317606617327102784047679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2211737744884735189365119 3317606617327102784047679)
          ·
            refine ⟨4976409925990654176071519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3317606617327102784047679 4976409925990654176071519)
            ·
              refine ⟨7464614888985981264107279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4976409925990654176071519 7464614888985981264107279)
              ·
                refine ⟨11196922333478971896160919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7464614888985981264107279 11196922333478971896160919)
                ·
                  refine ⟨16795383500218457844241379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11196922333478971896160919 16795383500218457844241379)
                  ·
                    refine ⟨25193075250327686766362069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16795383500218457844241379 25193075250327686766362069)
                    ·
                      refine ⟨590462701179555158586611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25193075250327686766362069 590462701179555158586611)
                      ·
                        rfl

theorem cell23_1149922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1149922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149922 prefixEnd_1149922 := by exact prefixLift 1149922
  have htrace : WordTrace (prefixWord ++ tailWord_1149922) baseStart_1149922 baseEnd_1149922 := by
    simpa [prefixWord, tailWord_1149922, baseEnd_1149922] using wordTrace_append hprefix tailTrace_1149922
  have hstable : (prefixWord ++ tailWord_1149922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149922).length < 2 ^ (prefixWord ++ tailWord_1149922).sum := by decide
  have hdescent : baseEnd_1149922 < baseStart_1149922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149959 : List Nat := [1, 1, 4, 3, 1, 1, 2, 5, 1, 4]
def baseStart_1149959 : Nat := 118140960795 + 1149959 * 2 ^ 59
def prefixEnd_1149959 : Nat := 4983230072969 + 3 ^ 40 * 1149959 * 2
def baseEnd_1149959 : Nat := 196827233321257171274647

theorem tailTrace_1149959 : CollatzResearch.WordTrace tailWord_1149959 prefixEnd_1149959 196827233321257171274647 := by
  unfold tailWord_1149959
  simp only [CollatzResearch.WordTrace]
  refine ⟨41942450440902415206316931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27961633627268276804211287 41942450440902415206316931)
  ·
    refine ⟨62913675661353622809475397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41942450440902415206316931 62913675661353622809475397)
    ·
      refine ⟨11796314186503804276776637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62913675661353622809475397 11796314186503804276776637)
      ·
        refine ⟨4423617819938926603791239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11796314186503804276776637 4423617819938926603791239)
        ·
          refine ⟨6635426729908389905686859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4423617819938926603791239 6635426729908389905686859)
          ·
            refine ⟨9953140094862584858530289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6635426729908389905686859 9953140094862584858530289)
            ·
              refine ⟨7464855071146938643897717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9953140094862584858530289 7464855071146938643897717)
              ·
                refine ⟨699830162920025497865411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7464855071146938643897717 699830162920025497865411)
                ·
                  refine ⟨1049745244380038246798117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699830162920025497865411 1049745244380038246798117)
                  ·
                    refine ⟨196827233321257171274647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1049745244380038246798117 196827233321257171274647)
                    ·
                      rfl

theorem cell23_1149959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_1149959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149959 prefixEnd_1149959 := by exact prefixLift 1149959
  have htrace : WordTrace (prefixWord ++ tailWord_1149959) baseStart_1149959 baseEnd_1149959 := by
    simpa [prefixWord, tailWord_1149959, baseEnd_1149959] using wordTrace_append hprefix tailTrace_1149959
  have hstable : (prefixWord ++ tailWord_1149959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149959).length < 2 ^ (prefixWord ++ tailWord_1149959).sum := by decide
  have hdescent : baseEnd_1149959 < baseStart_1149959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1149976 : List Nat := [2, 1, 2, 3, 2, 2, 4, 2, 1, 4]
def baseStart_1149976 : Nat := 118140960795 + 1149976 * 2 ^ 59
def prefixEnd_1149976 : Nat := 4983230072969 + 3 ^ 40 * 1149976 * 2
def baseEnd_1149976 : Nat := 196830143044965982437121

theorem tailTrace_1149976 : CollatzResearch.WordTrace tailWord_1149976 prefixEnd_1149976 196830143044965982437121 := by
  unfold tailWord_1149976
  simp only [CollatzResearch.WordTrace]
  refine ⟨20971535240920413554842891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27962046987893884739790521 20971535240920413554842891)
  ·
    refine ⟨31457302861380620332264337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20971535240920413554842891 31457302861380620332264337)
    ·
      refine ⟨23592977146035465249198253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31457302861380620332264337 23592977146035465249198253)
      ·
        refine ⟨8847366429763299468449345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23592977146035465249198253 8847366429763299468449345)
        ·
          refine ⟨6635524822322474601337009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8847366429763299468449345 6635524822322474601337009)
          ·
            refine ⟨4976643616741855951002757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6635524822322474601337009 4976643616741855951002757)
            ·
              refine ⟨933120678139097990813017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4976643616741855951002757 933120678139097990813017)
              ·
                refine ⟨699840508604323493109763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933120678139097990813017 699840508604323493109763)
                ·
                  refine ⟨1049760762906485239664645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699840508604323493109763 1049760762906485239664645)
                  ·
                    refine ⟨196830143044965982437121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1049760762906485239664645 196830143044965982437121)
                    ·
                      rfl

theorem cell23_1149976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_1149976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1149976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1149976 prefixEnd_1149976 := by exact prefixLift 1149976
  have htrace : WordTrace (prefixWord ++ tailWord_1149976) baseStart_1149976 baseEnd_1149976 := by
    simpa [prefixWord, tailWord_1149976, baseEnd_1149976] using wordTrace_append hprefix tailTrace_1149976
  have hstable : (prefixWord ++ tailWord_1149976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1149976).length < 2 ^ (prefixWord ++ tailWord_1149976).sum := by decide
  have hdescent : baseEnd_1149976 < baseStart_1149976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1149976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150002 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 1, 5]
def baseStart_1150002 : Nat := 118140960795 + 1150002 * 2 ^ 59
def prefixEnd_1150002 : Nat := 4983230072969 + 3 ^ 40 * 1150002 * 2
def baseEnd_1150002 : Nat := 196834593210638281862081

theorem tailTrace_1150002 : CollatzResearch.WordTrace tailWord_1150002 prefixEnd_1150002 196834593210638281862081 := by
  unfold tailWord_1150002
  simp only [CollatzResearch.WordTrace]
  refine ⟨10486004694936658387533065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27962679186497755700088173 10486004694936658387533065)
  ·
    refine ⟨7864503521202493790649799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10486004694936658387533065 7864503521202493790649799)
    ·
      refine ⟨11796755281803740685974699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7864503521202493790649799 11796755281803740685974699)
      ·
        refine ⟨17695132922705611028962049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11796755281803740685974699 17695132922705611028962049)
        ·
          refine ⟨13271349692029208271721537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17695132922705611028962049 13271349692029208271721537)
          ·
            refine ⟨9953512269021906203791153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13271349692029208271721537 9953512269021906203791153)
            ·
              refine ⟨7465134201766429652843365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9953512269021906203791153 7465134201766429652843365)
              ·
                refine ⟨1399712662831205559908131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7465134201766429652843365 1399712662831205559908131)
                ·
                  refine ⟨2099568994246808339862197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399712662831205559908131 2099568994246808339862197)
                  ·
                    refine ⟨196834593210638281862081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2099568994246808339862197 196834593210638281862081)
                    ·
                      rfl

theorem cell23_1150002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_1150002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150002 prefixEnd_1150002 := by exact prefixLift 1150002
  have htrace : WordTrace (prefixWord ++ tailWord_1150002) baseStart_1150002 baseEnd_1150002 := by
    simpa [prefixWord, tailWord_1150002, baseEnd_1150002] using wordTrace_append hprefix tailTrace_1150002
  have hstable : (prefixWord ++ tailWord_1150002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150002).length < 2 ^ (prefixWord ++ tailWord_1150002).sum := by decide
  have hdescent : baseEnd_1150002 < baseStart_1150002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150009 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 1, 5, 2]
def baseStart_1150009 : Nat := 118140960795 + 1150009 * 2 ^ 59
def prefixEnd_1150009 : Nat := 4983230072969 + 3 ^ 40 * 1150009 * 2
def baseEnd_1150009 : Nat := 590507373996496318198711

theorem tailTrace_1150009 : CollatzResearch.WordTrace tailWord_1150009 prefixEnd_1150009 590507373996496318198711 := by
  unfold tailWord_1150009
  simp only [CollatzResearch.WordTrace]
  refine ⟨41944274090721273745637081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27962849393814182497091387 41944274090721273745637081)
  ·
    refine ⟨31458205568040955309227811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41944274090721273745637081 31458205568040955309227811)
    ·
      refine ⟨47187308352061432963841717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31458205568040955309227811 47187308352061432963841717)
      ·
        refine ⟨4423810158005759340360161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47187308352061432963841717 4423810158005759340360161)
        ·
          refine ⟨3317857618504319505270121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4423810158005759340360161 3317857618504319505270121)
          ·
            refine ⟨2488393213878239628952591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3317857618504319505270121 2488393213878239628952591)
            ·
              refine ⟨3732589820817359443428887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488393213878239628952591 3732589820817359443428887)
              ·
                refine ⟨5598884731226039165143331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3732589820817359443428887 5598884731226039165143331)
                ·
                  refine ⟨8398327096839058747714997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5598884731226039165143331 8398327096839058747714997)
                  ·
                    refine ⟨787343165328661757598281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8398327096839058747714997 787343165328661757598281)
                    ·
                      refine ⟨590507373996496318198711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 787343165328661757598281 590507373996496318198711)
                      ·
                        rfl

theorem cell23_1150009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_1150009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150009 prefixEnd_1150009 := by exact prefixLift 1150009
  have htrace : WordTrace (prefixWord ++ tailWord_1150009) baseStart_1150009 baseEnd_1150009 := by
    simpa [prefixWord, tailWord_1150009, baseEnd_1150009] using wordTrace_append hprefix tailTrace_1150009
  have hstable : (prefixWord ++ tailWord_1150009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150009).length < 2 ^ (prefixWord ++ tailWord_1150009).sum := by decide
  have hdescent : baseEnd_1150009 < baseStart_1150009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150016 : List Nat := [2, 1, 1, 2, 2, 3, 4, 3, 1, 1, 3]
def baseStart_1150016 : Nat := 118140960795 + 1150016 * 2 ^ 59
def prefixEnd_1150016 : Nat := 4983230072969 + 3 ^ 40 * 1150016 * 2
def baseEnd_1150016 : Nat := 590510968361077790811179

theorem tailTrace_1150016 : CollatzResearch.WordTrace tailWord_1150016 prefixEnd_1150016 590510968361077790811179 := by
  unfold tailWord_1150016
  simp only [CollatzResearch.WordTrace]
  refine ⟨20972264700847956970570951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27963019601130609294094601 20972264700847956970570951)
  ·
    refine ⟨31458397051271935455856427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20972264700847956970570951 31458397051271935455856427)
    ·
      refine ⟨47187595576907903183784641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31458397051271935455856427 47187595576907903183784641)
      ·
        refine ⟨35390696682680927387838481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47187595576907903183784641 35390696682680927387838481)
        ·
          refine ⟨26543022512010695540878861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35390696682680927387838481 26543022512010695540878861)
          ·
            refine ⟨9953633442004010827829573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26543022512010695540878861 9953633442004010827829573)
            ·
              refine ⟨1866306270375752030218045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9953633442004010827829573 1866306270375752030218045)
              ·
                refine ⟨699864851390907011331767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1866306270375752030218045 699864851390907011331767)
                ·
                  refine ⟨1049797277086360516997651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699864851390907011331767 1049797277086360516997651)
                  ·
                    refine ⟨1574695915629540775496477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1049797277086360516997651 1574695915629540775496477)
                    ·
                      refine ⟨590510968361077790811179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1574695915629540775496477 590510968361077790811179)
                      ·
                        rfl

theorem cell23_1150016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 1, 1, 3].length) (baseStart_1150016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150016 prefixEnd_1150016 := by exact prefixLift 1150016
  have htrace : WordTrace (prefixWord ++ tailWord_1150016) baseStart_1150016 baseEnd_1150016 := by
    simpa [prefixWord, tailWord_1150016, baseEnd_1150016] using wordTrace_append hprefix tailTrace_1150016
  have hstable : (prefixWord ++ tailWord_1150016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150016).length < 2 ^ (prefixWord ++ tailWord_1150016).sum := by decide
  have hdescent : baseEnd_1150016 < baseStart_1150016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150035 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 4]
def baseStart_1150035 : Nat := 118140960795 + 1150035 * 2 ^ 59
def prefixEnd_1150035 : Nat := 4983230072969 + 3 ^ 40 * 1150035 * 2
def baseEnd_1150035 : Nat := 590520724493513216473591

theorem tailTrace_1150035 : CollatzResearch.WordTrace tailWord_1150035 prefixEnd_1150035 590520724493513216473591 := by
  unfold tailWord_1150035
  simp only [CollatzResearch.WordTrace]
  refine ⟨41945222388627080186083559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27963481592418053457389039 41945222388627080186083559)
  ·
    refine ⟨62917833582940620279125339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41945222388627080186083559 62917833582940620279125339)
    ·
      refine ⟨94376750374410930418688009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62917833582940620279125339 94376750374410930418688009)
      ·
        refine ⟨70782562780808197814016007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94376750374410930418688009 70782562780808197814016007)
        ·
          refine ⟨106173844171212296721024011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70782562780808197814016007 106173844171212296721024011)
          ·
            refine ⟨159260766256818445081536017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106173844171212296721024011 159260766256818445081536017)
            ·
              refine ⟨119445574692613833811152013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159260766256818445081536017 119445574692613833811152013)
              ·
                refine ⟨44792090509730187679182005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119445574692613833811152013 44792090509730187679182005)
                ·
                  refine ⟨4199258485287205094923313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44792090509730187679182005 4199258485287205094923313)
                  ·
                    refine ⟨3149443863965403821192485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4199258485287205094923313 3149443863965403821192485)
                    ·
                      refine ⟨590520724493513216473591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3149443863965403821192485 590520724493513216473591)
                      ·
                        rfl

theorem cell23_1150035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_1150035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150035 prefixEnd_1150035 := by exact prefixLift 1150035
  have htrace : WordTrace (prefixWord ++ tailWord_1150035) baseStart_1150035 baseEnd_1150035 := by
    simpa [prefixWord, tailWord_1150035, baseEnd_1150035] using wordTrace_append hprefix tailTrace_1150035
  have hstable : (prefixWord ++ tailWord_1150035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150035).length < 2 ^ (prefixWord ++ tailWord_1150035).sum := by decide
  have hdescent : baseEnd_1150035 < baseStart_1150035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150042 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3]
def baseStart_1150042 : Nat := 118140960795 + 1150042 * 2 ^ 59
def prefixEnd_1150042 : Nat := 4983230072969 + 3 ^ 40 * 1150042 * 2
def baseEnd_1150042 : Nat := 590524318858094689086059

theorem tailTrace_1150042 : CollatzResearch.WordTrace tailWord_1150042 prefixEnd_1150042 590524318858094689086059 := by
  unfold tailWord_1150042
  simp only [CollatzResearch.WordTrace]
  refine ⟨10486369424900430095397095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27963651799734480254392253 10486369424900430095397095)
  ·
    refine ⟨15729554137350645143095643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10486369424900430095397095 15729554137350645143095643)
    ·
      refine ⟨23594331206025967714643465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15729554137350645143095643 23594331206025967714643465)
      ·
        refine ⟨17695748404519475785982599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23594331206025967714643465 17695748404519475785982599)
        ·
          refine ⟨26543622606779213678973899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17695748404519475785982599 26543622606779213678973899)
          ·
            refine ⟨39815433910168820518460849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26543622606779213678973899 39815433910168820518460849)
            ·
              refine ⟨29861575432626615388845637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39815433910168820518460849 29861575432626615388845637)
              ·
                refine ⟨5599045393617490385408557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29861575432626615388845637 5599045393617490385408557)
                ·
                  refine ⟨2099642022606558894528209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5599045393617490385408557 2099642022606558894528209)
                  ·
                    refine ⟨1574731516954919170896157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2099642022606558894528209 1574731516954919170896157)
                    ·
                      refine ⟨590524318858094689086059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1574731516954919170896157 590524318858094689086059)
                      ·
                        rfl

theorem cell23_1150042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_1150042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150042 prefixEnd_1150042 := by exact prefixLift 1150042
  have htrace : WordTrace (prefixWord ++ tailWord_1150042) baseStart_1150042 baseEnd_1150042 := by
    simpa [prefixWord, tailWord_1150042, baseEnd_1150042] using wordTrace_append hprefix tailTrace_1150042
  have hstable : (prefixWord ++ tailWord_1150042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150042).length < 2 ^ (prefixWord ++ tailWord_1150042).sum := by decide
  have hdescent : baseEnd_1150042 < baseStart_1150042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150062 : List Nat := [4, 1, 2, 2, 1, 3, 1, 9]
def baseStart_1150062 : Nat := 118140960795 + 1150062 * 2 ^ 59
def prefixEnd_1150062 : Nat := 4983230072969 + 3 ^ 40 * 1150062 * 2
def baseEnd_1150062 : Nat := 21871651424858689290221

theorem tailTrace_1150062 : CollatzResearch.WordTrace tailWord_1150062 prefixEnd_1150062 21871651424858689290221 := by
  unfold tailWord_1150062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5243275894941157974664555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27964138106352842531544293 5243275894941157974664555)
  ·
    refine ⟨7864913842411736961996833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5243275894941157974664555 7864913842411736961996833)
    ·
      refine ⟨5898685381808802721497625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7864913842411736961996833 5898685381808802721497625)
      ·
        refine ⟨4424014036356602041123219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5898685381808802721497625 4424014036356602041123219)
        ·
          refine ⟨6636021054534903061684829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4424014036356602041123219 6636021054534903061684829)
          ·
            refine ⟨2488507895450588648131811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6636021054534903061684829 2488507895450588648131811)
            ·
              refine ⟨3732761843175882972197717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488507895450588648131811 3732761843175882972197717)
              ·
                refine ⟨21871651424858689290221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3732761843175882972197717 21871651424858689290221)
                ·
                  rfl

theorem cell23_1150062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_1150062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150062 prefixEnd_1150062 := by exact prefixLift 1150062
  have htrace : WordTrace (prefixWord ++ tailWord_1150062) baseStart_1150062 baseEnd_1150062 := by
    simpa [prefixWord, tailWord_1150062, baseEnd_1150062] using wordTrace_append hprefix tailTrace_1150062
  have hstable : (prefixWord ++ tailWord_1150062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150062).length < 2 ^ (prefixWord ++ tailWord_1150062).sum := by decide
  have hdescent : baseEnd_1150062 < baseStart_1150062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150072 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 1, 3, 3]
def baseStart_1150072 : Nat := 118140960795 + 1150072 * 2 ^ 59
def prefixEnd_1150072 : Nat := 4983230072969 + 3 ^ 40 * 1150072 * 2
def baseEnd_1150072 : Nat := 590539723277729571710921

theorem tailTrace_1150072 : CollatzResearch.WordTrace tailWord_1150072 prefixEnd_1150072 590539723277729571710921 := by
  unfold tailWord_1150072
  simp only [CollatzResearch.WordTrace]
  refine ⟨20973285944746517752590235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27964381259662023670120313 20973285944746517752590235)
  ·
    refine ⟨31459928917119776628885353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20973285944746517752590235 31459928917119776628885353)
    ·
      refine ⟨23594946687839832471664015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31459928917119776628885353 23594946687839832471664015)
      ·
        refine ⟨35392420031759748707496023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23594946687839832471664015 35392420031759748707496023)
        ·
          refine ⟨53088630047639623061244035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35392420031759748707496023 53088630047639623061244035)
          ·
            refine ⟨79632945071459434591866053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53088630047639623061244035 79632945071459434591866053)
            ·
              refine ⟨14931177200898643985974885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79632945071459434591866053 14931177200898643985974885)
              ·
                refine ⟨2799595725168495747370291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14931177200898643985974885 2799595725168495747370291)
                ·
                  refine ⟨4199393587752743621055437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2799595725168495747370291 4199393587752743621055437)
                  ·
                    refine ⟨1574772595407278857895789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4199393587752743621055437 1574772595407278857895789)
                    ·
                      refine ⟨590539723277729571710921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1574772595407278857895789 590539723277729571710921)
                      ·
                        rfl

theorem cell23_1150072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_1150072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150072 prefixEnd_1150072 := by exact prefixLift 1150072
  have htrace : WordTrace (prefixWord ++ tailWord_1150072) baseStart_1150072 baseEnd_1150072 := by
    simpa [prefixWord, tailWord_1150072, baseEnd_1150072] using wordTrace_append hprefix tailTrace_1150072
  have hstable : (prefixWord ++ tailWord_1150072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150072).length < 2 ^ (prefixWord ++ tailWord_1150072).sum := by decide
  have hdescent : baseEnd_1150072 < baseStart_1150072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150089 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 4, 1, 3]
def baseStart_1150089 : Nat := 118140960795 + 1150089 * 2 ^ 59
def prefixEnd_1150089 : Nat := 4983230072969 + 3 ^ 40 * 1150089 * 2
def baseEnd_1150089 : Nat := 590548452448856005198343

theorem tailTrace_1150089 : CollatzResearch.WordTrace tailWord_1150089 prefixEnd_1150089 590548452448856005198343 := by
  unfold tailWord_1150089
  simp only [CollatzResearch.WordTrace]
  refine ⟨41947191930431447408549321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27964794620287631605699547 41947191930431447408549321)
  ·
    refine ⟨31460393947823585556411991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41947191930431447408549321 31460393947823585556411991)
    ·
      refine ⟨47190590921735378334617987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31460393947823585556411991 47190590921735378334617987)
      ·
        refine ⟨70785886382603067501926981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47190590921735378334617987 70785886382603067501926981)
        ·
          refine ⟨13272353696738075156611309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70785886382603067501926981 13272353696738075156611309)
          ·
            refine ⟨4977132636276778183729241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13272353696738075156611309 4977132636276778183729241)
            ·
              refine ⟨3732849477207583637796931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4977132636276778183729241 3732849477207583637796931)
              ·
                refine ⟨5599274215811375456695397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3732849477207583637796931 5599274215811375456695397)
                ·
                  refine ⟨1049863915464632898130387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5599274215811375456695397 1049863915464632898130387)
                  ·
                    refine ⟨1574795873196949347195581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1049863915464632898130387 1574795873196949347195581)
                    ·
                      refine ⟨590548452448856005198343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1574795873196949347195581 590548452448856005198343)
                      ·
                        rfl

theorem cell23_1150089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 1, 3].length) (baseStart_1150089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150089 prefixEnd_1150089 := by exact prefixLift 1150089
  have htrace : WordTrace (prefixWord ++ tailWord_1150089) baseStart_1150089 baseEnd_1150089 := by
    simpa [prefixWord, tailWord_1150089, baseEnd_1150089] using wordTrace_append hprefix tailTrace_1150089
  have hstable : (prefixWord ++ tailWord_1150089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150089).length < 2 ^ (prefixWord ++ tailWord_1150089).sum := by decide
  have hdescent : baseEnd_1150089 < baseStart_1150089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150090 : List Nat := [3, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2]
def baseStart_1150090 : Nat := 118140960795 + 1150090 * 2 ^ 59
def prefixEnd_1150090 : Nat := 4983230072969 + 3 ^ 40 * 1150090 * 2
def baseEnd_1150090 : Nat := 590548965929510501285839

theorem tailTrace_1150090 : CollatzResearch.WordTrace tailWord_1150090 prefixEnd_1150090 590548965929510501285839 := by
  unfold tailWord_1150090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10486807100856956144833931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27964818935618549719557149 10486807100856956144833931)
  ·
    refine ⟨15730210651285434217250897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10486807100856956144833931 15730210651285434217250897)
    ·
      refine ⟨11797657988464075662938173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15730210651285434217250897 11797657988464075662938173)
      ·
        refine ⟨4424121745674028373601815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11797657988464075662938173 4424121745674028373601815)
        ·
          refine ⟨6636182618511042560402723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4424121745674028373601815 6636182618511042560402723)
          ·
            refine ⟨9954273927766563840604085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6636182618511042560402723 9954273927766563840604085)
            ·
              refine ⟨933213180728115360056633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9954273927766563840604085 933213180728115360056633)
              ·
                refine ⟨699909885546086520042475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933213180728115360056633 699909885546086520042475)
                ·
                  refine ⟨1049864828319129780063713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699909885546086520042475 1049864828319129780063713)
                  ·
                    refine ⟨787398621239347335047785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1049864828319129780063713 787398621239347335047785)
                    ·
                      refine ⟨590548965929510501285839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 787398621239347335047785 590548965929510501285839)
                      ·
                        rfl

theorem cell23_1150090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_1150090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150090 prefixEnd_1150090 := by exact prefixLift 1150090
  have htrace : WordTrace (prefixWord ++ tailWord_1150090) baseStart_1150090 baseEnd_1150090 := by
    simpa [prefixWord, tailWord_1150090, baseEnd_1150090] using wordTrace_append hprefix tailTrace_1150090
  have hstable : (prefixWord ++ tailWord_1150090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150090).length < 2 ^ (prefixWord ++ tailWord_1150090).sum := by decide
  have hdescent : baseEnd_1150090 < baseStart_1150090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150116 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 3, 3, 2]
def baseStart_1150116 : Nat := 118140960795 + 1150116 * 2 ^ 59
def prefixEnd_1150116 : Nat := 4983230072969 + 3 ^ 40 * 1150116 * 2
def baseEnd_1150116 : Nat := 590562316426527399560719

theorem tailTrace_1150116 : CollatzResearch.WordTrace tailWord_1150116 prefixEnd_1150116 590562316426527399560719 := by
  unfold tailWord_1150116
  simp only [CollatzResearch.WordTrace]
  refine ⟨20974088350666815509891101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27965451134222420679854801 20974088350666815509891101)
  ·
    refine ⟨7865283131500055816209163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20974088350666815509891101 7865283131500055816209163)
    ·
      refine ⟨11797924697250083724313745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7865283131500055816209163 11797924697250083724313745)
      ·
        refine ⟨8848443522937562793235309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11797924697250083724313745 8848443522937562793235309)
        ·
          refine ⟨3318166321101586047463241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8848443522937562793235309 3318166321101586047463241)
          ·
            refine ⟨2488624740826189535597431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3318166321101586047463241 2488624740826189535597431)
            ·
              refine ⟨3732937111239284303396147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488624740826189535597431 3732937111239284303396147)
              ·
                refine ⟨5599405666858926455094221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3732937111239284303396147 5599405666858926455094221)
                ·
                  refine ⟨2099777125072097420660333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5599405666858926455094221 2099777125072097420660333)
                  ·
                    refine ⟨787416421902036532747625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2099777125072097420660333 787416421902036532747625)
                    ·
                      refine ⟨590562316426527399560719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 787416421902036532747625 590562316426527399560719)
                      ·
                        rfl

theorem cell23_1150116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_1150116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150116 prefixEnd_1150116 := by exact prefixLift 1150116
  have htrace : WordTrace (prefixWord ++ tailWord_1150116) baseStart_1150116 baseEnd_1150116 := by
    simpa [prefixWord, tailWord_1150116, baseEnd_1150116] using wordTrace_append hprefix tailTrace_1150116
  have hstable : (prefixWord ++ tailWord_1150116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150116).length < 2 ^ (prefixWord ++ tailWord_1150116).sum := by decide
  have hdescent : baseEnd_1150116 < baseStart_1150116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150186 : List Nat := [3, 1, 3, 1, 1, 4, 2, 3, 5]
def baseStart_1150186 : Nat := 118140960795 + 1150186 * 2 ^ 59
def prefixEnd_1150186 : Nat := 4983230072969 + 3 ^ 40 * 1150186 * 2
def baseEnd_1150186 : Nat := 65622028896926902853933

theorem tailTrace_1150186 : CollatzResearch.WordTrace tailWord_1150186 prefixEnd_1150186 65622028896926902853933 := by
  unfold tailWord_1150186
  simp only [CollatzResearch.WordTrace]
  refine ⟨10487682452770008243707603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27967153207386688649886941 10487682452770008243707603)
  ·
    refine ⟨15731523679155012365561405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10487682452770008243707603 15731523679155012365561405)
    ·
      refine ⟨5899321379683129637085527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15731523679155012365561405 5899321379683129637085527)
      ·
        refine ⟨8848982069524694455628291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5899321379683129637085527 8848982069524694455628291)
        ·
          refine ⟨13273473104287041683442437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8848982069524694455628291 13273473104287041683442437)
          ·
            refine ⟨2488776207053820315645457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13273473104287041683442437 2488776207053820315645457)
            ·
              refine ⟨1866582155290365236734093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2488776207053820315645457 1866582155290365236734093)
              ·
                refine ⟨699968308233886963775285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1866582155290365236734093 699968308233886963775285)
                ·
                  refine ⟨65622028896926902853933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 699968308233886963775285 65622028896926902853933)
                  ·
                    rfl

theorem cell23_1150186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_1150186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150186 prefixEnd_1150186 := by exact prefixLift 1150186
  have htrace : WordTrace (prefixWord ++ tailWord_1150186) baseStart_1150186 baseEnd_1150186 := by
    simpa [prefixWord, tailWord_1150186, baseEnd_1150186] using wordTrace_append hprefix tailTrace_1150186
  have hstable : (prefixWord ++ tailWord_1150186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150186).length < 2 ^ (prefixWord ++ tailWord_1150186).sum := by decide
  have hdescent : baseEnd_1150186 < baseStart_1150186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150253 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1150253 : Nat := 118140960795 + 1150253 * 2 ^ 59
def prefixEnd_1150253 : Nat := 4983230072969 + 3 ^ 40 * 1150253 * 2
def baseEnd_1150253 : Nat := 590632663276193363547589

theorem tailTrace_1150253 : CollatzResearch.WordTrace tailWord_1150253 prefixEnd_1150253 590632663276193363547589 := by
  unfold tailWord_1150253
  simp only [CollatzResearch.WordTrace]
  refine ⟨41953173501837303417519413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27968782334558202278346275 41953173501837303417519413)
  ·
    refine ⟨3933110015797247195392445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41953173501837303417519413 3933110015797247195392445)
    ·
      refine ⟨1474916255923967698272167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3933110015797247195392445 1474916255923967698272167)
      ·
        refine ⟨2212374383885951547408251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474916255923967698272167 2212374383885951547408251)
        ·
          refine ⟨3318561575828927321112377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212374383885951547408251 3318561575828927321112377)
          ·
            refine ⟨2488921181871695490834283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3318561575828927321112377 2488921181871695490834283)
            ·
              refine ⟨3733381772807543236251425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488921181871695490834283 3733381772807543236251425)
              ·
                refine ⟨2800036329605657427188569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3733381772807543236251425 2800036329605657427188569)
                ·
                  refine ⟨2100027247204243070391427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2800036329605657427188569 2100027247204243070391427)
                  ·
                    refine ⟨3150040870806364605587141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2100027247204243070391427 3150040870806364605587141)
                    ·
                      refine ⟨590632663276193363547589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3150040870806364605587141 590632663276193363547589)
                      ·
                        rfl

theorem cell23_1150253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1150253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150253 prefixEnd_1150253 := by exact prefixLift 1150253
  have htrace : WordTrace (prefixWord ++ tailWord_1150253) baseStart_1150253 baseEnd_1150253 := by
    simpa [prefixWord, tailWord_1150253, baseEnd_1150253] using wordTrace_append hprefix tailTrace_1150253
  have hstable : (prefixWord ++ tailWord_1150253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150253).length < 2 ^ (prefixWord ++ tailWord_1150253).sum := by decide
  have hdescent : baseEnd_1150253 < baseStart_1150253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150286 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_1150286 : Nat := 118140960795 + 1150286 * 2 ^ 59
def prefixEnd_1150286 : Nat := 4983230072969 + 3 ^ 40 * 1150286 * 2
def baseEnd_1150286 : Nat := 590649608137791734434937

theorem tailTrace_1150286 : CollatzResearch.WordTrace tailWord_1150286 prefixEnd_1150286 590649608137791734434937 := by
  unfold tailWord_1150286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5244297138839718756683839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27969584740478500035647141 5244297138839718756683839)
  ·
    refine ⟨7866445708259578135025759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5244297138839718756683839 7866445708259578135025759)
    ·
      refine ⟨11799668562389367202538639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7866445708259578135025759 11799668562389367202538639)
      ·
        refine ⟨17699502843584050803807959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11799668562389367202538639 17699502843584050803807959)
        ·
          refine ⟨26549254265376076205711939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17699502843584050803807959 26549254265376076205711939)
          ·
            refine ⟨39823881398064114308567909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26549254265376076205711939 39823881398064114308567909)
            ·
              refine ⟨7466977762137021432856483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39823881398064114308567909 7466977762137021432856483)
              ·
                refine ⟨11200466643205532149284725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7466977762137021432856483 11200466643205532149284725)
                ·
                  refine ⟨1050043747800518638995443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11200466643205532149284725 1050043747800518638995443)
                  ·
                    refine ⟨1575065621700777958493165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1050043747800518638995443 1575065621700777958493165)
                    ·
                      refine ⟨590649608137791734434937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1575065621700777958493165 590649608137791734434937)
                      ·
                        rfl

theorem cell23_1150286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_1150286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150286 prefixEnd_1150286 := by exact prefixLift 1150286
  have htrace : WordTrace (prefixWord ++ tailWord_1150286) baseStart_1150286 baseEnd_1150286 := by
    simpa [prefixWord, tailWord_1150286, baseEnd_1150286] using wordTrace_append hprefix tailTrace_1150286
  have hstable : (prefixWord ++ tailWord_1150286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150286).length < 2 ^ (prefixWord ++ tailWord_1150286).sum := by decide
  have hdescent : baseEnd_1150286 < baseStart_1150286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150289 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 3, 5]
def baseStart_1150289 : Nat := 118140960795 + 1150289 * 2 ^ 59
def prefixEnd_1150289 : Nat := 4983230072969 + 3 ^ 40 * 1150289 * 2
def baseEnd_1150289 : Nat := 196883716193251740899141

theorem tailTrace_1150289 : CollatzResearch.WordTrace tailWord_1150289 prefixEnd_1150289 196883716193251740899141 := by
  unfold tailWord_1150289
  simp only [CollatzResearch.WordTrace]
  refine ⟨41954486529706881565829921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27969657686471254377219947 41954486529706881565829921)
  ·
    refine ⟨31465864897280161174372441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41954486529706881565829921 31465864897280161174372441)
    ·
      refine ⟨23599398672960120880779331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31465864897280161174372441 23599398672960120880779331)
      ·
        refine ⟨35399098009440181321168997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23599398672960120880779331 35399098009440181321168997)
        ·
          refine ⟨6637330876770033997719187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35399098009440181321168997 6637330876770033997719187)
          ·
            refine ⟨9955996315155050996578781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6637330876770033997719187 9955996315155050996578781)
            ·
              refine ⟨3733498618183144123717043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9955996315155050996578781 3733498618183144123717043)
              ·
                refine ⟨5600247927274716185575565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3733498618183144123717043 5600247927274716185575565)
                ·
                  refine ⟨2100092972728018569590837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5600247927274716185575565 2100092972728018569590837)
                  ·
                    refine ⟨196883716193251740899141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2100092972728018569590837 196883716193251740899141)
                    ·
                      rfl

theorem cell23_1150289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_1150289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150289 prefixEnd_1150289 := by exact prefixLift 1150289
  have htrace : WordTrace (prefixWord ++ tailWord_1150289) baseStart_1150289 baseEnd_1150289 := by
    simpa [prefixWord, tailWord_1150289, baseEnd_1150289] using wordTrace_append hprefix tailTrace_1150289
  have hstable : (prefixWord ++ tailWord_1150289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150289).length < 2 ^ (prefixWord ++ tailWord_1150289).sum := by decide
  have hdescent : baseEnd_1150289 < baseStart_1150289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150303 : List Nat := [1, 1, 2, 3, 1, 2, 1, 7, 1, 1, 3]
def baseStart_1150303 : Nat := 118140960795 + 1150303 * 2 ^ 59
def prefixEnd_1150303 : Nat := 4983230072969 + 3 ^ 40 * 1150303 * 2
def baseEnd_1150303 : Nat := 590658337308918167922359

theorem tailTrace_1150303 : CollatzResearch.WordTrace tailWord_1150303 prefixEnd_1150303 590658337308918167922359 := by
  unfold tailWord_1150303
  simp only [CollatzResearch.WordTrace]
  refine ⟨41954997151656161956839563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27969998101104107971226375 41954997151656161956839563)
  ·
    refine ⟨62932495727484242935259345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41954997151656161956839563 62932495727484242935259345)
    ·
      refine ⟨47199371795613182201444509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62932495727484242935259345 47199371795613182201444509)
      ·
        refine ⟨17699764423354943325541691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47199371795613182201444509 17699764423354943325541691)
        ·
          refine ⟨26549646635032414988312537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17699764423354943325541691 26549646635032414988312537)
          ·
            refine ⟨19912234976274311241234403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26549646635032414988312537 19912234976274311241234403)
            ·
              refine ⟨29868352464411466861851605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19912234976274311241234403 29868352464411466861851605)
              ·
                refine ⟨700039510884643754574647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29868352464411466861851605 700039510884643754574647)
                ·
                  refine ⟨1050059266326965631861971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700039510884643754574647 1050059266326965631861971)
                  ·
                    refine ⟨1575088899490448447792957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1050059266326965631861971 1575088899490448447792957)
                    ·
                      refine ⟨590658337308918167922359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1575088899490448447792957 590658337308918167922359)
                      ·
                        rfl

theorem cell23_1150303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_1150303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150303 prefixEnd_1150303 := by exact prefixLift 1150303
  have htrace : WordTrace (prefixWord ++ tailWord_1150303) baseStart_1150303 baseEnd_1150303 := by
    simpa [prefixWord, tailWord_1150303, baseEnd_1150303] using wordTrace_append hprefix tailTrace_1150303
  have hstable : (prefixWord ++ tailWord_1150303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150303).length < 2 ^ (prefixWord ++ tailWord_1150303).sum := by decide
  have hdescent : baseEnd_1150303 < baseStart_1150303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150314 : List Nat := [3, 1, 3, 3, 3, 1, 2, 2, 1, 4]
def baseStart_1150314 : Nat := 118140960795 + 1150314 * 2 ^ 59
def prefixEnd_1150314 : Nat := 4983230072969 + 3 ^ 40 * 1150314 * 2
def baseEnd_1150314 : Nat := 196887995198705874961603

theorem tailTrace_1150314 : CollatzResearch.WordTrace tailWord_1150314 prefixEnd_1150314 196887995198705874961603 := by
  unfold tailWord_1150314
  simp only [CollatzResearch.WordTrace]
  refine ⟨10488849588654077708872499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27970265569744207223659997 10488849588654077708872499)
  ·
    refine ⟨15733274382981116563308749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10488849588654077708872499 15733274382981116563308749)
    ·
      refine ⟨5899977893617918711240781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15733274382981116563308749 5899977893617918711240781)
      ·
        refine ⟨2212491710106719516715293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5899977893617918711240781 2212491710106719516715293)
        ·
          refine ⟨829684391290019818768235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2212491710106719516715293 829684391290019818768235)
          ·
            refine ⟨1244526586935029728152353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829684391290019818768235 1244526586935029728152353)
            ·
              refine ⟨933394940201272296114265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244526586935029728152353 933394940201272296114265)
              ·
                refine ⟨700046205150954222085699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933394940201272296114265 700046205150954222085699)
                ·
                  refine ⟨1050069307726431333128549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700046205150954222085699 1050069307726431333128549)
                  ·
                    refine ⟨196887995198705874961603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1050069307726431333128549 196887995198705874961603)
                    ·
                      rfl

theorem cell23_1150314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_1150314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150314 prefixEnd_1150314 := by exact prefixLift 1150314
  have htrace : WordTrace (prefixWord ++ tailWord_1150314) baseStart_1150314 baseEnd_1150314 := by
    simpa [prefixWord, tailWord_1150314, baseEnd_1150314] using wordTrace_append hprefix tailTrace_1150314
  have hstable : (prefixWord ++ tailWord_1150314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150314).length < 2 ^ (prefixWord ++ tailWord_1150314).sum := by decide
  have hdescent : baseEnd_1150314 < baseStart_1150314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150329 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 5]
def baseStart_1150329 : Nat := 118140960795 + 1150329 * 2 ^ 59
def prefixEnd_1150329 : Nat := 4983230072969 + 3 ^ 40 * 1150329 * 2
def baseEnd_1150329 : Nat := 590671687805935066197239

theorem tailTrace_1150329 : CollatzResearch.WordTrace tailWord_1150329 prefixEnd_1150329 590671687805935066197239 := by
  unfold tailWord_1150329
  simp only [CollatzResearch.WordTrace]
  refine ⟨41955945449561968397286041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27970630299707978931524027 41955945449561968397286041)
  ·
    refine ⟨31466959087171476297964531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41955945449561968397286041 31466959087171476297964531)
    ·
      refine ⟨47200438630757214446946797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31466959087171476297964531 47200438630757214446946797)
      ·
        refine ⟨17700164486533955417605049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47200438630757214446946797 17700164486533955417605049)
        ·
          refine ⟨13275123364900466563203787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17700164486533955417605049 13275123364900466563203787)
          ·
            refine ⟨19912685047350699844805681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13275123364900466563203787 19912685047350699844805681)
            ·
              refine ⟨14934513785513024883604261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19912685047350699844805681 14934513785513024883604261)
              ·
                refine ⟨2800221334783692165675799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14934513785513024883604261 2800221334783692165675799)
                ·
                  refine ⟨4200332002175538248513699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800221334783692165675799 4200332002175538248513699)
                  ·
                    refine ⟨6300498003263307372770549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4200332002175538248513699 6300498003263307372770549)
                    ·
                      refine ⟨590671687805935066197239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6300498003263307372770549 590671687805935066197239)
                      ·
                        rfl

theorem cell23_1150329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_1150329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150329 prefixEnd_1150329 := by exact prefixLift 1150329
  have htrace : WordTrace (prefixWord ++ tailWord_1150329) baseStart_1150329 baseEnd_1150329 := by
    simpa [prefixWord, tailWord_1150329, baseEnd_1150329] using wordTrace_append hprefix tailTrace_1150329
  have hstable : (prefixWord ++ tailWord_1150329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150329).length < 2 ^ (prefixWord ++ tailWord_1150329).sum := by decide
  have hdescent : baseEnd_1150329 < baseStart_1150329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150343 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 5, 2, 2]
def baseStart_1150343 : Nat := 118140960795 + 1150343 * 2 ^ 59
def prefixEnd_1150343 : Nat := 4983230072969 + 3 ^ 40 * 1150343 * 2
def baseEnd_1150343 : Nat := 590678876535098011422175

theorem tailTrace_1150343 : CollatzResearch.WordTrace tailWord_1150343 prefixEnd_1150343 590678876535098011422175 := by
  unfold tailWord_1150343
  simp only [CollatzResearch.WordTrace]
  refine ⟨41956456071511248788295683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27970970714340832525530455 41956456071511248788295683)
  ·
    refine ⟨62934684107266873182443525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41956456071511248788295683 62934684107266873182443525)
    ·
      refine ⟨11800253270112538721708161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62934684107266873182443525 11800253270112538721708161)
      ·
        refine ⟨8850189952584404041281121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11800253270112538721708161 8850189952584404041281121)
        ·
          refine ⟨6637642464438303030960841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8850189952584404041281121 6637642464438303030960841)
          ·
            refine ⟨4978231848328727273220631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6637642464438303030960841 4978231848328727273220631)
            ·
              refine ⟨7467347772493090909830947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978231848328727273220631 7467347772493090909830947)
              ·
                refine ⟨11201021658739636364746421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7467347772493090909830947 11201021658739636364746421)
                ·
                  refine ⟨1050095780506840909194977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11201021658739636364746421 1050095780506840909194977)
                  ·
                    refine ⟨787571835380130681896233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1050095780506840909194977 787571835380130681896233)
                    ·
                      refine ⟨590678876535098011422175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 787571835380130681896233 590678876535098011422175)
                      ·
                        rfl

theorem cell23_1150343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_1150343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150343 prefixEnd_1150343 := by exact prefixLift 1150343
  have htrace : WordTrace (prefixWord ++ tailWord_1150343) baseStart_1150343 baseEnd_1150343 := by
    simpa [prefixWord, tailWord_1150343, baseEnd_1150343] using wordTrace_append hprefix tailTrace_1150343
  have hstable : (prefixWord ++ tailWord_1150343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150343).length < 2 ^ (prefixWord ++ tailWord_1150343).sum := by decide
  have hdescent : baseEnd_1150343 < baseStart_1150343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150354 : List Nat := [3, 2, 3, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1150354 : Nat := 118140960795 + 1150354 * 2 ^ 59
def prefixEnd_1150354 : Nat := 4983230072969 + 3 ^ 40 * 1150354 * 2
def baseEnd_1150354 : Nat := 590684524822297468384625

theorem tailTrace_1150354 : CollatzResearch.WordTrace tailWord_1150354 prefixEnd_1150354 590684524822297468384625 := by
  unfold tailWord_1150354
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489214318617849416736529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27971238182980931777964077 10489214318617849416736529)
  ·
    refine ⟨7866910738963387062552397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10489214318617849416736529 7866910738963387062552397)
    ·
      refine ⟨2950091527111270148457149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7866910738963387062552397 2950091527111270148457149)
      ·
        refine ⟨1106284322666726305671431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2950091527111270148457149 1106284322666726305671431)
        ·
          refine ⟨1659426484000089458507147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106284322666726305671431 1659426484000089458507147)
          ·
            refine ⟨2489139726000134187760721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659426484000089458507147 2489139726000134187760721)
            ·
              refine ⟨1866854794500100640820541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2489139726000134187760721 1866854794500100640820541)
              ·
                refine ⟨700070547937537740307703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1866854794500100640820541 700070547937537740307703)
                ·
                  refine ⟨1050105821906306610461555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700070547937537740307703 1050105821906306610461555)
                  ·
                    refine ⟨1575158732859459915692333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1050105821906306610461555 1575158732859459915692333)
                    ·
                      refine ⟨590684524822297468384625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1575158732859459915692333 590684524822297468384625)
                      ·
                        rfl

theorem cell23_1150354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1150354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150354 prefixEnd_1150354 := by exact prefixLift 1150354
  have htrace : WordTrace (prefixWord ++ tailWord_1150354) baseStart_1150354 baseEnd_1150354 := by
    simpa [prefixWord, tailWord_1150354, baseEnd_1150354] using wordTrace_append hprefix tailTrace_1150354
  have hstable : (prefixWord ++ tailWord_1150354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150354).length < 2 ^ (prefixWord ++ tailWord_1150354).sum := by decide
  have hdescent : baseEnd_1150354 < baseStart_1150354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150370 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1150370 : Nat := 118140960795 + 1150370 * 2 ^ 59
def prefixEnd_1150370 : Nat := 4983230072969 + 3 ^ 40 * 1150370 * 2
def baseEnd_1150370 : Nat := 196897580170923135261517

theorem tailTrace_1150370 : CollatzResearch.WordTrace tailWord_1150370 prefixEnd_1150370 196897580170923135261517 := by
  unfold tailWord_1150370
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489360210603358099882141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27971627228275621599685709 10489360210603358099882141)
  ·
    refine ⟨3933510078976259287455803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10489360210603358099882141 3933510078976259287455803)
    ·
      refine ⟨5900265118464388931183705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3933510078976259287455803 5900265118464388931183705)
      ·
        refine ⟨4425198838848291698387779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5900265118464388931183705 4425198838848291698387779)
        ·
          refine ⟨6637798258272437547581669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4425198838848291698387779 6637798258272437547581669)
          ·
            refine ⟨1244587173426082040171563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6637798258272437547581669 1244587173426082040171563)
            ·
              refine ⟨1866880760139123060257345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244587173426082040171563 1866880760139123060257345)
              ·
                refine ⟨1400160570104342295193009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1866880760139123060257345 1400160570104342295193009)
                ·
                  refine ⟨1050120427578256721394757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1400160570104342295193009 1050120427578256721394757)
                  ·
                    refine ⟨196897580170923135261517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1050120427578256721394757 196897580170923135261517)
                    ·
                      rfl

theorem cell23_1150370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1150370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150370 prefixEnd_1150370 := by exact prefixLift 1150370
  have htrace : WordTrace (prefixWord ++ tailWord_1150370) baseStart_1150370 baseEnd_1150370 := by
    simpa [prefixWord, tailWord_1150370, baseEnd_1150370] using wordTrace_append hprefix tailTrace_1150370
  have hstable : (prefixWord ++ tailWord_1150370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150370).length < 2 ^ (prefixWord ++ tailWord_1150370).sum := by decide
  have hdescent : baseEnd_1150370 < baseStart_1150370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150386 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2]
def baseStart_1150386 : Nat := 118140960795 + 1150386 * 2 ^ 59
def prefixEnd_1150386 : Nat := 4983230072969 + 3 ^ 40 * 1150386 * 2
def baseEnd_1150386 : Nat := 590700956203241343184477

theorem tailTrace_1150386 : CollatzResearch.WordTrace tailWord_1150386 prefixEnd_1150386 590700956203241343184477 := by
  unfold tailWord_1150386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489506102588866783027753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27972016273570311421407341 10489506102588866783027753)
  ·
    refine ⟨7867129576941650087270815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10489506102588866783027753 7867129576941650087270815)
    ·
      refine ⟨11800694365412475130906223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7867129576941650087270815 11800694365412475130906223)
      ·
        refine ⟨17701041548118712696359335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11800694365412475130906223 17701041548118712696359335)
        ·
          refine ⟨26551562322178069044539003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17701041548118712696359335 26551562322178069044539003)
          ·
            refine ⟨39827343483267103566808505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26551562322178069044539003 39827343483267103566808505)
            ·
              refine ⟨29870507612450327675106379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39827343483267103566808505 29870507612450327675106379)
              ·
                refine ⟨44805761418675491512659569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29870507612450327675106379 44805761418675491512659569)
                ·
                  refine ⟨33604321064006618634494677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44805761418675491512659569 33604321064006618634494677)
                  ·
                    refine ⟨787601274937655124245969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33604321064006618634494677 787601274937655124245969)
                    ·
                      refine ⟨590700956203241343184477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 787601274937655124245969 590700956203241343184477)
                      ·
                        rfl

theorem cell23_1150386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_1150386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150386 prefixEnd_1150386 := by exact prefixLift 1150386
  have htrace : WordTrace (prefixWord ++ tailWord_1150386) baseStart_1150386 baseEnd_1150386 := by
    simpa [prefixWord, tailWord_1150386, baseEnd_1150386] using wordTrace_append hprefix tailTrace_1150386
  have hstable : (prefixWord ++ tailWord_1150386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150386).length < 2 ^ (prefixWord ++ tailWord_1150386).sum := by decide
  have hdescent : baseEnd_1150386 < baseStart_1150386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150399 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 4]
def baseStart_1150399 : Nat := 118140960795 + 1150399 * 2 ^ 59
def prefixEnd_1150399 : Nat := 4983230072969 + 3 ^ 40 * 1150399 * 2
def baseEnd_1150399 : Nat := 590707631451749792321917

theorem tailTrace_1150399 : CollatzResearch.WordTrace tailWord_1150399 prefixEnd_1150399 590707631451749792321917 := by
  unfold tailWord_1150399
  simp only [CollatzResearch.WordTrace]
  refine ⟨41958498559308370352334251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27972332372872246901556167 41958498559308370352334251)
  ·
    refine ⟨62937747838962555528501377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41958498559308370352334251 62937747838962555528501377)
    ·
      refine ⟨47203310879221916646376033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62937747838962555528501377 47203310879221916646376033)
      ·
        refine ⟨35402483159416437484782025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47203310879221916646376033 35402483159416437484782025)
        ·
          refine ⟨26551862369562328113586519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35402483159416437484782025 26551862369562328113586519)
          ·
            refine ⟨39827793554343492170379779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26551862369562328113586519 39827793554343492170379779)
            ·
              refine ⟨59741690331515238255569669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39827793554343492170379779 59741690331515238255569669)
              ·
                refine ⟨11201566937159107172919313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59741690331515238255569669 11201566937159107172919313)
                ·
                  refine ⟨8401175202869330379689485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11201566937159107172919313 8401175202869330379689485)
                  ·
                    refine ⟨3150440701075998892383557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8401175202869330379689485 3150440701075998892383557)
                    ·
                      refine ⟨590707631451749792321917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3150440701075998892383557 590707631451749792321917)
                      ·
                        rfl

theorem cell23_1150399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_1150399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150399 prefixEnd_1150399 := by exact prefixLift 1150399
  have htrace : WordTrace (prefixWord ++ tailWord_1150399) baseStart_1150399 baseEnd_1150399 := by
    simpa [prefixWord, tailWord_1150399, baseEnd_1150399] using wordTrace_append hprefix tailTrace_1150399
  have hstable : (prefixWord ++ tailWord_1150399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150399).length < 2 ^ (prefixWord ++ tailWord_1150399).sum := by decide
  have hdescent : baseEnd_1150399 < baseStart_1150399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150403 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 1, 3, 2]
def baseStart_1150403 : Nat := 118140960795 + 1150403 * 2 ^ 59
def prefixEnd_1150403 : Nat := 4983230072969 + 3 ^ 40 * 1150403 * 2
def baseEnd_1150403 : Nat := 590709685374367776671899

theorem tailTrace_1150403 : CollatzResearch.WordTrace tailWord_1150403 prefixEnd_1150403 590709685374367776671899 := by
  unfold tailWord_1150403
  simp only [CollatzResearch.WordTrace]
  refine ⟨41958644451293879035479863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27972429634195919356986575 41958644451293879035479863)
  ·
    refine ⟨62937966676940818553219795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41958644451293879035479863 62937966676940818553219795)
    ·
      refine ⟨94406950015411227829829693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62937966676940818553219795 94406950015411227829829693)
      ·
        refine ⟨35402606255779210436186135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94406950015411227829829693 35402606255779210436186135)
        ·
          refine ⟨53103909383668815654279203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35402606255779210436186135 53103909383668815654279203)
          ·
            refine ⟨79655864075503223481418805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53103909383668815654279203 79655864075503223481418805)
            ·
              refine ⟨7467737257078427201383013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79655864075503223481418805 7467737257078427201383013)
              ·
                refine ⟨1400200735702205100259315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7467737257078427201383013 1400200735702205100259315)
                ·
                  refine ⟨2100301103553307650388973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400200735702205100259315 2100301103553307650388973)
                  ·
                    refine ⟨787612913832490368895865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2100301103553307650388973 787612913832490368895865)
                    ·
                      refine ⟨590709685374367776671899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 787612913832490368895865 590709685374367776671899)
                      ·
                        rfl

theorem cell23_1150403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 3, 2].length) (baseStart_1150403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150403 prefixEnd_1150403 := by exact prefixLift 1150403
  have htrace : WordTrace (prefixWord ++ tailWord_1150403) baseStart_1150403 baseEnd_1150403 := by
    simpa [prefixWord, tailWord_1150403, baseEnd_1150403] using wordTrace_append hprefix tailTrace_1150403
  have hstable : (prefixWord ++ tailWord_1150403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150403).length < 2 ^ (prefixWord ++ tailWord_1150403).sum := by decide
  have hdescent : baseEnd_1150403 < baseStart_1150403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150446 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1150446 : Nat := 118140960795 + 1150446 * 2 ^ 59
def prefixEnd_1150446 : Nat := 4983230072969 + 3 ^ 40 * 1150446 * 2
def baseEnd_1150446 : Nat := 590731765042511108434201

theorem tailTrace_1150446 : CollatzResearch.WordTrace tailWord_1150446 prefixEnd_1150446 590731765042511108434201 := by
  unfold tailWord_1150446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5245026598767262172411899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27973475193425398252863461 5245026598767262172411899)
  ·
    refine ⟨7867539898150893258617849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5245026598767262172411899 7867539898150893258617849)
    ·
      refine ⟨5900654923613169943963387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7867539898150893258617849 5900654923613169943963387)
      ·
        refine ⟨8850982385419754915945081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5900654923613169943963387 8850982385419754915945081)
        ·
          refine ⟨6638236789064816186958811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8850982385419754915945081 6638236789064816186958811)
          ·
            refine ⟨9957355183597224280438217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6638236789064816186958811 9957355183597224280438217)
            ·
              refine ⟨7468016387697918210328663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9957355183597224280438217 7468016387697918210328663)
              ·
                refine ⟨11202024581546877315492995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7468016387697918210328663 11202024581546877315492995)
                ·
                  refine ⟨16803036872320315973239493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11202024581546877315492995 16803036872320315973239493)
                  ·
                    refine ⟨3150569413560059244982405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16803036872320315973239493 3150569413560059244982405)
                    ·
                      refine ⟨590731765042511108434201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3150569413560059244982405 590731765042511108434201)
                      ·
                        rfl

theorem cell23_1150446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1150446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150446 prefixEnd_1150446 := by exact prefixLift 1150446
  have htrace : WordTrace (prefixWord ++ tailWord_1150446) baseStart_1150446 baseEnd_1150446 := by
    simpa [prefixWord, tailWord_1150446, baseEnd_1150446] using wordTrace_append hprefix tailTrace_1150446
  have hstable : (prefixWord ++ tailWord_1150446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150446).length < 2 ^ (prefixWord ++ tailWord_1150446).sum := by decide
  have hdescent : baseEnd_1150446 < baseStart_1150446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150453 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1150453 : Nat := 118140960795 + 1150453 * 2 ^ 59
def prefixEnd_1150453 : Nat := 4983230072969 + 3 ^ 40 * 1150453 * 2
def baseEnd_1150453 : Nat := 590735359407092581046669

theorem tailTrace_1150453 : CollatzResearch.WordTrace tailWord_1150453 prefixEnd_1150453 590735359407092581046669 := by
  unfold tailWord_1150453
  simp only [CollatzResearch.WordTrace]
  refine ⟨41960468101112737574800013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27973645400741825049866675 41960468101112737574800013)
  ·
    refine ⟨15735175537917276590550005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41960468101112737574800013 15735175537917276590550005)
    ·
      refine ⟨1475172706679744680364063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15735175537917276590550005 1475172706679744680364063)
      ·
        refine ⟨2212759060019617020546095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475172706679744680364063 2212759060019617020546095)
        ·
          refine ⟨3319138590029425530819143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212759060019617020546095 3319138590029425530819143)
          ·
            refine ⟨4978707885044138296228715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3319138590029425530819143 4978707885044138296228715)
            ·
              refine ⟨7468061827566207444343073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978707885044138296228715 7468061827566207444343073)
              ·
                refine ⟨5601046370674655583257305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7468061827566207444343073 5601046370674655583257305)
                ·
                  refine ⟨4200784778005991687442979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5601046370674655583257305 4200784778005991687442979)
                  ·
                    refine ⟨6301177167008987531164469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4200784778005991687442979 6301177167008987531164469)
                    ·
                      refine ⟨590735359407092581046669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6301177167008987531164469 590735359407092581046669)
                      ·
                        rfl

theorem cell23_1150453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1150453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150453 prefixEnd_1150453 := by exact prefixLift 1150453
  have htrace : WordTrace (prefixWord ++ tailWord_1150453) baseStart_1150453 baseEnd_1150453 := by
    simpa [prefixWord, tailWord_1150453, baseEnd_1150453] using wordTrace_append hprefix tailTrace_1150453
  have hstable : (prefixWord ++ tailWord_1150453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150453).length < 2 ^ (prefixWord ++ tailWord_1150453).sum := by decide
  have hdescent : baseEnd_1150453 < baseStart_1150453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150489 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_1150489 : Nat := 118140960795 + 1150489 * 2 ^ 59
def prefixEnd_1150489 : Nat := 4983230072969 + 3 ^ 40 * 1150489 * 2
def baseEnd_1150489 : Nat := 590753844710654440196503

theorem tailTrace_1150489 : CollatzResearch.WordTrace tailWord_1150489 prefixEnd_1150489 590753844710654440196503 := by
  unfold tailWord_1150489
  simp only [CollatzResearch.WordTrace]
  refine ⟨41961781128982315723110521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27974520752654877148740347 41961781128982315723110521)
  ·
    refine ⟨31471335846736736792332891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41961781128982315723110521 31471335846736736792332891)
    ·
      refine ⟨47207003770105105188499337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31471335846736736792332891 47207003770105105188499337)
      ·
        refine ⟨35405252827578828891374503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47207003770105105188499337 35405252827578828891374503)
        ·
          refine ⟨53107879241368243337061755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35405252827578828891374503 53107879241368243337061755)
          ·
            refine ⟨79661818862052365005592633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53107879241368243337061755 79661818862052365005592633)
            ·
              refine ⟨59746364146539273754194475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79661818862052365005592633 59746364146539273754194475)
              ·
                refine ⟨89619546219808910631291713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59746364146539273754194475 89619546219808910631291713)
                ·
                  refine ⟨67214659664856682973468785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89619546219808910631291713 67214659664856682973468785)
                  ·
                    refine ⟨50410994748642512230101589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67214659664856682973468785 50410994748642512230101589)
                    ·
                      refine ⟨590753844710654440196503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 50410994748642512230101589 590753844710654440196503)
                      ·
                        rfl

theorem cell23_1150489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_1150489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150489 prefixEnd_1150489 := by exact prefixLift 1150489
  have htrace : WordTrace (prefixWord ++ tailWord_1150489) baseStart_1150489 baseEnd_1150489 := by
    simpa [prefixWord, tailWord_1150489, baseEnd_1150489] using wordTrace_append hprefix tailTrace_1150489
  have hstable : (prefixWord ++ tailWord_1150489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150489).length < 2 ^ (prefixWord ++ tailWord_1150489).sum := by decide
  have hdescent : baseEnd_1150489 < baseStart_1150489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150493 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_1150493 : Nat := 118140960795 + 1150493 * 2 ^ 59
def prefixEnd_1150493 : Nat := 4983230072969 + 3 ^ 40 * 1150493 * 2
def baseEnd_1150493 : Nat := 590755898633272424546485

theorem tailTrace_1150493 : CollatzResearch.WordTrace tailWord_1150493 prefixEnd_1150493 590755898633272424546485 := by
  unfold tailWord_1150493
  simp only [CollatzResearch.WordTrace]
  refine ⟨41961927020967824406256133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27974618013978549604170755 41961927020967824406256133)
  ·
    refine ⟨7867861316431467076173025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41961927020967824406256133 7867861316431467076173025)
    ·
      refine ⟨5900895987323600307129769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7867861316431467076173025 5900895987323600307129769)
      ·
        refine ⟨4425671990492700230347327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5900895987323600307129769 4425671990492700230347327)
        ·
          refine ⟨6638507985739050345520991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4425671990492700230347327 6638507985739050345520991)
          ·
            refine ⟨9957761978608575518281487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6638507985739050345520991 9957761978608575518281487)
            ·
              refine ⟨14936642967912863277422231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9957761978608575518281487 14936642967912863277422231)
              ·
                refine ⟨22404964451869294916133347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14936642967912863277422231 22404964451869294916133347)
                ·
                  refine ⟨33607446677803942374200021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22404964451869294916133347 33607446677803942374200021)
                  ·
                    refine ⟨787674531511029899395313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33607446677803942374200021 787674531511029899395313)
                    ·
                      refine ⟨590755898633272424546485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 787674531511029899395313 590755898633272424546485)
                      ·
                        rfl

theorem cell23_1150493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_1150493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150493 prefixEnd_1150493 := by exact prefixLift 1150493
  have htrace : WordTrace (prefixWord ++ tailWord_1150493) baseStart_1150493 baseEnd_1150493 := by
    simpa [prefixWord, tailWord_1150493, baseEnd_1150493] using wordTrace_append hprefix tailTrace_1150493
  have hstable : (prefixWord ++ tailWord_1150493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150493).length < 2 ^ (prefixWord ++ tailWord_1150493).sum := by decide
  have hdescent : baseEnd_1150493 < baseStart_1150493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150643 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 4]
def baseStart_1150643 : Nat := 118140960795 + 1150643 * 2 ^ 59
def prefixEnd_1150643 : Nat := 4983230072969 + 3 ^ 40 * 1150643 * 2
def baseEnd_1150643 : Nat := 590832920731446837670795

theorem tailTrace_1150643 : CollatzResearch.WordTrace tailWord_1150643 prefixEnd_1150643 590832920731446837670795 := by
  unfold tailWord_1150643
  simp only [CollatzResearch.WordTrace]
  refine ⟨41967397970424400024216583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27978265313616266682811055 41967397970424400024216583)
  ·
    refine ⟨62951096955636600036324875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41967397970424400024216583 62951096955636600036324875)
    ·
      refine ⟨94426645433454900054487313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62951096955636600036324875 94426645433454900054487313)
      ·
        refine ⟨70819984075091175040865485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94426645433454900054487313 70819984075091175040865485)
        ·
          refine ⟨26557494028159190640324557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70819984075091175040865485 26557494028159190640324557)
          ·
            refine ⟨9959060260559696490121709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26557494028159190640324557 9959060260559696490121709)
            ·
              refine ⟨3734647597709886183795641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9959060260559696490121709 3734647597709886183795641)
              ·
                refine ⟨2800985698282414637846731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3734647597709886183795641 2800985698282414637846731)
                ·
                  refine ⟨4201478547423621956770097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800985698282414637846731 4201478547423621956770097)
                  ·
                    refine ⟨3151108910567716467577573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4201478547423621956770097 3151108910567716467577573)
                    ·
                      refine ⟨590832920731446837670795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3151108910567716467577573 590832920731446837670795)
                      ·
                        rfl

theorem cell23_1150643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_1150643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150643 prefixEnd_1150643 := by exact prefixLift 1150643
  have htrace : WordTrace (prefixWord ++ tailWord_1150643) baseStart_1150643 baseEnd_1150643 := by
    simpa [prefixWord, tailWord_1150643, baseEnd_1150643] using wordTrace_append hprefix tailTrace_1150643
  have hstable : (prefixWord ++ tailWord_1150643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150643).length < 2 ^ (prefixWord ++ tailWord_1150643).sum := by decide
  have hdescent : baseEnd_1150643 < baseStart_1150643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150647 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 1, 1, 4]
def baseStart_1150647 : Nat := 118140960795 + 1150647 * 2 ^ 59
def prefixEnd_1150647 : Nat := 4983230072969 + 3 ^ 40 * 1150647 * 2
def baseEnd_1150647 : Nat := 590834974654064822020777

theorem tailTrace_1150647 : CollatzResearch.WordTrace tailWord_1150647 prefixEnd_1150647 590834974654064822020777 := by
  unfold tailWord_1150647
  simp only [CollatzResearch.WordTrace]
  refine ⟨41967543862409908707362195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27978362574939939138241463 41967543862409908707362195)
  ·
    refine ⟨62951315793614863061043293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41967543862409908707362195 62951315793614863061043293)
    ·
      refine ⟨23606743422605573647891235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62951315793614863061043293 23606743422605573647891235)
      ·
        refine ⟨35410115133908360471836853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23606743422605573647891235 35410115133908360471836853)
        ·
          refine ⟨3319698293803908794234705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35410115133908360471836853 3319698293803908794234705)
          ·
            refine ⟨2489773720352931595676029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3319698293803908794234705 2489773720352931595676029)
            ·
              refine ⟨933665145132349348378511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2489773720352931595676029 933665145132349348378511)
              ·
                refine ⟨1400497717698524022567767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933665145132349348378511 1400497717698524022567767)
                ·
                  refine ⟨2100746576547786033851651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400497717698524022567767 2100746576547786033851651)
                  ·
                    refine ⟨3151119864821679050777477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2100746576547786033851651 3151119864821679050777477)
                    ·
                      refine ⟨590834974654064822020777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3151119864821679050777477 590834974654064822020777)
                      ·
                        rfl

theorem cell23_1150647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 1, 1, 4].length) (baseStart_1150647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150647 prefixEnd_1150647 := by exact prefixLift 1150647
  have htrace : WordTrace (prefixWord ++ tailWord_1150647) baseStart_1150647 baseEnd_1150647 := by
    simpa [prefixWord, tailWord_1150647, baseEnd_1150647] using wordTrace_append hprefix tailTrace_1150647
  have hstable : (prefixWord ++ tailWord_1150647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150647).length < 2 ^ (prefixWord ++ tailWord_1150647).sum := by decide
  have hdescent : baseEnd_1150647 < baseStart_1150647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150650 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5]
def baseStart_1150650 : Nat := 118140960795 + 1150650 * 2 ^ 59
def prefixEnd_1150650 : Nat := 4983230072969 + 3 ^ 40 * 1150650 * 2
def baseEnd_1150650 : Nat := 590836515096028310283263

theorem tailTrace_1150650 : CollatzResearch.WordTrace tailWord_1150650 prefixEnd_1150650 590836515096028310283263 := by
  unfold tailWord_1150650
  simp only [CollatzResearch.WordTrace]
  refine ⟨10491913320349760054930351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27978435520932693479814269 10491913320349760054930351)
  ·
    refine ⟨15737869980524640082395527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10491913320349760054930351 15737869980524640082395527)
    ·
      refine ⟨23606804970786960123593291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15737869980524640082395527 23606804970786960123593291)
      ·
        refine ⟨35410207456180440185389937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23606804970786960123593291 35410207456180440185389937)
        ·
          refine ⟨26557655592135330139042453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35410207456180440185389937 26557655592135330139042453)
          ·
            refine ⟨1244890105881343600267615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26557655592135330139042453 1244890105881343600267615)
            ·
              refine ⟨1867335158822015400401423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244890105881343600267615 1867335158822015400401423)
              ·
                refine ⟨2801002738233023100602135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867335158822015400401423 2801002738233023100602135)
                ·
                  refine ⟨4201504107349534650903203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801002738233023100602135 4201504107349534650903203)
                  ·
                    refine ⟨6302256161024301976354805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4201504107349534650903203 6302256161024301976354805)
                    ·
                      refine ⟨590836515096028310283263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6302256161024301976354805 590836515096028310283263)
                      ·
                        rfl

theorem cell23_1150650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_1150650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150650 prefixEnd_1150650 := by exact prefixLift 1150650
  have htrace : WordTrace (prefixWord ++ tailWord_1150650) baseStart_1150650 baseEnd_1150650 := by
    simpa [prefixWord, tailWord_1150650, baseEnd_1150650] using wordTrace_append hprefix tailTrace_1150650
  have hstable : (prefixWord ++ tailWord_1150650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150650).length < 2 ^ (prefixWord ++ tailWord_1150650).sum := by decide
  have hdescent : baseEnd_1150650 < baseStart_1150650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150663 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_1150663 : Nat := 118140960795 + 1150663 * 2 ^ 59
def prefixEnd_1150663 : Nat := 4983230072969 + 3 ^ 40 * 1150663 * 2
def baseEnd_1150663 : Nat := 590843190344536759420703

theorem tailTrace_1150663 : CollatzResearch.WordTrace tailWord_1150663 prefixEnd_1150663 590843190344536759420703 := by
  unfold tailWord_1150663
  simp only [CollatzResearch.WordTrace]
  refine ⟨41968127430351943439944643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27978751620234628959963095 41968127430351943439944643)
  ·
    refine ⟨62952191145527915159916965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41968127430351943439944643 62952191145527915159916965)
    ·
      refine ⟨11803535839786484092484431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62952191145527915159916965 11803535839786484092484431)
      ·
        refine ⟨17705303759679726138726647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11803535839786484092484431 17705303759679726138726647)
        ·
          refine ⟨26557955639519589208089971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17705303759679726138726647 26557955639519589208089971)
          ·
            refine ⟨39836933459279383812134957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26557955639519589208089971 39836933459279383812134957)
            ·
              refine ⟨14938850047229768929550609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39836933459279383812134957 14938850047229768929550609)
              ·
                refine ⟨11204137535422326697162957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14938850047229768929550609 11204137535422326697162957)
                ·
                  refine ⟨4201551575783372511436109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11204137535422326697162957 4201551575783372511436109)
                  ·
                    refine ⟨1575581840918764691788541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4201551575783372511436109 1575581840918764691788541)
                    ·
                      refine ⟨590843190344536759420703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1575581840918764691788541 590843190344536759420703)
                      ·
                        rfl

theorem cell23_1150663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_1150663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150663 prefixEnd_1150663 := by exact prefixLift 1150663
  have htrace : WordTrace (prefixWord ++ tailWord_1150663) baseStart_1150663 baseEnd_1150663 := by
    simpa [prefixWord, tailWord_1150663, baseEnd_1150663] using wordTrace_append hprefix tailTrace_1150663
  have hstable : (prefixWord ++ tailWord_1150663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150663).length < 2 ^ (prefixWord ++ tailWord_1150663).sum := by decide
  have hdescent : baseEnd_1150663 < baseStart_1150663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150664 : List Nat := [2, 1, 3, 1, 2, 2, 3, 4, 1, 2, 2]
def baseStart_1150664 : Nat := 118140960795 + 1150664 * 2 ^ 59
def prefixEnd_1150664 : Nat := 4983230072969 + 3 ^ 40 * 1150664 * 2
def baseEnd_1150664 : Nat := 590843703825191255508199

theorem tailTrace_1150664 : CollatzResearch.WordTrace tailWord_1150664 prefixEnd_1150664 590843703825191255508199 := by
  unfold tailWord_1150664
  simp only [CollatzResearch.WordTrace]
  refine ⟨20984081951674160305365523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27978775935565547073820697 20984081951674160305365523)
  ·
    refine ⟨31476122927511240458048285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20984081951674160305365523 31476122927511240458048285)
    ·
      refine ⟨11803546097816715171768107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31476122927511240458048285 11803546097816715171768107)
      ·
        refine ⟨17705319146725072757652161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11803546097816715171768107 17705319146725072757652161)
        ·
          refine ⟨13278989360043804568239121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17705319146725072757652161 13278989360043804568239121)
          ·
            refine ⟨9959242020032853426179341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13278989360043804568239121 9959242020032853426179341)
            ·
              refine ⟨3734715757512320034817253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9959242020032853426179341 3734715757512320034817253)
              ·
                refine ⟨700259204533560006528235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3734715757512320034817253 700259204533560006528235)
                ·
                  refine ⟨1050388806800340009792353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700259204533560006528235 1050388806800340009792353)
                  ·
                    refine ⟨787791605100255007344265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1050388806800340009792353 787791605100255007344265)
                    ·
                      refine ⟨590843703825191255508199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 787791605100255007344265 590843703825191255508199)
                      ·
                        rfl

theorem cell23_1150664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_1150664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150664 prefixEnd_1150664 := by exact prefixLift 1150664
  have htrace : WordTrace (prefixWord ++ tailWord_1150664) baseStart_1150664 baseEnd_1150664 := by
    simpa [prefixWord, tailWord_1150664, baseEnd_1150664] using wordTrace_append hprefix tailTrace_1150664
  have hstable : (prefixWord ++ tailWord_1150664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150664).length < 2 ^ (prefixWord ++ tailWord_1150664).sum := by decide
  have hdescent : baseEnd_1150664 < baseStart_1150664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150680 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 1, 3, 3]
def baseStart_1150680 : Nat := 118140960795 + 1150680 * 2 ^ 59
def prefixEnd_1150680 : Nat := 4983230072969 + 3 ^ 40 * 1150680 * 2
def baseEnd_1150680 : Nat := 590851919515663192908125

theorem tailTrace_1150680 : CollatzResearch.WordTrace tailWord_1150680 prefixEnd_1150680 590851919515663192908125 := by
  unfold tailWord_1150680
  simp only [CollatzResearch.WordTrace]
  refine ⟨20984373735645177671656747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27979164980860236895542329 20984373735645177671656747)
  ·
    refine ⟨31476560603467766507485121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20984373735645177671656747 31476560603467766507485121)
    ·
      refine ⟨23607420452600824880613841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31476560603467766507485121 23607420452600824880613841)
      ·
        refine ⟨17705565339450618660460381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23607420452600824880613841 17705565339450618660460381)
        ·
          refine ⟨6639587002293981997672643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17705565339450618660460381 6639587002293981997672643)
          ·
            refine ⟨9959380503440972996508965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6639587002293981997672643 9959380503440972996508965)
            ·
              refine ⟨1867383844395182436845431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9959380503440972996508965 1867383844395182436845431)
              ·
                refine ⟨2801075766592773655268147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867383844395182436845431 2801075766592773655268147)
                ·
                  refine ⟨4201613649889160482902221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801075766592773655268147 4201613649889160482902221)
                  ·
                    refine ⟨1575605118708435181088333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4201613649889160482902221 1575605118708435181088333)
                    ·
                      refine ⟨590851919515663192908125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1575605118708435181088333 590851919515663192908125)
                      ·
                        rfl

theorem cell23_1150680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_1150680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150680 prefixEnd_1150680 := by exact prefixLift 1150680
  have htrace : WordTrace (prefixWord ++ tailWord_1150680) baseStart_1150680 baseEnd_1150680 := by
    simpa [prefixWord, tailWord_1150680, baseEnd_1150680] using wordTrace_append hprefix tailTrace_1150680
  have hstable : (prefixWord ++ tailWord_1150680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150680).length < 2 ^ (prefixWord ++ tailWord_1150680).sum := by decide
  have hdescent : baseEnd_1150680 < baseStart_1150680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150693 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1150693 : Nat := 118140960795 + 1150693 * 2 ^ 59
def prefixEnd_1150693 : Nat := 4983230072969 + 3 ^ 40 * 1150693 * 2
def baseEnd_1150693 : Nat := 590858594764171642045565

theorem tailTrace_1150693 : CollatzResearch.WordTrace tailWord_1150693 prefixEnd_1150693 590858594764171642045565 := by
  unfold tailWord_1150693
  simp only [CollatzResearch.WordTrace]
  refine ⟨41969221620243258563536733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27979481080162172375691155 41969221620243258563536733)
  ·
    refine ⟨15738458107591221961326275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41969221620243258563536733 15738458107591221961326275)
    ·
      refine ⟨23607687161386832941989413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15738458107591221961326275 23607687161386832941989413)
      ·
        refine ⟨4426441342760031176623015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23607687161386832941989413 4426441342760031176623015)
        ·
          refine ⟨6639662014140046764934523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4426441342760031176623015 6639662014140046764934523)
          ·
            refine ⟨9959493021210070147401785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6639662014140046764934523 9959493021210070147401785)
            ·
              refine ⟨7469619765907552610551339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9959493021210070147401785 7469619765907552610551339)
              ·
                refine ⟨11204429648861328915827009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7469619765907552610551339 11204429648861328915827009)
                ·
                  refine ⟨8403322236645996686870257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11204429648861328915827009 8403322236645996686870257)
                  ·
                    refine ⟨6302491677484497515152693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8403322236645996686870257 6302491677484497515152693)
                    ·
                      refine ⟨590858594764171642045565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6302491677484497515152693 590858594764171642045565)
                      ·
                        rfl

theorem cell23_1150693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1150693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150693 prefixEnd_1150693 := by exact prefixLift 1150693
  have htrace : WordTrace (prefixWord ++ tailWord_1150693) baseStart_1150693 baseEnd_1150693 := by
    simpa [prefixWord, tailWord_1150693, baseEnd_1150693] using wordTrace_append hprefix tailTrace_1150693
  have hstable : (prefixWord ++ tailWord_1150693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150693).length < 2 ^ (prefixWord ++ tailWord_1150693).sum := by decide
  have hdescent : baseEnd_1150693 < baseStart_1150693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150723 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 3]
def baseStart_1150723 : Nat := 118140960795 + 1150723 * 2 ^ 59
def prefixEnd_1150723 : Nat := 4983230072969 + 3 ^ 40 * 1150723 * 2
def baseEnd_1150723 : Nat := 590873999183806524670427

theorem tailTrace_1150723 : CollatzResearch.WordTrace tailWord_1150723 prefixEnd_1150723 590873999183806524670427 := by
  unfold tailWord_1150723
  simp only [CollatzResearch.WordTrace]
  refine ⟨41970315810134573687128823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27980210540089715791419215 41970315810134573687128823)
  ·
    refine ⟨62955473715201860530693235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41970315810134573687128823 62955473715201860530693235)
    ·
      refine ⟨94433210572802790796039853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62955473715201860530693235 94433210572802790796039853)
      ·
        refine ⟨35412453964801046548514945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94433210572802790796039853 35412453964801046548514945)
        ·
          refine ⟨26559340473600784911386209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35412453964801046548514945 26559340473600784911386209)
          ·
            refine ⟨19919505355200588683539657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26559340473600784911386209 19919505355200588683539657)
            ·
              refine ⟨14939629016400441512654743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19919505355200588683539657 14939629016400441512654743)
              ·
                refine ⟨22409443524600662268982115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14939629016400441512654743 22409443524600662268982115)
                ·
                  refine ⟨33614165286900993403473173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22409443524600662268982115 33614165286900993403473173)
                  ·
                    refine ⟨1575663997823484065787805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33614165286900993403473173 1575663997823484065787805)
                    ·
                      refine ⟨590873999183806524670427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1575663997823484065787805 590873999183806524670427)
                      ·
                        rfl

theorem cell23_1150723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_1150723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150723 prefixEnd_1150723 := by exact prefixLift 1150723
  have htrace : WordTrace (prefixWord ++ tailWord_1150723) baseStart_1150723 baseEnd_1150723 := by
    simpa [prefixWord, tailWord_1150723, baseEnd_1150723] using wordTrace_append hprefix tailTrace_1150723
  have hstable : (prefixWord ++ tailWord_1150723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150723).length < 2 ^ (prefixWord ++ tailWord_1150723).sum := by decide
  have hdescent : baseEnd_1150723 < baseStart_1150723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150807 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 2, 5]
def baseStart_1150807 : Nat := 118140960795 + 1150807 * 2 ^ 59
def prefixEnd_1150807 : Nat := 4983230072969 + 3 ^ 40 * 1150807 * 2
def baseEnd_1150807 : Nat := 196972377186261398673347

theorem tailTrace_1150807 : CollatzResearch.WordTrace tailWord_1150807 prefixEnd_1150807 196972377186261398673347 := by
  unfold tailWord_1150807
  simp only [CollatzResearch.WordTrace]
  refine ⟨41973379541830256033186675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27982253027886837355457783 41973379541830256033186675)
  ·
    refine ⟨62960069312745384049780013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41973379541830256033186675 62960069312745384049780013)
    ·
      refine ⟨23610025992279519018667505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62960069312745384049780013 23610025992279519018667505)
      ·
        refine ⟨17707519494209639264000629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23610025992279519018667505 17707519494209639264000629)
        ·
          refine ⟨1660079952582153681000059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17707519494209639264000629 1660079952582153681000059)
          ·
            refine ⟨2490119928873230521500089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660079952582153681000059 2490119928873230521500089)
            ·
              refine ⟨1867589946654922891125067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2490119928873230521500089 1867589946654922891125067)
              ·
                refine ⟨2801384919982384336687601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867589946654922891125067 2801384919982384336687601)
                ·
                  refine ⟨2101038689986788252515701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2801384919982384336687601 2101038689986788252515701)
                  ·
                    refine ⟨196972377186261398673347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2101038689986788252515701 196972377186261398673347)
                    ·
                      rfl

theorem cell23_1150807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_1150807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150807 prefixEnd_1150807 := by exact prefixLift 1150807
  have htrace : WordTrace (prefixWord ++ tailWord_1150807) baseStart_1150807 baseEnd_1150807 := by
    simpa [prefixWord, tailWord_1150807, baseEnd_1150807] using wordTrace_append hprefix tailTrace_1150807
  have hstable : (prefixWord ++ tailWord_1150807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150807).length < 2 ^ (prefixWord ++ tailWord_1150807).sum := by decide
  have hdescent : baseEnd_1150807 < baseStart_1150807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150837 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1150837 : Nat := 118140960795 + 1150837 * 2 ^ 59
def prefixEnd_1150837 : Nat := 4983230072969 + 3 ^ 40 * 1150837 * 2
def baseEnd_1150837 : Nat := 196977511992806359548301

theorem tailTrace_1150837 : CollatzResearch.WordTrace tailWord_1150837 prefixEnd_1150837 196977511992806359548301 := by
  unfold tailWord_1150837
  simp only [CollatzResearch.WordTrace]
  refine ⟨41974473731721571156778765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27982982487814380771185843 41974473731721571156778765)
  ·
    refine ⟨15740427649395589183792037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41974473731721571156778765 15740427649395589183792037)
    ·
      refine ⟨2951330184261672971961007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15740427649395589183792037 2951330184261672971961007)
      ·
        refine ⟨4426995276392509457941511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2951330184261672971961007 4426995276392509457941511)
        ·
          refine ⟨6640492914588764186912267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4426995276392509457941511 6640492914588764186912267)
          ·
            refine ⟨9960739371883146280368401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6640492914588764186912267 9960739371883146280368401)
            ·
              refine ⟨7470554528912359710276301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9960739371883146280368401 7470554528912359710276301)
              ·
                refine ⟨2801457948342134891353613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7470554528912359710276301 2801457948342134891353613)
                ·
                  refine ⟨1050546730628300584257605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2801457948342134891353613 1050546730628300584257605)
                  ·
                    refine ⟨196977511992806359548301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1050546730628300584257605 196977511992806359548301)
                    ·
                      rfl

theorem cell23_1150837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1150837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150837 prefixEnd_1150837 := by exact prefixLift 1150837
  have htrace : WordTrace (prefixWord ++ tailWord_1150837) baseStart_1150837 baseEnd_1150837 := by
    simpa [prefixWord, tailWord_1150837, baseEnd_1150837] using wordTrace_append hprefix tailTrace_1150837
  have hstable : (prefixWord ++ tailWord_1150837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150837).length < 2 ^ (prefixWord ++ tailWord_1150837).sum := by decide
  have hdescent : baseEnd_1150837 < baseStart_1150837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1150982 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1150982 : Nat := 118140960795 + 1150982 * 2 ^ 59
def prefixEnd_1150982 : Nat := 4983230072969 + 3 ^ 40 * 1150982 * 2
def baseEnd_1150982 : Nat := 197002330224440337110579

theorem tailTrace_1150982 : CollatzResearch.WordTrace tailWord_1150982 prefixEnd_1150982 197002330224440337110579 := by
  unfold tailWord_1150982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1311867572381133153775225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27986508210797507280538133 1311867572381133153775225)
  ·
    refine ⟨983900679285849865331419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1311867572381133153775225 983900679285849865331419)
    ·
      refine ⟨1475851018928774797997129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 983900679285849865331419 1475851018928774797997129)
      ·
        refine ⟨1106888264196581098497847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1475851018928774797997129 1106888264196581098497847)
        ·
          refine ⟨1660332396294871647746771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106888264196581098497847 1660332396294871647746771)
          ·
            refine ⟨2490498594442307471620157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660332396294871647746771 2490498594442307471620157)
            ·
              refine ⟨933936972915865301857559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2490498594442307471620157 933936972915865301857559)
              ·
                refine ⟨1400905459373797952786339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933936972915865301857559 1400905459373797952786339)
                ·
                  refine ⟨2101358189060696929179509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1400905459373797952786339 2101358189060696929179509)
                  ·
                    refine ⟨197002330224440337110579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2101358189060696929179509 197002330224440337110579)
                    ·
                      rfl

theorem cell23_1150982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1150982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1150982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1150982 prefixEnd_1150982 := by exact prefixLift 1150982
  have htrace : WordTrace (prefixWord ++ tailWord_1150982) baseStart_1150982 baseEnd_1150982 := by
    simpa [prefixWord, tailWord_1150982, baseEnd_1150982] using wordTrace_append hprefix tailTrace_1150982
  have hstable : (prefixWord ++ tailWord_1150982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1150982).length < 2 ^ (prefixWord ++ tailWord_1150982).sum := by decide
  have hdescent : baseEnd_1150982 < baseStart_1150982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1150982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151024 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 1, 4, 2]
def baseStart_1151024 : Nat := 118140960795 + 1151024 * 2 ^ 59
def prefixEnd_1151024 : Nat := 4983230072969 + 3 ^ 40 * 1151024 * 2
def baseEnd_1151024 : Nat := 591028556860809847006543

theorem tailTrace_1151024 : CollatzResearch.WordTrace tailWord_1151024 prefixEnd_1151024 591028556860809847006543 := by
  unfold tailWord_1151024
  simp only [CollatzResearch.WordTrace]
  refine ⟨20990647091022051046918063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27987529454696068062557417 20990647091022051046918063)
  ·
    refine ⟨31485970636533076570377095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20990647091022051046918063 31485970636533076570377095)
    ·
      refine ⟨47228955954799614855565643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31485970636533076570377095 47228955954799614855565643)
      ·
        refine ⟨70843433932199422283348465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47228955954799614855565643 70843433932199422283348465)
        ·
          refine ⟨53132575449149566712511349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70843433932199422283348465 53132575449149566712511349)
          ·
            refine ⟨4981178948357771879297939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53132575449149566712511349 4981178948357771879297939)
            ·
              refine ⟨7471768422536657818946909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4981178948357771879297939 7471768422536657818946909)
              ·
                refine ⟨2801913158451246682105091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7471768422536657818946909 2801913158451246682105091)
                ·
                  refine ⟨4202869737676870023157637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801913158451246682105091 4202869737676870023157637)
                  ·
                    refine ⟨788038075814413129342057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4202869737676870023157637 788038075814413129342057)
                    ·
                      refine ⟨591028556860809847006543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788038075814413129342057 591028556860809847006543)
                      ·
                        rfl

theorem cell23_1151024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 4, 2].length) (baseStart_1151024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151024 prefixEnd_1151024 := by exact prefixLift 1151024
  have htrace : WordTrace (prefixWord ++ tailWord_1151024) baseStart_1151024 baseEnd_1151024 := by
    simpa [prefixWord, tailWord_1151024, baseEnd_1151024] using wordTrace_append hprefix tailTrace_1151024
  have hstable : (prefixWord ++ tailWord_1151024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151024).length < 2 ^ (prefixWord ++ tailWord_1151024).sum := by decide
  have hdescent : baseEnd_1151024 < baseStart_1151024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151037 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1151037 : Nat := 118140960795 + 1151037 * 2 ^ 59
def prefixEnd_1151037 : Nat := 4983230072969 + 3 ^ 40 * 1151037 * 2
def baseEnd_1151037 : Nat := 591035232109318296143983

theorem tailTrace_1151037 : CollatzResearch.WordTrace tailWord_1151037 prefixEnd_1151037 591035232109318296143983 := by
  unfold tailWord_1151037
  simp only [CollatzResearch.WordTrace]
  refine ⟨41981768330997005314059365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27987845553998003542706243 41981768330997005314059365)
  ·
    refine ⟨7871581562061938496386131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41981768330997005314059365 7871581562061938496386131)
    ·
      refine ⟨11807372343092907744579197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7871581562061938496386131 11807372343092907744579197)
      ·
        refine ⟨4427764628659840404217199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11807372343092907744579197 4427764628659840404217199)
        ·
          refine ⟨6641646942989760606325799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4427764628659840404217199 6641646942989760606325799)
          ·
            refine ⟨9962470414484640909488699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6641646942989760606325799 9962470414484640909488699)
            ·
              refine ⟨14943705621726961364233049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9962470414484640909488699 14943705621726961364233049)
              ·
                refine ⟨11207779216295221023174787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14943705621726961364233049 11207779216295221023174787)
                ·
                  refine ⟨16811668824442831534762181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11207779216295221023174787 16811668824442831534762181)
                  ·
                    refine ⟨3152187904583030912767909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16811668824442831534762181 3152187904583030912767909)
                    ·
                      refine ⟨591035232109318296143983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3152187904583030912767909 591035232109318296143983)
                      ·
                        rfl

theorem cell23_1151037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1151037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151037 prefixEnd_1151037 := by exact prefixLift 1151037
  have htrace : WordTrace (prefixWord ++ tailWord_1151037) baseStart_1151037 baseEnd_1151037 := by
    simpa [prefixWord, tailWord_1151037, baseEnd_1151037] using wordTrace_append hprefix tailTrace_1151037
  have hstable : (prefixWord ++ tailWord_1151037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151037).length < 2 ^ (prefixWord ++ tailWord_1151037).sum := by decide
  have hdescent : baseEnd_1151037 < baseStart_1151037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151041 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_1151041 : Nat := 118140960795 + 1151041 * 2 ^ 59
def prefixEnd_1151041 : Nat := 4983230072969 + 3 ^ 40 * 1151041 * 2
def baseEnd_1151041 : Nat := 591037286031936280493965

theorem tailTrace_1151041 : CollatzResearch.WordTrace tailWord_1151041 prefixEnd_1151041 591037286031936280493965 := by
  unfold tailWord_1151041
  simp only [CollatzResearch.WordTrace]
  refine ⟨41981914222982513997204977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27987942815321675998136651 41981914222982513997204977)
  ·
    refine ⟨31486435667236885497903733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41981914222982513997204977 31486435667236885497903733)
    ·
      refine ⟨2951853343803458015428475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31486435667236885497903733 2951853343803458015428475)
      ·
        refine ⟨4427780015705187023142713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2951853343803458015428475 4427780015705187023142713)
        ·
          refine ⟨3320835011778890267357035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4427780015705187023142713 3320835011778890267357035)
          ·
            refine ⟨4981252517668335401035553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3320835011778890267357035 4981252517668335401035553)
            ·
              refine ⟨3735939388251251550776665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4981252517668335401035553 3735939388251251550776665)
              ·
                refine ⟨2801954541188438663082499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3735939388251251550776665 2801954541188438663082499)
                ·
                  refine ⟨4202931811782657994623749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801954541188438663082499 4202931811782657994623749)
                  ·
                    refine ⟨788049714709248373991953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4202931811782657994623749 788049714709248373991953)
                    ·
                      refine ⟨591037286031936280493965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788049714709248373991953 591037286031936280493965)
                      ·
                        rfl

theorem cell23_1151041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_1151041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151041 prefixEnd_1151041 := by exact prefixLift 1151041
  have htrace : WordTrace (prefixWord ++ tailWord_1151041) baseStart_1151041 baseEnd_1151041 := by
    simpa [prefixWord, tailWord_1151041, baseEnd_1151041] using wordTrace_append hprefix tailTrace_1151041
  have hstable : (prefixWord ++ tailWord_1151041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151041).length < 2 ^ (prefixWord ++ tailWord_1151041).sum := by decide
  have hdescent : baseEnd_1151041 < baseStart_1151041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151058 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_1151058 : Nat := 118140960795 + 1151058 * 2 ^ 59
def prefixEnd_1151058 : Nat := 4983230072969 + 3 ^ 40 * 1151058 * 2
def baseEnd_1151058 : Nat := 591046015203062713981387

theorem tailTrace_1151058 : CollatzResearch.WordTrace tailWord_1151058 prefixEnd_1151058 591046015203062713981387 := by
  unfold tailWord_1151058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10495633565980231475143457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27988356175947283933715885 10495633565980231475143457)
  ·
    refine ⟨7871725174485173606357593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10495633565980231475143457 7871725174485173606357593)
    ·
      refine ⟨5903793880863880204768195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7871725174485173606357593 5903793880863880204768195)
      ·
        refine ⟨8855690821295820307152293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5903793880863880204768195 8855690821295820307152293)
        ·
          refine ⟨1660442028992966307591055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8855690821295820307152293 1660442028992966307591055)
          ·
            refine ⟨2490663043489449461386583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660442028992966307591055 2490663043489449461386583)
            ·
              refine ⟨3735994565234174192079875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2490663043489449461386583 3735994565234174192079875)
              ·
                refine ⟨5603991847851261288119813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3735994565234174192079875 5603991847851261288119813)
                ·
                  refine ⟨1050748471472111491522465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5603991847851261288119813 1050748471472111491522465)
                  ·
                    refine ⟨788061353604083618641849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1050748471472111491522465 788061353604083618641849)
                    ·
                      refine ⟨591046015203062713981387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788061353604083618641849 591046015203062713981387)
                      ·
                        rfl

theorem cell23_1151058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_1151058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151058 prefixEnd_1151058 := by exact prefixLift 1151058
  have htrace : WordTrace (prefixWord ++ tailWord_1151058) baseStart_1151058 baseEnd_1151058 := by
    simpa [prefixWord, tailWord_1151058, baseEnd_1151058] using wordTrace_append hprefix tailTrace_1151058
  have hstable : (prefixWord ++ tailWord_1151058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151058).length < 2 ^ (prefixWord ++ tailWord_1151058).sum := by decide
  have hdescent : baseEnd_1151058 < baseStart_1151058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151064 : List Nat := [2, 1, 2, 2, 1, 4, 2, 4, 5]
def baseStart_1151064 : Nat := 118140960795 + 1151064 * 2 ^ 59
def prefixEnd_1151064 : Nat := 4983230072969 + 3 ^ 40 * 1151064 * 2
def baseEnd_1151064 : Nat := 65672121787443298945151

theorem tailTrace_1151064 : CollatzResearch.WordTrace tailWord_1151064 prefixEnd_1151064 65672121787443298945151 := by
  unfold tailWord_1151064
  simp only [CollatzResearch.WordTrace]
  refine ⟨20991376550949594462646123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27988502067932792616861497 20991376550949594462646123)
  ·
    refine ⟨31487064826424391693969185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20991376550949594462646123 31487064826424391693969185)
    ·
      refine ⟨23615298619818293770476889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31487064826424391693969185 23615298619818293770476889)
      ·
        refine ⟨17711473964863720327857667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23615298619818293770476889 17711473964863720327857667)
        ·
          refine ⟨26567210947295580491786501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17711473964863720327857667 26567210947295580491786501)
          ·
            refine ⟨4981352052617921342209969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26567210947295580491786501 4981352052617921342209969)
            ·
              refine ⟨3736014039463441006657477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4981352052617921342209969 3736014039463441006657477)
              ·
                refine ⟨700502632399395188748277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3736014039463441006657477 700502632399395188748277)
                ·
                  refine ⟨65672121787443298945151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 700502632399395188748277 65672121787443298945151)
                  ·
                    rfl

theorem cell23_1151064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 5].length) (baseStart_1151064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151064 prefixEnd_1151064 := by exact prefixLift 1151064
  have htrace : WordTrace (prefixWord ++ tailWord_1151064) baseStart_1151064 baseEnd_1151064 := by
    simpa [prefixWord, tailWord_1151064, baseEnd_1151064] using wordTrace_append hprefix tailTrace_1151064
  have hstable : (prefixWord ++ tailWord_1151064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151064).length < 2 ^ (prefixWord ++ tailWord_1151064).sum := by decide
  have hdescent : baseEnd_1151064 < baseStart_1151064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151077 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_1151077 : Nat := 118140960795 + 1151077 * 2 ^ 59
def prefixEnd_1151077 : Nat := 4983230072969 + 3 ^ 40 * 1151077 * 2
def baseEnd_1151077 : Nat := 197018590445166046547933

theorem tailTrace_1151077 : CollatzResearch.WordTrace tailWord_1151077 prefixEnd_1151077 197018590445166046547933 := by
  unfold tailWord_1151077
  simp only [CollatzResearch.WordTrace]
  refine ⟨41983227250852092145515485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27988818167234728097010323 41983227250852092145515485)
  ·
    refine ⟨15743710219069534554568307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41983227250852092145515485 15743710219069534554568307)
    ·
      refine ⟨23615565328604301831852461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15743710219069534554568307 23615565328604301831852461)
      ·
        refine ⟨8855836998226613186944673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23615565328604301831852461 8855836998226613186944673)
        ·
          refine ⟨6641877748669959890208505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8855836998226613186944673 6641877748669959890208505)
          ·
            refine ⟨4981408311502469917656379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6641877748669959890208505 4981408311502469917656379)
            ·
              refine ⟨7472112467253704876484569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4981408311502469917656379 7472112467253704876484569)
              ·
                refine ⟨5604084350440278657363427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7472112467253704876484569 5604084350440278657363427)
                ·
                  refine ⟨8406126525660417986045141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5604084350440278657363427 8406126525660417986045141)
                  ·
                    refine ⟨197018590445166046547933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8406126525660417986045141 197018590445166046547933)
                    ·
                      rfl

theorem cell23_1151077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_1151077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151077 prefixEnd_1151077 := by exact prefixLift 1151077
  have htrace : WordTrace (prefixWord ++ tailWord_1151077) baseStart_1151077 baseEnd_1151077 := by
    simpa [prefixWord, tailWord_1151077, baseEnd_1151077] using wordTrace_append hprefix tailTrace_1151077
  have hstable : (prefixWord ++ tailWord_1151077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151077).length < 2 ^ (prefixWord ++ tailWord_1151077).sum := by decide
  have hdescent : baseEnd_1151077 < baseStart_1151077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151094 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1151094 : Nat := 118140960795 + 1151094 * 2 ^ 59
def prefixEnd_1151094 : Nat := 4983230072969 + 3 ^ 40 * 1151094 * 2
def baseEnd_1151094 : Nat := 197021500168874857710407

theorem tailTrace_1151094 : CollatzResearch.WordTrace tailWord_1151094 prefixEnd_1151094 197021500168874857710407 := by
  unfold tailWord_1151094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2623990455736906503055271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27989231527860336032589557 2623990455736906503055271)
  ·
    refine ⟨3935985683605359754582907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2623990455736906503055271 3935985683605359754582907)
    ·
      refine ⟨5903978525408039631874361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3935985683605359754582907 5903978525408039631874361)
      ·
        refine ⟨4427983894056029723905771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5903978525408039631874361 4427983894056029723905771)
        ·
          refine ⟨6641975841084044585858657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4427983894056029723905771 6641975841084044585858657)
          ·
            refine ⟨4981481880813033439393993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6641975841084044585858657 4981481880813033439393993)
            ·
              refine ⟨3736111410609775079545495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4981481880813033439393993 3736111410609775079545495)
              ·
                refine ⟨5604167115914662619318243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3736111410609775079545495 5604167115914662619318243)
                ·
                  refine ⟨8406250673871993928977365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5604167115914662619318243 8406250673871993928977365)
                  ·
                    refine ⟨197021500168874857710407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8406250673871993928977365 197021500168874857710407)
                    ·
                      rfl

theorem cell23_1151094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1151094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151094 prefixEnd_1151094 := by exact prefixLift 1151094
  have htrace : WordTrace (prefixWord ++ tailWord_1151094) baseStart_1151094 baseEnd_1151094 := by
    simpa [prefixWord, tailWord_1151094, baseEnd_1151094] using wordTrace_append hprefix tailTrace_1151094
  have hstable : (prefixWord ++ tailWord_1151094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151094).length < 2 ^ (prefixWord ++ tailWord_1151094).sum := by decide
  have hdescent : baseEnd_1151094 < baseStart_1151094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151114 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1151114 : Nat := 118140960795 + 1151114 * 2 ^ 59
def prefixEnd_1151114 : Nat := 4983230072969 + 3 ^ 40 * 1151114 * 2
def baseEnd_1151114 : Nat := 591074770119714494881129

theorem tailTrace_1151114 : CollatzResearch.WordTrace tailWord_1151114 prefixEnd_1151114 591074770119714494881129 := by
  unfold tailWord_1151114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10496144187929511866153099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27989717834478698309741597 10496144187929511866153099)
  ·
    refine ⟨15744216281894267799229649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10496144187929511866153099 15744216281894267799229649)
    ·
      refine ⟨11808162211420700849422237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15744216281894267799229649 11808162211420700849422237)
      ·
        refine ⟨4428060829282762818533339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11808162211420700849422237 4428060829282762818533339)
        ·
          refine ⟨6642091243924144227800009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4428060829282762818533339 6642091243924144227800009)
          ·
            refine ⟨4981568432943108170850007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6642091243924144227800009 4981568432943108170850007)
            ·
              refine ⟨7472352649414662256275011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4981568432943108170850007 7472352649414662256275011)
              ·
                refine ⟨11208528974121993384412517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7472352649414662256275011 11208528974121993384412517)
                ·
                  refine ⟨2101599182647873759577347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11208528974121993384412517 2101599182647873759577347)
                  ·
                    refine ⟨3152398773971810639366021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2101599182647873759577347 3152398773971810639366021)
                    ·
                      refine ⟨591074770119714494881129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3152398773971810639366021 591074770119714494881129)
                      ·
                        rfl

theorem cell23_1151114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1151114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151114 prefixEnd_1151114 := by exact prefixLift 1151114
  have htrace : WordTrace (prefixWord ++ tailWord_1151114) baseStart_1151114 baseEnd_1151114 := by
    simpa [prefixWord, tailWord_1151114, baseEnd_1151114] using wordTrace_append hprefix tailTrace_1151114
  have hstable : (prefixWord ++ tailWord_1151114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151114).length < 2 ^ (prefixWord ++ tailWord_1151114).sum := by decide
  have hdescent : baseEnd_1151114 < baseStart_1151114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151126 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1151126 : Nat := 118140960795 + 1151126 * 2 ^ 59
def prefixEnd_1151126 : Nat := 4983230072969 + 3 ^ 40 * 1151126 * 2
def baseEnd_1151126 : Nat := 591080931887568447931075

theorem tailTrace_1151126 : CollatzResearch.WordTrace tailWord_1151126 prefixEnd_1151126 591080931887568447931075 := by
  unfold tailWord_1151126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624063401729660844628077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27990009618449715676032821 2624063401729660844628077)
  ·
    refine ⟨984023775648622816735529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2624063401729660844628077 984023775648622816735529)
    ·
      refine ⟨738017831736467112551647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 984023775648622816735529 738017831736467112551647)
      ·
        refine ⟨1107026747604700668827471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738017831736467112551647 1107026747604700668827471)
        ·
          refine ⟨1660540121407051003241207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107026747604700668827471 1660540121407051003241207)
          ·
            refine ⟨2490810182110576504861811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660540121407051003241207 2490810182110576504861811)
            ·
              refine ⟨3736215273165864757292717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2490810182110576504861811 3736215273165864757292717)
              ·
                refine ⟨1401080727437199283984769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3736215273165864757292717 1401080727437199283984769)
                ·
                  refine ⟨1050810545577899462988577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1401080727437199283984769 1050810545577899462988577)
                  ·
                    refine ⟨788107909183424597241433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1050810545577899462988577 788107909183424597241433)
                    ·
                      refine ⟨591080931887568447931075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788107909183424597241433 591080931887568447931075)
                      ·
                        rfl

theorem cell23_1151126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1151126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151126 prefixEnd_1151126 := by exact prefixLift 1151126
  have htrace : WordTrace (prefixWord ++ tailWord_1151126) baseStart_1151126 baseEnd_1151126 := by
    simpa [prefixWord, tailWord_1151126, baseEnd_1151126] using wordTrace_append hprefix tailTrace_1151126
  have hstable : (prefixWord ++ tailWord_1151126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151126).length < 2 ^ (prefixWord ++ tailWord_1151126).sum := by decide
  have hdescent : baseEnd_1151126 < baseStart_1151126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151187 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 4]
def baseStart_1151187 : Nat := 118140960795 + 1151187 * 2 ^ 59
def prefixEnd_1151187 : Nat := 4983230072969 + 3 ^ 40 * 1151187 * 2
def baseEnd_1151187 : Nat := 591112254207492709268293

theorem tailTrace_1151187 : CollatzResearch.WordTrace tailWord_1151187 prefixEnd_1151187 591112254207492709268293 := by
  unfold tailWord_1151187
  simp only [CollatzResearch.WordTrace]
  refine ⟨41987239280453580932019815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27991492853635720621346543 41987239280453580932019815)
  ·
    refine ⟨62980858920680371398029723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41987239280453580932019815 62980858920680371398029723)
    ·
      refine ⟨94471288381020557097044585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62980858920680371398029723 94471288381020557097044585)
      ·
        refine ⟨70853466285765417822783439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94471288381020557097044585 70853466285765417822783439)
        ·
          refine ⟨106280199428648126734175159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70853466285765417822783439 106280199428648126734175159)
          ·
            refine ⟨159420299142972190101262739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106280199428648126734175159 159420299142972190101262739)
            ·
              refine ⟨239130448714458285151894109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159420299142972190101262739 239130448714458285151894109)
              ·
                refine ⟨89673918267921856931960291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239130448714458285151894109 89673918267921856931960291)
                ·
                  refine ⟨134510877401882785397940437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89673918267921856931960291 134510877401882785397940437)
                  ·
                    refine ⟨3152598689106627782764229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 134510877401882785397940437 3152598689106627782764229)
                    ·
                      refine ⟨591112254207492709268293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3152598689106627782764229 591112254207492709268293)
                      ·
                        rfl

theorem cell23_1151187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_1151187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151187 prefixEnd_1151187 := by exact prefixLift 1151187
  have htrace : WordTrace (prefixWord ++ tailWord_1151187) baseStart_1151187 baseEnd_1151187 := by
    simpa [prefixWord, tailWord_1151187, baseEnd_1151187] using wordTrace_append hprefix tailTrace_1151187
  have hstable : (prefixWord ++ tailWord_1151187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151187).length < 2 ^ (prefixWord ++ tailWord_1151187).sum := by decide
  have hdescent : baseEnd_1151187 < baseStart_1151187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151208 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_1151208 : Nat := 118140960795 + 1151208 * 2 ^ 59
def prefixEnd_1151208 : Nat := 4983230072969 + 3 ^ 40 * 1151208 * 2
def baseEnd_1151208 : Nat := 591123037301237127105697

theorem tailTrace_1151208 : CollatzResearch.WordTrace tailWord_1151208 prefixEnd_1151208 591123037301237127105697 := by
  unfold tailWord_1151208
  simp only [CollatzResearch.WordTrace]
  refine ⟨20994002606688750759267139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27992003475585001012356185 20994002606688750759267139)
  ·
    refine ⟨31491003910033126138900709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20994002606688750759267139 31491003910033126138900709)
    ·
      refine ⟨5904563233131211151043883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31491003910033126138900709 5904563233131211151043883)
      ·
        refine ⟨8856844849696816726565825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5904563233131211151043883 8856844849696816726565825)
        ·
          refine ⟨6642633637272612544924369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8856844849696816726565825 6642633637272612544924369)
          ·
            refine ⟨4981975227954459408693277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6642633637272612544924369 4981975227954459408693277)
            ·
              refine ⟨1868240710482922278259979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4981975227954459408693277 1868240710482922278259979)
              ·
                refine ⟨2802361065724383417389969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1868240710482922278259979 2802361065724383417389969)
                ·
                  refine ⟨2101770799293287563042477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2802361065724383417389969 2101770799293287563042477)
                  ·
                    refine ⟨788164049734982836140929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2101770799293287563042477 788164049734982836140929)
                    ·
                      refine ⟨591123037301237127105697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788164049734982836140929 591123037301237127105697)
                      ·
                        rfl

theorem cell23_1151208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_1151208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151208 prefixEnd_1151208 := by exact prefixLift 1151208
  have htrace : WordTrace (prefixWord ++ tailWord_1151208) baseStart_1151208 baseEnd_1151208 := by
    simpa [prefixWord, tailWord_1151208, baseEnd_1151208] using wordTrace_append hprefix tailTrace_1151208
  have hstable : (prefixWord ++ tailWord_1151208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151208).length < 2 ^ (prefixWord ++ tailWord_1151208).sum := by decide
  have hdescent : baseEnd_1151208 < baseStart_1151208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151215 : List Nat := [1, 1, 2, 1, 6, 2, 2, 3, 1, 1, 3]
def baseStart_1151215 : Nat := 118140960795 + 1151215 * 2 ^ 59
def prefixEnd_1151215 : Nat := 4983230072969 + 3 ^ 40 * 1151215 * 2
def baseEnd_1151215 : Nat := 591126631665818599718165

theorem tailTrace_1151215 : CollatzResearch.WordTrace tailWord_1151215 prefixEnd_1151215 591126631665818599718165 := by
  unfold tailWord_1151215
  simp only [CollatzResearch.WordTrace]
  refine ⟨41988260524352141714039099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27992173682901427809359399 41988260524352141714039099)
  ·
    refine ⟨62982390786528212571058649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41988260524352141714039099 62982390786528212571058649)
    ·
      refine ⟨47236793089896159428293987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62982390786528212571058649 47236793089896159428293987)
      ·
        refine ⟨70855189634844239142440981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47236793089896159428293987 70855189634844239142440981)
        ·
          refine ⟨3321337014133323709801921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70855189634844239142440981 3321337014133323709801921)
          ·
            refine ⟨2491002760599992782351441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3321337014133323709801921 2491002760599992782351441)
            ·
              refine ⟨1868252070449994586763581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2491002760599992782351441 1868252070449994586763581)
              ·
                refine ⟨700594526418747970036343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1868252070449994586763581 700594526418747970036343)
                ·
                  refine ⟨1050891789628121955054515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700594526418747970036343 1050891789628121955054515)
                  ·
                    refine ⟨1576337684442182932581773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1050891789628121955054515 1576337684442182932581773)
                    ·
                      refine ⟨591126631665818599718165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1576337684442182932581773 591126631665818599718165)
                      ·
                        rfl

theorem cell23_1151215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 1, 1, 3].length) (baseStart_1151215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151215 prefixEnd_1151215 := by exact prefixLift 1151215
  have htrace : WordTrace (prefixWord ++ tailWord_1151215) baseStart_1151215 baseEnd_1151215 := by
    simpa [prefixWord, tailWord_1151215, baseEnd_1151215] using wordTrace_append hprefix tailTrace_1151215
  have hstable : (prefixWord ++ tailWord_1151215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151215).length < 2 ^ (prefixWord ++ tailWord_1151215).sum := by decide
  have hdescent : baseEnd_1151215 < baseStart_1151215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151218 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_1151218 : Nat := 118140960795 + 1151218 * 2 ^ 59
def prefixEnd_1151218 : Nat := 4983230072969 + 3 ^ 40 * 1151218 * 2
def baseEnd_1151218 : Nat := 197042724035927362660217

theorem tailTrace_1151218 : CollatzResearch.WordTrace tailWord_1151218 prefixEnd_1151218 197042724035927362660217 := by
  unfold tailWord_1151218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10497092485835318306599577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27992246628894182150932205 10497092485835318306599577)
  ·
    refine ⟨7872819364376488729949683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10497092485835318306599577 7872819364376488729949683)
    ·
      refine ⟨11809229046564733094924525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7872819364376488729949683 11809229046564733094924525)
      ·
        refine ⟨4428460892461774910596697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11809229046564733094924525 4428460892461774910596697)
        ·
          refine ⟨3321345669346331182947523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4428460892461774910596697 3321345669346331182947523)
          ·
            refine ⟨4982018504019496774421285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321345669346331182947523 4982018504019496774421285)
            ·
              refine ⟨934128469503655645203991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4982018504019496774421285 934128469503655645203991)
              ·
                refine ⟨1401192704255483467805987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934128469503655645203991 1401192704255483467805987)
                ·
                  refine ⟨2101789056383225201708981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401192704255483467805987 2101789056383225201708981)
                  ·
                    refine ⟨197042724035927362660217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2101789056383225201708981 197042724035927362660217)
                    ·
                      rfl

theorem cell23_1151218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_1151218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151218 prefixEnd_1151218 := by exact prefixLift 1151218
  have htrace : WordTrace (prefixWord ++ tailWord_1151218) baseStart_1151218 baseEnd_1151218 := by
    simpa [prefixWord, tailWord_1151218, baseEnd_1151218] using wordTrace_append hprefix tailTrace_1151218
  have hstable : (prefixWord ++ tailWord_1151218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151218).length < 2 ^ (prefixWord ++ tailWord_1151218).sum := by decide
  have hdescent : baseEnd_1151218 < baseStart_1151218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151261 : List Nat := [1, 4, 2, 3, 2, 1, 1, 9]
def baseStart_1151261 : Nat := 118140960795 + 1151261 * 2 ^ 59
def prefixEnd_1151261 : Nat := 4983230072969 + 3 ^ 40 * 1151261 * 2
def baseEnd_1151261 : Nat := 21894453769478719249739

theorem tailTrace_1151261 : CollatzResearch.WordTrace tailWord_1151261 prefixEnd_1151261 21894453769478719249739 := by
  unfold tailWord_1151261
  simp only [CollatzResearch.WordTrace]
  refine ⟨41989938282185491570213637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27993292188123661046809091 41989938282185491570213637)
  ·
    refine ⟨7873113427909779669415057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41989938282185491570213637 7873113427909779669415057)
    ·
      refine ⟨5904835070932334752061293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7873113427909779669415057 5904835070932334752061293)
      ·
        refine ⟨2214313151599625532022985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5904835070932334752061293 2214313151599625532022985)
        ·
          refine ⟨1660734863699719149017239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2214313151599625532022985 1660734863699719149017239)
          ·
            refine ⟨2491102295549578723525859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660734863699719149017239 2491102295549578723525859)
            ·
              refine ⟨3736653443324368085288789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2491102295549578723525859 3736653443324368085288789)
              ·
                refine ⟨21894453769478719249739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3736653443324368085288789 21894453769478719249739)
                ·
                  rfl

theorem cell23_1151261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 9].length) (baseStart_1151261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151261 prefixEnd_1151261 := by exact prefixLift 1151261
  have htrace : WordTrace (prefixWord ++ tailWord_1151261) baseStart_1151261 baseEnd_1151261 := by
    simpa [prefixWord, tailWord_1151261, baseEnd_1151261] using wordTrace_append hprefix tailTrace_1151261
  have hstable : (prefixWord ++ tailWord_1151261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151261).length < 2 ^ (prefixWord ++ tailWord_1151261).sum := by decide
  have hdescent : baseEnd_1151261 < baseStart_1151261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151278 : List Nat := [4, 1, 3, 3, 1, 2, 9]
def baseStart_1151278 : Nat := 118140960795 + 1151278 * 2 ^ 59
def prefixEnd_1151278 : Nat := 4983230072969 + 3 ^ 40 * 1151278 * 2
def baseEnd_1151278 : Nat := 7298259024037677200375

theorem tailTrace_1151278 : CollatzResearch.WordTrace tailWord_1151278 prefixEnd_1151278 7298259024037677200375 := by
  unfold tailWord_1151278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5248819790390487934197811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27993705548749268982388325 5248819790390487934197811)
  ·
    refine ⟨7873229685585731901296717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5248819790390487934197811 7873229685585731901296717)
    ·
      refine ⟨2952461132094649462986269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7873229685585731901296717 2952461132094649462986269)
      ·
        refine ⟨1107172924535493548619851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2952461132094649462986269 1107172924535493548619851)
        ·
          refine ⟨1660759386803240322929777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107172924535493548619851 1660759386803240322929777)
          ·
            refine ⟨1245569540102430242197333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1660759386803240322929777 1245569540102430242197333)
            ·
              refine ⟨7298259024037677200375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1245569540102430242197333 7298259024037677200375)
              ·
                rfl

theorem cell23_1151278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 9].length) (baseStart_1151278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151278 prefixEnd_1151278 := by exact prefixLift 1151278
  have htrace : WordTrace (prefixWord ++ tailWord_1151278) baseStart_1151278 baseEnd_1151278 := by
    simpa [prefixWord, tailWord_1151278, baseEnd_1151278] using wordTrace_append hprefix tailTrace_1151278
  have hstable : (prefixWord ++ tailWord_1151278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151278).length < 2 ^ (prefixWord ++ tailWord_1151278).sum := by decide
  have hdescent : baseEnd_1151278 < baseStart_1151278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151289 : List Nat := [1, 2, 1, 6, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1151289 : Nat := 118140960795 + 1151289 * 2 ^ 59
def prefixEnd_1151289 : Nat := 4983230072969 + 3 ^ 40 * 1151289 * 2
def baseEnd_1151289 : Nat := 591164629234251310192825

theorem tailTrace_1151289 : CollatzResearch.WordTrace tailWord_1151289 prefixEnd_1151289 591164629234251310192825 := by
  unfold tailWord_1151289
  simp only [CollatzResearch.WordTrace]
  refine ⟨41990959526084052352232921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27993973017389368234821947 41990959526084052352232921)
  ·
    refine ⟨31493219644563039264174691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41990959526084052352232921 31493219644563039264174691)
    ·
      refine ⟨47239829466844558896262037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31493219644563039264174691 47239829466844558896262037)
      ·
        refine ⟨2214367006258338698262283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47239829466844558896262037 2214367006258338698262283)
        ·
          refine ⟨3321550509387508047393425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2214367006258338698262283 3321550509387508047393425)
          ·
            refine ⟨2491162882040631035545069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3321550509387508047393425 2491162882040631035545069)
            ·
              refine ⟨934186080765236638329401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2491162882040631035545069 934186080765236638329401)
              ·
                refine ⟨700639560573927478747051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934186080765236638329401 700639560573927478747051)
                ·
                  refine ⟨1050959340860891218120577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700639560573927478747051 1050959340860891218120577)
                  ·
                    refine ⟨788219505645668413590433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1050959340860891218120577 788219505645668413590433)
                    ·
                      refine ⟨591164629234251310192825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788219505645668413590433 591164629234251310192825)
                      ·
                        rfl

theorem cell23_1151289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1151289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151289 prefixEnd_1151289 := by exact prefixLift 1151289
  have htrace : WordTrace (prefixWord ++ tailWord_1151289) baseStart_1151289 baseEnd_1151289 := by
    simpa [prefixWord, tailWord_1151289, baseEnd_1151289] using wordTrace_append hprefix tailTrace_1151289
  have hstable : (prefixWord ++ tailWord_1151289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151289).length < 2 ^ (prefixWord ++ tailWord_1151289).sum := by decide
  have hdescent : baseEnd_1151289 < baseStart_1151289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151304 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 2, 6]
def baseStart_1151304 : Nat := 118140960795 + 1151304 * 2 ^ 59
def prefixEnd_1151304 : Nat := 4983230072969 + 3 ^ 40 * 1151304 * 2
def baseEnd_1151304 : Nat := 197057443814689583835085

theorem tailTrace_1151304 : CollatzResearch.WordTrace tailWord_1151304 prefixEnd_1151304 197057443814689583835085 := by
  unfold tailWord_1151304
  simp only [CollatzResearch.WordTrace]
  refine ⟨20995753310514854957014483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27994337747353139942685977 20995753310514854957014483)
  ·
    refine ⟨31493629965772282435521725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20995753310514854957014483 31493629965772282435521725)
    ·
      refine ⟨11810111237164605913320647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31493629965772282435521725 11810111237164605913320647)
      ·
        refine ⟨17715166855746908869980971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11810111237164605913320647 17715166855746908869980971)
        ·
          refine ⟨26572750283620363304971457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17715166855746908869980971 26572750283620363304971457)
          ·
            refine ⟨19929562712715272478728593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26572750283620363304971457 19929562712715272478728593)
            ·
              refine ⟨14947172034536454359046445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19929562712715272478728593 14947172034536454359046445)
              ·
                refine ⟨5605189512951170384642417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14947172034536454359046445 5605189512951170384642417)
                ·
                  refine ⟨4203892134713377788481813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5605189512951170384642417 4203892134713377788481813)
                  ·
                    refine ⟨197057443814689583835085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4203892134713377788481813 197057443814689583835085)
                    ·
                      rfl

theorem cell23_1151304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_1151304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151304 prefixEnd_1151304 := by exact prefixLift 1151304
  have htrace : WordTrace (prefixWord ++ tailWord_1151304) baseStart_1151304 baseEnd_1151304 := by
    simpa [prefixWord, tailWord_1151304, baseEnd_1151304] using wordTrace_append hprefix tailTrace_1151304
  have hstable : (prefixWord ++ tailWord_1151304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151304).length < 2 ^ (prefixWord ++ tailWord_1151304).sum := by decide
  have hdescent : baseEnd_1151304 < baseStart_1151304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151326 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_1151326 : Nat := 118140960795 + 1151326 * 2 ^ 59
def prefixEnd_1151326 : Nat := 4983230072969 + 3 ^ 40 * 1151326 * 2
def baseEnd_1151326 : Nat := 591183628018467665430155

theorem tailTrace_1151326 : CollatzResearch.WordTrace tailWord_1151326 prefixEnd_1151326 591183628018467665430155 := by
  unfold tailWord_1151326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5249038628368750958916229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27994872684633338447553221 5249038628368750958916229)
  ·
    refine ⟨984194742819140804796793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5249038628368750958916229 984194742819140804796793)
    ·
      refine ⟨738146057114355603597595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 984194742819140804796793 738146057114355603597595)
      ·
        refine ⟨1107219085671533405396393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738146057114355603597595 1107219085671533405396393)
        ·
          refine ⟨830414314253650054047295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1107219085671533405396393 830414314253650054047295)
          ·
            refine ⟨1245621471380475081070943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830414314253650054047295 1245621471380475081070943)
            ·
              refine ⟨1868432207070712621606415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245621471380475081070943 1868432207070712621606415)
              ·
                refine ⟨2802648310606068932409623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1868432207070712621606415 2802648310606068932409623)
                ·
                  refine ⟨4203972465909103398614435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2802648310606068932409623 4203972465909103398614435)
                  ·
                    refine ⟨6305958698863655097921653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4203972465909103398614435 6305958698863655097921653)
                    ·
                      refine ⟨591183628018467665430155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6305958698863655097921653 591183628018467665430155)
                      ·
                        rfl

theorem cell23_1151326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_1151326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151326 prefixEnd_1151326 := by exact prefixLift 1151326
  have htrace : WordTrace (prefixWord ++ tailWord_1151326) baseStart_1151326 baseEnd_1151326 := by
    simpa [prefixWord, tailWord_1151326, baseEnd_1151326] using wordTrace_append hprefix tailTrace_1151326
  have hstable : (prefixWord ++ tailWord_1151326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151326).length < 2 ^ (prefixWord ++ tailWord_1151326).sum := by decide
  have hdescent : baseEnd_1151326 < baseStart_1151326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151341 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1151341 : Nat := 118140960795 + 1151341 * 2 ^ 59
def prefixEnd_1151341 : Nat := 4983230072969 + 3 ^ 40 * 1151341 * 2
def baseEnd_1151341 : Nat := 591191330228285106742585

theorem tailTrace_1151341 : CollatzResearch.WordTrace tailWord_1151341 prefixEnd_1151341 591191330228285106742585 := by
  unfold tailWord_1151341
  simp only [CollatzResearch.WordTrace]
  refine ⟨41992856121895665233125877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27995237414597110155417251 41992856121895665233125877)
  ·
    refine ⟨3936830261427718615605551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41992856121895665233125877 3936830261427718615605551)
    ·
      refine ⟨5905245392141577923408327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3936830261427718615605551 5905245392141577923408327)
      ·
        refine ⟨8857868088212366885112491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5905245392141577923408327 8857868088212366885112491)
        ·
          refine ⟨13286802132318550327668737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8857868088212366885112491 13286802132318550327668737)
          ·
            refine ⟨9965101599238912745751553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13286802132318550327668737 9965101599238912745751553)
            ·
              refine ⟨7473826199429184559313665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9965101599238912745751553 7473826199429184559313665)
              ·
                refine ⟨5605369649571888419485249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7473826199429184559313665 5605369649571888419485249)
                ·
                  refine ⟨4204027237178916314613937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5605369649571888419485249 4204027237178916314613937)
                  ·
                    refine ⟨3153020427884187235960453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4204027237178916314613937 3153020427884187235960453)
                    ·
                      refine ⟨591191330228285106742585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3153020427884187235960453 591191330228285106742585)
                      ·
                        rfl

theorem cell23_1151341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1151341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151341 prefixEnd_1151341 := by exact prefixLift 1151341
  have htrace : WordTrace (prefixWord ++ tailWord_1151341) baseStart_1151341 baseEnd_1151341 := by
    simpa [prefixWord, tailWord_1151341, baseEnd_1151341] using wordTrace_append hprefix tailTrace_1151341
  have hstable : (prefixWord ++ tailWord_1151341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151341).length < 2 ^ (prefixWord ++ tailWord_1151341).sum := by decide
  have hdescent : baseEnd_1151341 < baseStart_1151341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151401 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 4]
def baseStart_1151401 : Nat := 118140960795 + 1151401 * 2 ^ 59
def prefixEnd_1151401 : Nat := 4983230072969 + 3 ^ 40 * 1151401 * 2
def baseEnd_1151401 : Nat := 591222139067554871992309

theorem tailTrace_1151401 : CollatzResearch.WordTrace tailWord_1151401 prefixEnd_1151401 591222139067554871992309 := by
  unfold tailWord_1151401
  simp only [CollatzResearch.WordTrace]
  refine ⟨41995044501678295480310057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27996696334452196986873371 41995044501678295480310057)
  ·
    refine ⟨31496283376258721610232543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41995044501678295480310057 31496283376258721610232543)
    ·
      refine ⟨47244425064388082415348815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31496283376258721610232543 47244425064388082415348815)
      ·
        refine ⟨70866637596582123623023223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47244425064388082415348815 70866637596582123623023223)
        ·
          refine ⟨106299956394873185434534835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70866637596582123623023223 106299956394873185434534835)
          ·
            refine ⟨159449934592309778151802253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106299956394873185434534835 159449934592309778151802253)
            ·
              refine ⟨59793725472116166806925845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159449934592309778151802253 59793725472116166806925845)
              ·
                refine ⟨2802830881505445319074649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59793725472116166806925845 2802830881505445319074649)
                ·
                  refine ⟨2102123161129083989305987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2802830881505445319074649 2102123161129083989305987)
                  ·
                    refine ⟨3153184741693625983958981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2102123161129083989305987 3153184741693625983958981)
                    ·
                      refine ⟨591222139067554871992309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3153184741693625983958981 591222139067554871992309)
                      ·
                        rfl

theorem cell23_1151401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_1151401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151401 prefixEnd_1151401 := by exact prefixLift 1151401
  have htrace : WordTrace (prefixWord ++ tailWord_1151401) baseStart_1151401 baseEnd_1151401 := by
    simpa [prefixWord, tailWord_1151401, baseEnd_1151401] using wordTrace_append hprefix tailTrace_1151401
  have hstable : (prefixWord ++ tailWord_1151401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151401).length < 2 ^ (prefixWord ++ tailWord_1151401).sum := by decide
  have hdescent : baseEnd_1151401 < baseStart_1151401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151402 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 7]
def baseStart_1151402 : Nat := 118140960795 + 1151402 * 2 ^ 59
def prefixEnd_1151402 : Nat := 4983230072969 + 3 ^ 40 * 1151402 * 2
def baseEnd_1151402 : Nat := 65691405838689929786645

theorem tailTrace_1151402 : CollatzResearch.WordTrace tailWord_1151402 prefixEnd_1151402 65691405838689929786645 := by
  unfold tailWord_1151402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10498770243668668162774115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27996720649783115100730973 10498770243668668162774115)
  ·
    refine ⟨15748155365503002244161173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10498770243668668162774115 15748155365503002244161173)
    ·
      refine ⟨738194782757953230195055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15748155365503002244161173 738194782757953230195055)
      ·
        refine ⟨1107292174136929845292583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738194782757953230195055 1107292174136929845292583)
        ·
          refine ⟨1660938261205394767938875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107292174136929845292583 1660938261205394767938875)
          ·
            refine ⟨2491407391808092151908313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660938261205394767938875 2491407391808092151908313)
            ·
              refine ⟨1868555543856069113931235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2491407391808092151908313 1868555543856069113931235)
              ·
                refine ⟨2802833315784103670896853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1868555543856069113931235 2802833315784103670896853)
                ·
                  refine ⟨65691405838689929786645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2802833315784103670896853 65691405838689929786645)
                  ·
                    rfl

theorem cell23_1151402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_1151402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151402 prefixEnd_1151402 := by exact prefixLift 1151402
  have htrace : WordTrace (prefixWord ++ tailWord_1151402) baseStart_1151402 baseEnd_1151402 := by
    simpa [prefixWord, tailWord_1151402, baseEnd_1151402] using wordTrace_append hprefix tailTrace_1151402
  have hstable : (prefixWord ++ tailWord_1151402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151402).length < 2 ^ (prefixWord ++ tailWord_1151402).sum := by decide
  have hdescent : baseEnd_1151402 < baseStart_1151402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151438 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_1151438 : Nat := 118140960795 + 1151438 * 2 ^ 59
def prefixEnd_1151438 : Nat := 4983230072969 + 3 ^ 40 * 1151438 * 2
def baseEnd_1151438 : Nat := 591241137851771227229639

theorem tailTrace_1151438 : CollatzResearch.WordTrace tailWord_1151438 prefixEnd_1151438 591241137851771227229639 := by
  unfold tailWord_1151438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5249549250318031349925871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27997596001696167199604645 5249549250318031349925871)
  ·
    refine ⟨7874323875477047024888807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5249549250318031349925871 7874323875477047024888807)
    ·
      refine ⟨11811485813215570537333211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7874323875477047024888807 11811485813215570537333211)
      ·
        refine ⟨17717228719823355805999817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11811485813215570537333211 17717228719823355805999817)
        ·
          refine ⟨13287921539867516854499863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17717228719823355805999817 13287921539867516854499863)
          ·
            refine ⟨19931882309801275281749795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13287921539867516854499863 19931882309801275281749795)
            ·
              refine ⟨29897823464701912922624693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19931882309801275281749795 29897823464701912922624693)
              ·
                refine ⟨2802920949815804336496065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29897823464701912922624693 2802920949815804336496065)
                ·
                  refine ⟨2102190712361853252372049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2802920949815804336496065 2102190712361853252372049)
                  ·
                    refine ⟨1576643034271389939279037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2102190712361853252372049 1576643034271389939279037)
                    ·
                      refine ⟨591241137851771227229639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1576643034271389939279037 591241137851771227229639)
                      ·
                        rfl

theorem cell23_1151438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_1151438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151438 prefixEnd_1151438 := by exact prefixLift 1151438
  have htrace : WordTrace (prefixWord ++ tailWord_1151438) baseStart_1151438 baseEnd_1151438 := by
    simpa [prefixWord, tailWord_1151438, baseEnd_1151438] using wordTrace_append hprefix tailTrace_1151438
  have hstable : (prefixWord ++ tailWord_1151438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151438).length < 2 ^ (prefixWord ++ tailWord_1151438).sum := by decide
  have hdescent : baseEnd_1151438 < baseStart_1151438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151471 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 3, 5]
def baseStart_1151471 : Nat := 118140960795 + 1151471 * 2 ^ 59
def prefixEnd_1151471 : Nat := 4983230072969 + 3 ^ 40 * 1151471 * 2
def baseEnd_1151471 : Nat := 197086027571123199372329

theorem tailTrace_1151471 : CollatzResearch.WordTrace tailWord_1151471 prefixEnd_1151471 197086027571123199372329 := by
  unfold tailWord_1151471
  simp only [CollatzResearch.WordTrace]
  refine ⟨41997597611424697435358267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27998398407616464956905511 41997597611424697435358267)
  ·
    refine ⟨62996396417137046153037401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41997597611424697435358267 62996396417137046153037401)
    ·
      refine ⟨47247297312852784614778051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62996396417137046153037401 47247297312852784614778051)
      ·
        refine ⟨70870945969279176922167077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47247297312852784614778051 70870945969279176922167077)
        ·
          refine ⟨13288302369239845672906327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70870945969279176922167077 13288302369239845672906327)
          ·
            refine ⟨19932453553859768509359491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13288302369239845672906327 19932453553859768509359491)
            ·
              refine ⟨29898680330789652764039237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19932453553859768509359491 29898680330789652764039237)
              ·
                refine ⟨5606002562023059893257357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29898680330789652764039237 5606002562023059893257357)
                ·
                  refine ⟨2102250960758647459971509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5606002562023059893257357 2102250960758647459971509)
                  ·
                    refine ⟨197086027571123199372329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2102250960758647459971509 197086027571123199372329)
                    ·
                      rfl

theorem cell23_1151471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_1151471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151471 prefixEnd_1151471 := by exact prefixLift 1151471
  have htrace : WordTrace (prefixWord ++ tailWord_1151471) baseStart_1151471 baseEnd_1151471 := by
    simpa [prefixWord, tailWord_1151471, baseEnd_1151471] using wordTrace_append hprefix tailTrace_1151471
  have hstable : (prefixWord ++ tailWord_1151471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151471).length < 2 ^ (prefixWord ++ tailWord_1151471).sum := by decide
  have hdescent : baseEnd_1151471 < baseStart_1151471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151538 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_1151538 : Nat := 118140960795 + 1151538 * 2 ^ 59
def prefixEnd_1151538 : Nat := 4983230072969 + 3 ^ 40 * 1151538 * 2
def baseEnd_1151538 : Nat := 591292485917220835979179

theorem tailTrace_1151538 : CollatzResearch.WordTrace tailWord_1151538 prefixEnd_1151538 591292485917220835979179 := by
  unfold tailWord_1151538
  simp only [CollatzResearch.WordTrace]
  refine ⟨10500010325545491969511817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28000027534787978585364845 10500010325545491969511817)
  ·
    refine ⟨7875007744159118977133863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10500010325545491969511817 7875007744159118977133863)
    ·
      refine ⟨11812511616238678465700795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7875007744159118977133863 11812511616238678465700795)
      ·
        refine ⟨17718767424358017698551193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11812511616238678465700795 17718767424358017698551193)
        ·
          refine ⟨13289075568268513273913395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17718767424358017698551193 13289075568268513273913395)
          ·
            refine ⟨19933613352402769910870093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13289075568268513273913395 19933613352402769910870093)
            ·
              refine ⟨7475105007151038716576285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19933613352402769910870093 7475105007151038716576285)
              ·
                refine ⟨2803164377681639518716107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7475105007151038716576285 2803164377681639518716107)
                ·
                  refine ⟨4204746566522459278074161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803164377681639518716107 4204746566522459278074161)
                  ·
                    refine ⟨3153559924891844458555621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4204746566522459278074161 3153559924891844458555621)
                    ·
                      refine ⟨591292485917220835979179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3153559924891844458555621 591292485917220835979179)
                      ·
                        rfl

theorem cell23_1151538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_1151538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151538 prefixEnd_1151538 := by exact prefixLift 1151538
  have htrace : WordTrace (prefixWord ++ tailWord_1151538) baseStart_1151538 baseEnd_1151538 := by
    simpa [prefixWord, tailWord_1151538, baseEnd_1151538] using wordTrace_append hprefix tailTrace_1151538
  have hstable : (prefixWord ++ tailWord_1151538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151538).length < 2 ^ (prefixWord ++ tailWord_1151538).sum := by decide
  have hdescent : baseEnd_1151538 < baseStart_1151538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151545 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1151545 : Nat := 118140960795 + 1151545 * 2 ^ 59
def prefixEnd_1151545 : Nat := 4983230072969 + 3 ^ 40 * 1151545 * 2
def baseEnd_1151545 : Nat := 591296080281802308591647

theorem tailTrace_1151545 : CollatzResearch.WordTrace tailWord_1151545 prefixEnd_1151545 591296080281802308591647 := by
  unfold tailWord_1151545
  simp only [CollatzResearch.WordTrace]
  refine ⟨42000296613156608073552089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28000197742104405382368059 42000296613156608073552089)
  ·
    refine ⟨31500222459867456055164067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42000296613156608073552089 31500222459867456055164067)
    ·
      refine ⟨47250333689801184082746101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31500222459867456055164067 47250333689801184082746101)
      ·
        refine ⟨4429718783418861007757447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47250333689801184082746101 4429718783418861007757447)
        ·
          refine ⟨6644578175128291511636171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4429718783418861007757447 6644578175128291511636171)
          ·
            refine ⟨9966867262692437267454257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6644578175128291511636171 9966867262692437267454257)
            ·
              refine ⟨7475150447019327950590693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9966867262692437267454257 7475150447019327950590693)
              ·
                refine ⟨1401590708816123990735755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7475150447019327950590693 1401590708816123990735755)
                ·
                  refine ⟨2102386063224185986103633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401590708816123990735755 2102386063224185986103633)
                  ·
                    refine ⟨1576789547418139489577725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2102386063224185986103633 1576789547418139489577725)
                    ·
                      refine ⟨591296080281802308591647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1576789547418139489577725 591296080281802308591647)
                      ·
                        rfl

theorem cell23_1151545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1151545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151545 prefixEnd_1151545 := by exact prefixLift 1151545
  have htrace : WordTrace (prefixWord ++ tailWord_1151545) baseStart_1151545 baseEnd_1151545 := by
    simpa [prefixWord, tailWord_1151545, baseEnd_1151545] using wordTrace_append hprefix tailTrace_1151545
  have hstable : (prefixWord ++ tailWord_1151545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151545).length < 2 ^ (prefixWord ++ tailWord_1151545).sum := by decide
  have hdescent : baseEnd_1151545 < baseStart_1151545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151559 : List Nat := [1, 1, 4, 1, 4, 1, 1, 5, 1, 2, 2]
def baseStart_1151559 : Nat := 118140960795 + 1151559 * 2 ^ 59
def prefixEnd_1151559 : Nat := 4983230072969 + 3 ^ 40 * 1151559 * 2
def baseEnd_1151559 : Nat := 591303269010965253816583

theorem tailTrace_1151559 : CollatzResearch.WordTrace tailWord_1151559 prefixEnd_1151559 591303269010965253816583 := by
  unfold tailWord_1151559
  simp only [CollatzResearch.WordTrace]
  refine ⟨42000807235105888464561731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28000538156737258976374487 42000807235105888464561731)
  ·
    refine ⟨63001210852658832696842597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42000807235105888464561731 63001210852658832696842597)
    ·
      refine ⟨11812727034873531130657987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63001210852658832696842597 11812727034873531130657987)
      ·
        refine ⟨17719090552310296695986981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11812727034873531130657987 17719090552310296695986981)
        ·
          refine ⟨3322329478558180630497559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17719090552310296695986981 3322329478558180630497559)
          ·
            refine ⟨4983494217837270945746339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3322329478558180630497559 4983494217837270945746339)
            ·
              refine ⟨7475241326755906418619509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4983494217837270945746339 7475241326755906418619509)
              ·
                refine ⟨700803874383366226745579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7475241326755906418619509 700803874383366226745579)
                ·
                  refine ⟨1051205811575049340118369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700803874383366226745579 1051205811575049340118369)
                  ·
                    refine ⟨788404358681287005088777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1051205811575049340118369 788404358681287005088777)
                    ·
                      refine ⟨591303269010965253816583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788404358681287005088777 591303269010965253816583)
                      ·
                        rfl

theorem cell23_1151559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_1151559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151559 prefixEnd_1151559 := by exact prefixLift 1151559
  have htrace : WordTrace (prefixWord ++ tailWord_1151559) baseStart_1151559 baseEnd_1151559 := by
    simpa [prefixWord, tailWord_1151559, baseEnd_1151559] using wordTrace_append hprefix tailTrace_1151559
  have hstable : (prefixWord ++ tailWord_1151559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151559).length < 2 ^ (prefixWord ++ tailWord_1151559).sum := by decide
  have hdescent : baseEnd_1151559 < baseStart_1151559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151562 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3]
def baseStart_1151562 : Nat := 118140960795 + 1151562 * 2 ^ 59
def prefixEnd_1151562 : Nat := 4983230072969 + 3 ^ 40 * 1151562 * 2
def baseEnd_1151562 : Nat := 591304809452928742079069

theorem tailTrace_1151562 : CollatzResearch.WordTrace tailWord_1151562 prefixEnd_1151562 591304809452928742079069 := by
  unfold tailWord_1151562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10500229163523754994230235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28000611102730013317947293 10500229163523754994230235)
  ·
    refine ⟨15750343745285632491345353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10500229163523754994230235 15750343745285632491345353)
    ·
      refine ⟨11812757808964224368509015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15750343745285632491345353 11812757808964224368509015)
      ·
        refine ⟨17719136713446336552763523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11812757808964224368509015 17719136713446336552763523)
        ·
          refine ⟨26578705070169504829145285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17719136713446336552763523 26578705070169504829145285)
          ·
            refine ⟨4983507200656782155464741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26578705070169504829145285 4983507200656782155464741)
            ·
              refine ⟨934407600123146654149639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4983507200656782155464741 934407600123146654149639)
              ·
                refine ⟨1401611400184719981224459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934407600123146654149639 1401611400184719981224459)
                ·
                  refine ⟨2102417100277079971836689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401611400184719981224459 2102417100277079971836689)
                  ·
                    refine ⟨1576812825207809978877517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2102417100277079971836689 1576812825207809978877517)
                    ·
                      refine ⟨591304809452928742079069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1576812825207809978877517 591304809452928742079069)
                      ·
                        rfl

theorem cell23_1151562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_1151562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151562 prefixEnd_1151562 := by exact prefixLift 1151562
  have htrace : WordTrace (prefixWord ++ tailWord_1151562) baseStart_1151562 baseEnd_1151562 := by
    simpa [prefixWord, tailWord_1151562, baseEnd_1151562] using wordTrace_append hprefix tailTrace_1151562
  have hstable : (prefixWord ++ tailWord_1151562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151562).length < 2 ^ (prefixWord ++ tailWord_1151562).sum := by decide
  have hdescent : baseEnd_1151562 < baseStart_1151562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151575 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 4, 1, 3]
def baseStart_1151575 : Nat := 118140960795 + 1151575 * 2 ^ 59
def prefixEnd_1151575 : Nat := 4983230072969 + 3 ^ 40 * 1151575 * 2
def baseEnd_1151575 : Nat := 591311484701437191216509

theorem tailTrace_1151575 : CollatzResearch.WordTrace tailWord_1151575 prefixEnd_1151575 591311484701437191216509 := by
  unfold tailWord_1151575
  simp only [CollatzResearch.WordTrace]
  refine ⟨42001390803047923197144179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28000927202031948798096119 42001390803047923197144179)
  ·
    refine ⟨63002086204571884795716269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42001390803047923197144179 63002086204571884795716269)
    ·
      refine ⟨23625782326714456798393601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63002086204571884795716269 23625782326714456798393601)
      ·
        refine ⟨17719336745035842598795201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23625782326714456798393601 17719336745035842598795201)
        ·
          refine ⟨13289502558776881949096401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17719336745035842598795201 13289502558776881949096401)
          ·
            refine ⟨9967126919082661461822301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13289502558776881949096401 9967126919082661461822301)
            ·
              refine ⟨3737672594655998048183363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9967126919082661461822301 3737672594655998048183363)
              ·
                refine ⟨5606508891983997072275045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3737672594655998048183363 5606508891983997072275045)
                ·
                  refine ⟨1051220417246999451051571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5606508891983997072275045 1051220417246999451051571)
                  ·
                    refine ⟨1576830625870499176577357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1051220417246999451051571 1576830625870499176577357)
                    ·
                      refine ⟨591311484701437191216509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1576830625870499176577357 591311484701437191216509)
                      ·
                        rfl

theorem cell23_1151575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_1151575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151575 prefixEnd_1151575 := by exact prefixLift 1151575
  have htrace : WordTrace (prefixWord ++ tailWord_1151575) baseStart_1151575 baseEnd_1151575 := by
    simpa [prefixWord, tailWord_1151575, baseEnd_1151575] using wordTrace_append hprefix tailTrace_1151575
  have hstable : (prefixWord ++ tailWord_1151575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151575).length < 2 ^ (prefixWord ++ tailWord_1151575).sum := by decide
  have hdescent : baseEnd_1151575 < baseStart_1151575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151586 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1151586 : Nat := 118140960795 + 1151586 * 2 ^ 59
def prefixEnd_1151586 : Nat := 4983230072969 + 3 ^ 40 * 1151586 * 2
def baseEnd_1151586 : Nat := 197105710996212216059653

theorem tailTrace_1151586 : CollatzResearch.WordTrace tailWord_1151586 prefixEnd_1151586 197105710996212216059653 := by
  unfold tailWord_1151586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10500448001502018018948653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28001194670672048050529741 10500448001502018018948653)
  ·
    refine ⟨3937668000563256757105745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10500448001502018018948653 3937668000563256757105745)
    ·
      refine ⟨2953251000422442567829309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3937668000563256757105745 2953251000422442567829309)
      ·
        refine ⟨1107469125158415962935991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2953251000422442567829309 1107469125158415962935991)
        ·
          refine ⟨1661203687737623944403987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107469125158415962935991 1661203687737623944403987)
          ·
            refine ⟨2491805531606435916605981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661203687737623944403987 2491805531606435916605981)
            ·
              refine ⟨934427074352413468727243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2491805531606435916605981 934427074352413468727243)
              ·
                refine ⟨1401640611528620203090865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934427074352413468727243 1401640611528620203090865)
                ·
                  refine ⟨1051230458646465152318149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1401640611528620203090865 1051230458646465152318149)
                  ·
                    refine ⟨197105710996212216059653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1051230458646465152318149 197105710996212216059653)
                    ·
                      rfl

theorem cell23_1151586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1151586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151586 prefixEnd_1151586 := by exact prefixLift 1151586
  have htrace : WordTrace (prefixWord ++ tailWord_1151586) baseStart_1151586 baseEnd_1151586 := by
    simpa [prefixWord, tailWord_1151586, baseEnd_1151586] using wordTrace_append hprefix tailTrace_1151586
  have hstable : (prefixWord ++ tailWord_1151586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151586).length < 2 ^ (prefixWord ++ tailWord_1151586).sum := by decide
  have hdescent : baseEnd_1151586 < baseStart_1151586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151628 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_1151628 : Nat := 118140960795 + 1151628 * 2 ^ 59
def prefixEnd_1151628 : Nat := 4983230072969 + 3 ^ 40 * 1151628 * 2
def baseEnd_1151628 : Nat := 591338699176125483853765

theorem tailTrace_1151628 : CollatzResearch.WordTrace tailWord_1151628 prefixEnd_1151628 591338699176125483853765 := by
  unfold tailWord_1151628
  simp only [CollatzResearch.WordTrace]
  refine ⟨21001661935927956624411769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28002215914570608832549025 21001661935927956624411769)
  ·
    refine ⟨15751246451945967468308827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21001661935927956624411769 15751246451945967468308827)
    ·
      refine ⟨23626869677918951202463241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15751246451945967468308827 23626869677918951202463241)
      ·
        refine ⟨17720152258439213401847431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23626869677918951202463241 17720152258439213401847431)
        ·
          refine ⟨26580228387658820102771147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17720152258439213401847431 26580228387658820102771147)
          ·
            refine ⟨39870342581488230154156721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26580228387658820102771147 39870342581488230154156721)
            ·
              refine ⟨29902756936116172615617541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39870342581488230154156721 29902756936116172615617541)
              ·
                refine ⟨5606766925521782365428289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29902756936116172615617541 5606766925521782365428289)
                ·
                  refine ⟨4205075194141336774071217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5606766925521782365428289 4205075194141336774071217)
                  ·
                    refine ⟨3153806395606002580553413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4205075194141336774071217 3153806395606002580553413)
                    ·
                      refine ⟨591338699176125483853765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3153806395606002580553413 591338699176125483853765)
                      ·
                        rfl

theorem cell23_1151628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_1151628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151628 prefixEnd_1151628 := by exact prefixLift 1151628
  have htrace : WordTrace (prefixWord ++ tailWord_1151628) baseStart_1151628 baseEnd_1151628 := by
    simpa [prefixWord, tailWord_1151628, baseEnd_1151628] using wordTrace_append hprefix tailTrace_1151628
  have hstable : (prefixWord ++ tailWord_1151628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151628).length < 2 ^ (prefixWord ++ tailWord_1151628).sum := by decide
  have hdescent : baseEnd_1151628 < baseStart_1151628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151692 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 2, 5, 2]
def baseStart_1151692 : Nat := 118140960795 + 1151692 * 2 ^ 59
def prefixEnd_1151692 : Nat := 4983230072969 + 3 ^ 40 * 1151692 * 2
def baseEnd_1151692 : Nat := 591371561938013233453471

theorem tailTrace_1151692 : CollatzResearch.WordTrace tailWord_1151692 prefixEnd_1151692 591371561938013233453471 := by
  unfold tailWord_1151692
  simp only [CollatzResearch.WordTrace]
  refine ⟨21002829071812026089576665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28003772095749368119435553 21002829071812026089576665)
  ·
    refine ⟨15752121803859019567182499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21002829071812026089576665 15752121803859019567182499)
    ·
      refine ⟨23628182705788529350773749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15752121803859019567182499 23628182705788529350773749)
      ·
        refine ⟨2215142128667674626635039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23628182705788529350773749 2215142128667674626635039)
        ·
          refine ⟨3322713193001511939952559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2215142128667674626635039 3322713193001511939952559)
          ·
            refine ⟨4984069789502267909928839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3322713193001511939952559 4984069789502267909928839)
            ·
              refine ⟨7476104684253401864893259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984069789502267909928839 7476104684253401864893259)
              ·
                refine ⟨11214157026380102797339889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7476104684253401864893259 11214157026380102797339889)
                ·
                  refine ⟨8410617769785077098004917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11214157026380102797339889 8410617769785077098004917)
                  ·
                    refine ⟨788495415917350977937961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8410617769785077098004917 788495415917350977937961)
                    ·
                      refine ⟨591371561938013233453471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788495415917350977937961 591371561938013233453471)
                      ·
                        rfl

theorem cell23_1151692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_1151692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151692 prefixEnd_1151692 := by exact prefixLift 1151692
  have htrace : WordTrace (prefixWord ++ tailWord_1151692) baseStart_1151692 baseEnd_1151692 := by
    simpa [prefixWord, tailWord_1151692, baseEnd_1151692] using wordTrace_append hprefix tailTrace_1151692
  have hstable : (prefixWord ++ tailWord_1151692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151692).length < 2 ^ (prefixWord ++ tailWord_1151692).sum := by decide
  have hdescent : baseEnd_1151692 < baseStart_1151692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151728 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 8]
def baseStart_1151728 : Nat := 118140960795 + 1151728 * 2 ^ 59
def prefixEnd_1151728 : Nat := 4983230072969 + 3 ^ 40 * 1151728 * 2
def baseEnd_1151728 : Nat := 65710005249063899178145

theorem tailTrace_1151728 : CollatzResearch.WordTrace tailWord_1151728 prefixEnd_1151728 65710005249063899178145 := by
  unfold tailWord_1151728
  simp only [CollatzResearch.WordTrace]
  refine ⟨21003485585746815163731919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28004647447662420218309225 21003485585746815163731919)
  ·
    refine ⟨31505228378620222745597879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21003485585746815163731919 31505228378620222745597879)
    ·
      refine ⟨47257842567930334118396819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31505228378620222745597879 47257842567930334118396819)
      ·
        refine ⟨70886763851895501177595229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47257842567930334118396819 70886763851895501177595229)
        ·
          refine ⟨26582536444460812941598211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70886763851895501177595229 26582536444460812941598211)
          ·
            refine ⟨39873804666691219412397317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26582536444460812941598211 39873804666691219412397317)
            ·
              refine ⟨7476338375004603639824497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39873804666691219412397317 7476338375004603639824497)
              ·
                refine ⟨5607253781253452729868373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7476338375004603639824497 5607253781253452729868373)
                ·
                  refine ⟨65710005249063899178145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5607253781253452729868373 65710005249063899178145)
                  ·
                    rfl

theorem cell23_1151728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 8].length) (baseStart_1151728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151728 prefixEnd_1151728 := by exact prefixLift 1151728
  have htrace : WordTrace (prefixWord ++ tailWord_1151728) baseStart_1151728 baseEnd_1151728 := by
    simpa [prefixWord, tailWord_1151728, baseEnd_1151728] using wordTrace_append hprefix tailTrace_1151728
  have hstable : (prefixWord ++ tailWord_1151728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151728).length < 2 ^ (prefixWord ++ tailWord_1151728).sum := by decide
  have hdescent : baseEnd_1151728 < baseStart_1151728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151815 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_1151815 : Nat := 118140960795 + 1151815 * 2 ^ 59
def prefixEnd_1151815 : Nat := 4983230072969 + 3 ^ 40 * 1151815 * 2
def baseEnd_1151815 : Nat := 591434720058516252215405

theorem tailTrace_1151815 : CollatzResearch.WordTrace tailWord_1151815 prefixEnd_1151815 591434720058516252215405 := by
  unfold tailWord_1151815
  simp only [CollatzResearch.WordTrace]
  refine ⟨42010144322178444185880899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28006762881452296123920599 42010144322178444185880899)
  ·
    refine ⟨63015216483267666278821349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42010144322178444185880899 63015216483267666278821349)
    ·
      refine ⟨11815353090612687427279003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63015216483267666278821349 11815353090612687427279003)
      ·
        refine ⟨17723029635919031140918505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11815353090612687427279003 17723029635919031140918505)
        ·
          refine ⟨13292272226939273355688879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17723029635919031140918505 13292272226939273355688879)
          ·
            refine ⟨19938408340408910033533319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13292272226939273355688879 19938408340408910033533319)
            ·
              refine ⟨29907612510613365050299979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19938408340408910033533319 29907612510613365050299979)
              ·
                refine ⟨44861418765920047575449969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29907612510613365050299979 44861418765920047575449969)
                ·
                  refine ⟨33646064074440035681587477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44861418765920047575449969 33646064074440035681587477)
                  ·
                    refine ⟨1577159253489376672574413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33646064074440035681587477 1577159253489376672574413)
                    ·
                      refine ⟨591434720058516252215405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1577159253489376672574413 591434720058516252215405)
                      ·
                        rfl

theorem cell23_1151815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_1151815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151815 prefixEnd_1151815 := by exact prefixLift 1151815
  have htrace : WordTrace (prefixWord ++ tailWord_1151815) baseStart_1151815 baseEnd_1151815 := by
    simpa [prefixWord, tailWord_1151815, baseEnd_1151815] using wordTrace_append hprefix tailTrace_1151815
  have hstable : (prefixWord ++ tailWord_1151815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151815).length < 2 ^ (prefixWord ++ tailWord_1151815).sum := by decide
  have hdescent : baseEnd_1151815 < baseStart_1151815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151829 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 5, 2, 2]
def baseStart_1151829 : Nat := 118140960795 + 1151829 * 2 ^ 59
def prefixEnd_1151829 : Nat := 4983230072969 + 3 ^ 40 * 1151829 * 2
def baseEnd_1151829 : Nat := 591441908787679197440341

theorem tailTrace_1151829 : CollatzResearch.WordTrace tailWord_1151829 prefixEnd_1151829 591441908787679197440341 := by
  unfold tailWord_1151829
  simp only [CollatzResearch.WordTrace]
  refine ⟨42010654944127724576890541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28007103296085149717927027 42010654944127724576890541)
  ·
    refine ⟨15753995604047896716333953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42010654944127724576890541 15753995604047896716333953)
    ·
      refine ⟨11815496703035922537250465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15753995604047896716333953 11815496703035922537250465)
      ·
        refine ⟨8861622527276941902937849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11815496703035922537250465 8861622527276941902937849)
        ·
          refine ⟨6646216895457706427203387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8861622527276941902937849 6646216895457706427203387)
          ·
            refine ⟨9969325343186559640805081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6646216895457706427203387 9969325343186559640805081)
            ·
              refine ⟨7476994007389919730603811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9969325343186559640805081 7476994007389919730603811)
              ·
                refine ⟨11215491011084879595905717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7476994007389919730603811 11215491011084879595905717)
                ·
                  refine ⟨1051452282289207462116161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11215491011084879595905717 1051452282289207462116161)
                  ·
                    refine ⟨788589211716905596587121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1051452282289207462116161 788589211716905596587121)
                    ·
                      refine ⟨591441908787679197440341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788589211716905596587121 591441908787679197440341)
                      ·
                        rfl

theorem cell23_1151829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_1151829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151829 prefixEnd_1151829 := by exact prefixLift 1151829
  have htrace : WordTrace (prefixWord ++ tailWord_1151829) baseStart_1151829 baseEnd_1151829 := by
    simpa [prefixWord, tailWord_1151829, baseEnd_1151829] using wordTrace_append hprefix tailTrace_1151829
  have hstable : (prefixWord ++ tailWord_1151829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151829).length < 2 ^ (prefixWord ++ tailWord_1151829).sum := by decide
  have hdescent : baseEnd_1151829 < baseStart_1151829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151865 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 2, 7]
def baseStart_1151865 : Nat := 118140960795 + 1151865 * 2 ^ 59
def prefixEnd_1151865 : Nat := 4983230072969 + 3 ^ 40 * 1151865 * 2
def baseEnd_1151865 : Nat := 197153464697080352196725

theorem tailTrace_1151865 : CollatzResearch.WordTrace tailWord_1151865 prefixEnd_1151865 197153464697080352196725 := by
  unfold tailWord_1151865
  simp only [CollatzResearch.WordTrace]
  refine ⟨42011967971997302725201049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28007978647998201816800699 42011967971997302725201049)
  ·
    refine ⟨31508975978997977043900787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42011967971997302725201049 31508975978997977043900787)
    ·
      refine ⟨47263463968496965565851181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31508975978997977043900787 47263463968496965565851181)
      ·
        refine ⟨17723798988186362087194193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47263463968496965565851181 17723798988186362087194193)
        ·
          refine ⟨13292849241139771565395645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17723798988186362087194193 13292849241139771565395645)
          ·
            refine ⟨4984818465427414337023367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13292849241139771565395645 4984818465427414337023367)
            ·
              refine ⟨7477227698141121505535051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984818465427414337023367 7477227698141121505535051)
              ·
                refine ⟨11215841547211682258302577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7477227698141121505535051 11215841547211682258302577)
                ·
                  refine ⟨8411881160408761693726933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11215841547211682258302577 8411881160408761693726933)
                  ·
                    refine ⟨197153464697080352196725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8411881160408761693726933 197153464697080352196725)
                    ·
                      rfl

theorem cell23_1151865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_1151865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151865 prefixEnd_1151865 := by exact prefixLift 1151865
  have htrace : WordTrace (prefixWord ++ tailWord_1151865) baseStart_1151865 baseEnd_1151865 := by
    simpa [prefixWord, tailWord_1151865, baseEnd_1151865] using wordTrace_append hprefix tailTrace_1151865
  have hstable : (prefixWord ++ tailWord_1151865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151865).length < 2 ^ (prefixWord ++ tailWord_1151865).sum := by decide
  have hdescent : baseEnd_1151865 < baseStart_1151865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151879 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_1151879 : Nat := 118140960795 + 1151879 * 2 ^ 59
def prefixEnd_1151879 : Nat := 4983230072969 + 3 ^ 40 * 1151879 * 2
def baseEnd_1151879 : Nat := 591467582820404001815111

theorem tailTrace_1151879 : CollatzResearch.WordTrace tailWord_1151879 prefixEnd_1151879 591467582820404001815111 := by
  unfold tailWord_1151879
  simp only [CollatzResearch.WordTrace]
  refine ⟨42012478593946583116210691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28008319062631055410807127 42012478593946583116210691)
  ·
    refine ⟨63018717890919874674316037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42012478593946583116210691 63018717890919874674316037)
    ·
      refine ⟨11816009604547476501434257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63018717890919874674316037 11816009604547476501434257)
      ·
        refine ⟨8862007203410607376075693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11816009604547476501434257 8862007203410607376075693)
        ·
          refine ⟨3323252701278977766028385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8862007203410607376075693 3323252701278977766028385)
          ·
            refine ⟨2492439525959233324521289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3323252701278977766028385 2492439525959233324521289)
            ·
              refine ⟨1869329644469424993390967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2492439525959233324521289 1869329644469424993390967)
              ·
                refine ⟨2803994466704137490086451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869329644469424993390967 2803994466704137490086451)
                ·
                  refine ⟨4205991700056206235129677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803994466704137490086451 4205991700056206235129677)
                  ·
                    refine ⟨1577246887521077338173629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4205991700056206235129677 1577246887521077338173629)
                    ·
                      refine ⟨591467582820404001815111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1577246887521077338173629 591467582820404001815111)
                      ·
                        rfl

theorem cell23_1151879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_1151879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151879 prefixEnd_1151879 := by exact prefixLift 1151879
  have htrace : WordTrace (prefixWord ++ tailWord_1151879) baseStart_1151879 baseEnd_1151879 := by
    simpa [prefixWord, tailWord_1151879, baseEnd_1151879] using wordTrace_append hprefix tailTrace_1151879
  have hstable : (prefixWord ++ tailWord_1151879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151879).length < 2 ^ (prefixWord ++ tailWord_1151879).sum := by decide
  have hdescent : baseEnd_1151879 < baseStart_1151879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151889 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 1, 3, 2]
def baseStart_1151889 : Nat := 118140960795 + 1151889 * 2 ^ 59
def prefixEnd_1151889 : Nat := 4983230072969 + 3 ^ 40 * 1151889 * 2
def baseEnd_1151889 : Nat := 591472717626948962690065

theorem tailTrace_1151889 : CollatzResearch.WordTrace tailWord_1151889 prefixEnd_1151889 591472717626948962690065 := by
  unfold tailWord_1151889
  simp only [CollatzResearch.WordTrace]
  refine ⟨42012843323910354824074721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28008562215940236549383147 42012843323910354824074721)
  ·
    refine ⟨31509632492932766118056041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42012843323910354824074721 31509632492932766118056041)
    ·
      refine ⟨23632224369699574588542031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31509632492932766118056041 23632224369699574588542031)
      ·
        refine ⟨35448336554549361882813047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23632224369699574588542031 35448336554549361882813047)
        ·
          refine ⟨53172504831824042824219571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35448336554549361882813047 53172504831824042824219571)
          ·
            refine ⟨79758757247736064236329357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53172504831824042824219571 79758757247736064236329357)
            ·
              refine ⟨29909533967901024088623509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79758757247736064236329357 29909533967901024088623509)
              ·
                refine ⟨1402009404745360504154227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29909533967901024088623509 1402009404745360504154227)
                ·
                  refine ⟨2103014107118040756231341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402009404745360504154227 2103014107118040756231341)
                  ·
                    refine ⟨788630290169265283586753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2103014107118040756231341 788630290169265283586753)
                    ·
                      refine ⟨591472717626948962690065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788630290169265283586753 591472717626948962690065)
                      ·
                        rfl

theorem cell23_1151889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 3, 2].length) (baseStart_1151889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151889 prefixEnd_1151889 := by exact prefixLift 1151889
  have htrace : WordTrace (prefixWord ++ tailWord_1151889) baseStart_1151889 baseEnd_1151889 := by
    simpa [prefixWord, tailWord_1151889, baseEnd_1151889] using wordTrace_append hprefix tailTrace_1151889
  have hstable : (prefixWord ++ tailWord_1151889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151889).length < 2 ^ (prefixWord ++ tailWord_1151889).sum := by decide
  have hdescent : baseEnd_1151889 < baseStart_1151889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151892 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1151892 : Nat := 118140960795 + 1151892 * 2 ^ 59
def prefixEnd_1151892 : Nat := 4983230072969 + 3 ^ 40 * 1151892 * 2
def baseEnd_1151892 : Nat := 591474258068912450952551

theorem tailTrace_1151892 : CollatzResearch.WordTrace tailWord_1151892 prefixEnd_1151892 591474258068912450952551 := by
  unfold tailWord_1151892
  simp only [CollatzResearch.WordTrace]
  refine ⟨21006476371449743168216965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28008635161932990890955953 21006476371449743168216965)
  ·
    refine ⟨3938714319646826844040681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21006476371449743168216965 3938714319646826844040681)
    ·
      refine ⟨2954035739735120133030511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3938714319646826844040681 2954035739735120133030511)
      ·
        refine ⟨4431053609602680199545767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954035739735120133030511 4431053609602680199545767)
        ·
          refine ⟨6646580414404020299318651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4431053609602680199545767 6646580414404020299318651)
          ·
            refine ⟨9969870621606030448977977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6646580414404020299318651 9969870621606030448977977)
            ·
              refine ⟨7477402966204522836733483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9969870621606030448977977 7477402966204522836733483)
              ·
                refine ⟨11216104449306784255100225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7477402966204522836733483 11216104449306784255100225)
                ·
                  refine ⟨8412078336980088191325169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11216104449306784255100225 8412078336980088191325169)
                  ·
                    refine ⟨6309058752735066143493877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8412078336980088191325169 6309058752735066143493877)
                    ·
                      refine ⟨591474258068912450952551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6309058752735066143493877 591474258068912450952551)
                      ·
                        rfl

theorem cell23_1151892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1151892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151892 prefixEnd_1151892 := by exact prefixLift 1151892
  have htrace : WordTrace (prefixWord ++ tailWord_1151892) baseStart_1151892 baseEnd_1151892 := by
    simpa [prefixWord, tailWord_1151892, baseEnd_1151892] using wordTrace_append hprefix tailTrace_1151892
  have hstable : (prefixWord ++ tailWord_1151892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151892).length < 2 ^ (prefixWord ++ tailWord_1151892).sum := by decide
  have hdescent : baseEnd_1151892 < baseStart_1151892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151895 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 1, 8]
def baseStart_1151895 : Nat := 118140960795 + 1151895 * 2 ^ 59
def prefixEnd_1151895 : Nat := 4983230072969 + 3 ^ 40 * 1151895 * 2
def baseEnd_1151895 : Nat := 197158599503625313071679

theorem tailTrace_1151895 : CollatzResearch.WordTrace tailWord_1151895 prefixEnd_1151895 197158599503625313071679 := by
  unfold tailWord_1151895
  simp only [CollatzResearch.WordTrace]
  refine ⟨42013062161888617848793139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28008708107925745232528759 42013062161888617848793139)
  ·
    refine ⟨63019593242832926773189709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42013062161888617848793139 63019593242832926773189709)
    ·
      refine ⟨23632347466062347539946141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63019593242832926773189709 23632347466062347539946141)
      ·
        refine ⟨8862130299773380327479803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23632347466062347539946141 8862130299773380327479803)
        ·
          refine ⟨13293195449660070491219705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8862130299773380327479803 13293195449660070491219705)
          ·
            refine ⟨9969896587245052868414779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13293195449660070491219705 9969896587245052868414779)
            ·
              refine ⟨14954844880867579302622169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9969896587245052868414779 14954844880867579302622169)
              ·
                refine ⟨11216133660650684476966627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14954844880867579302622169 11216133660650684476966627)
                ·
                  refine ⟨16824200490976026715449941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11216133660650684476966627 16824200490976026715449941)
                  ·
                    refine ⟨197158599503625313071679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16824200490976026715449941 197158599503625313071679)
                    ·
                      rfl

theorem cell23_1151895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_1151895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151895 prefixEnd_1151895 := by exact prefixLift 1151895
  have htrace : WordTrace (prefixWord ++ tailWord_1151895) baseStart_1151895 baseEnd_1151895 := by
    simpa [prefixWord, tailWord_1151895, baseEnd_1151895] using wordTrace_append hprefix tailTrace_1151895
  have hstable : (prefixWord ++ tailWord_1151895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151895).length < 2 ^ (prefixWord ++ tailWord_1151895).sum := by decide
  have hdescent : baseEnd_1151895 < baseStart_1151895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151900 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_1151900 : Nat := 118140960795 + 1151900 * 2 ^ 59
def prefixEnd_1151900 : Nat := 4983230072969 + 3 ^ 40 * 1151900 * 2
def baseEnd_1151900 : Nat := 591478365914148419652515

theorem tailTrace_1151900 : CollatzResearch.WordTrace tailWord_1151900 prefixEnd_1151900 591478365914148419652515 := by
  unfold tailWord_1151900
  simp only [CollatzResearch.WordTrace]
  refine ⟨21006622263435251851362577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28008829684580335801816769 21006622263435251851362577)
  ·
    refine ⟨15754966697576438888521933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21006622263435251851362577 15754966697576438888521933)
    ·
      refine ⟨5908112511591164583195725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15754966697576438888521933 5908112511591164583195725)
      ·
        refine ⟨2215542191846686718698397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5908112511591164583195725 2215542191846686718698397)
        ·
          refine ⟨830828321942507519511899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2215542191846686718698397 830828321942507519511899)
          ·
            refine ⟨1246242482913761279267849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830828321942507519511899 1246242482913761279267849)
            ·
              refine ⟨934681862185320959450887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246242482913761279267849 934681862185320959450887)
              ·
                refine ⟨1402022793277981439176331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934681862185320959450887 1402022793277981439176331)
                ·
                  refine ⟨2103034189916972158764497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402022793277981439176331 2103034189916972158764497)
                  ·
                    refine ⟨1577275642437729119073373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2103034189916972158764497 1577275642437729119073373)
                    ·
                      refine ⟨591478365914148419652515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1577275642437729119073373 591478365914148419652515)
                      ·
                        rfl

theorem cell23_1151900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_1151900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151900 prefixEnd_1151900 := by exact prefixLift 1151900
  have htrace : WordTrace (prefixWord ++ tailWord_1151900) baseStart_1151900 baseEnd_1151900 := by
    simpa [prefixWord, tailWord_1151900, baseEnd_1151900] using wordTrace_append hprefix tailTrace_1151900
  have hstable : (prefixWord ++ tailWord_1151900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151900).length < 2 ^ (prefixWord ++ tailWord_1151900).sum := by decide
  have hdescent : baseEnd_1151900 < baseStart_1151900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151915 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 4]
def baseStart_1151915 : Nat := 118140960795 + 1151915 * 2 ^ 59
def prefixEnd_1151915 : Nat := 4983230072969 + 3 ^ 40 * 1151915 * 2
def baseEnd_1151915 : Nat := 591486068123965860964945

theorem tailTrace_1151915 : CollatzResearch.WordTrace tailWord_1151915 prefixEnd_1151915 591486068123965860964945 := by
  unfold tailWord_1151915
  simp only [CollatzResearch.WordTrace]
  refine ⟨42013791621816161264521199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28009194414544107509680799 42013791621816161264521199)
  ·
    refine ⟨63020687432724241896781799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42013791621816161264521199 63020687432724241896781799)
    ·
      refine ⟨94531031149086362845172699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63020687432724241896781799 94531031149086362845172699)
      ·
        refine ⟨141796546723629544267759049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94531031149086362845172699 141796546723629544267759049)
        ·
          refine ⟨106347410042722158200819287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141796546723629544267759049 106347410042722158200819287)
          ·
            refine ⟨159521115064083237301228931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106347410042722158200819287 159521115064083237301228931)
            ·
              refine ⟨239281672596124855951843397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159521115064083237301228931 239281672596124855951843397)
              ·
                refine ⟨44865313611773410490970637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239281672596124855951843397 44865313611773410490970637)
                ·
                  refine ⟨16824492604415028934113989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44865313611773410490970637 16824492604415028934113989)
                  ·
                    refine ⟨3154592363327817925146373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16824492604415028934113989 3154592363327817925146373)
                    ·
                      refine ⟨591486068123965860964945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3154592363327817925146373 591486068123965860964945)
                      ·
                        rfl

theorem cell23_1151915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 4].length) (baseStart_1151915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151915 prefixEnd_1151915 := by exact prefixLift 1151915
  have htrace : WordTrace (prefixWord ++ tailWord_1151915) baseStart_1151915 baseEnd_1151915 := by
    simpa [prefixWord, tailWord_1151915, baseEnd_1151915] using wordTrace_append hprefix tailTrace_1151915
  have hstable : (prefixWord ++ tailWord_1151915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151915).length < 2 ^ (prefixWord ++ tailWord_1151915).sum := by decide
  have hdescent : baseEnd_1151915 < baseStart_1151915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151936 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 1, 4, 2]
def baseStart_1151936 : Nat := 118140960795 + 1151936 * 2 ^ 59
def prefixEnd_1151936 : Nat := 4983230072969 + 3 ^ 40 * 1151936 * 2
def baseEnd_1151936 : Nat := 591496851217710278802349

theorem tailTrace_1151936 : CollatzResearch.WordTrace tailWord_1151936 prefixEnd_1151936 591496851217710278802349 := by
  unfold tailWord_1151936
  simp only [CollatzResearch.WordTrace]
  refine ⟨21007278777370040925517831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28009705036493387900690441 21007278777370040925517831)
  ·
    refine ⟨31510918166055061388276747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21007278777370040925517831 31510918166055061388276747)
    ·
      refine ⟨47266377249082592082415121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31510918166055061388276747 47266377249082592082415121)
      ·
        refine ⟨35449782936811944061811341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47266377249082592082415121 35449782936811944061811341)
        ·
          refine ⟨13293668601304479023179253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35449782936811944061811341 13293668601304479023179253)
          ·
            refine ⟨1246281431372294908423055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13293668601304479023179253 1246281431372294908423055)
            ·
              refine ⟨1869422147058442362634583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246281431372294908423055 1869422147058442362634583)
              ·
                refine ⟨2804133220587663543951875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869422147058442362634583 2804133220587663543951875)
                ·
                  refine ⟨4206199830881495315927813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804133220587663543951875 4206199830881495315927813)
                  ·
                    refine ⟨788662468290280371736465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4206199830881495315927813 788662468290280371736465)
                    ·
                      refine ⟨591496851217710278802349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788662468290280371736465 591496851217710278802349)
                      ·
                        rfl

theorem cell23_1151936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 4, 2].length) (baseStart_1151936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151936 prefixEnd_1151936 := by exact prefixLift 1151936
  have htrace : WordTrace (prefixWord ++ tailWord_1151936) baseStart_1151936 baseEnd_1151936 := by
    simpa [prefixWord, tailWord_1151936, baseEnd_1151936] using wordTrace_append hprefix tailTrace_1151936
  have hstable : (prefixWord ++ tailWord_1151936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151936).length < 2 ^ (prefixWord ++ tailWord_1151936).sum := by decide
  have hdescent : baseEnd_1151936 < baseStart_1151936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151940 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_1151940 : Nat := 118140960795 + 1151940 * 2 ^ 59
def prefixEnd_1151940 : Nat := 4983230072969 + 3 ^ 40 * 1151940 * 2
def baseEnd_1151940 : Nat := 591498905140328263152331

theorem tailTrace_1151940 : CollatzResearch.WordTrace tailWord_1151940 prefixEnd_1151940 591498905140328263152331 := by
  unfold tailWord_1151940
  simp only [CollatzResearch.WordTrace]
  refine ⟨21007351723362795267090637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28009802297817060356120849 21007351723362795267090637)
  ·
    refine ⟨7877756896261048225158989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21007351723362795267090637 7877756896261048225158989)
    ·
      refine ⟨2954158836097893084434621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7877756896261048225158989 2954158836097893084434621)
      ·
        refine ⟨1107809563536709906662983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2954158836097893084434621 1107809563536709906662983)
        ·
          refine ⟨1661714345305064859994475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107809563536709906662983 1661714345305064859994475)
          ·
            refine ⟨2492571517957597289991713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661714345305064859994475 2492571517957597289991713)
            ·
              refine ⟨1869428638468197967493785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2492571517957597289991713 1869428638468197967493785)
              ·
                refine ⟨1402071478851148475620339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1869428638468197967493785 1402071478851148475620339)
                ·
                  refine ⟨2103107218276722713430509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402071478851148475620339 2103107218276722713430509)
                  ·
                    refine ⟨788665206853771017536441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2103107218276722713430509 788665206853771017536441)
                    ·
                      refine ⟨591498905140328263152331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788665206853771017536441 591498905140328263152331)
                      ·
                        rfl

theorem cell23_1151940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_1151940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151940 prefixEnd_1151940 := by exact prefixLift 1151940
  have htrace : WordTrace (prefixWord ++ tailWord_1151940) baseStart_1151940 baseEnd_1151940 := by
    simpa [prefixWord, tailWord_1151940, baseEnd_1151940] using wordTrace_append hprefix tailTrace_1151940
  have hstable : (prefixWord ++ tailWord_1151940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151940).length < 2 ^ (prefixWord ++ tailWord_1151940).sum := by decide
  have hdescent : baseEnd_1151940 < baseStart_1151940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1151992 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_1151992 : Nat := 118140960795 + 1151992 * 2 ^ 59
def prefixEnd_1151992 : Nat := 4983230072969 + 3 ^ 40 * 1151992 * 2
def baseEnd_1151992 : Nat := 591525606134362059702091

theorem tailTrace_1151992 : CollatzResearch.WordTrace tailWord_1151992 prefixEnd_1151992 591525606134362059702091 := by
  unfold tailWord_1151992
  simp only [CollatzResearch.WordTrace]
  refine ⟨21008300021268601707537115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28011066695024802276716153 21008300021268601707537115)
  ·
    refine ⟨31512450031902902561305673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21008300021268601707537115 31512450031902902561305673)
    ·
      refine ⟨23634337523927176920979255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31512450031902902561305673 23634337523927176920979255)
      ·
        refine ⟨35451506285890765381468883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23634337523927176920979255 35451506285890765381468883)
        ·
          refine ⟨53177259428836148072203325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35451506285890765381468883 53177259428836148072203325)
          ·
            refine ⟨19941472285813555527076247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53177259428836148072203325 19941472285813555527076247)
            ·
              refine ⟨29912208428720333290614371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19941472285813555527076247 29912208428720333290614371)
              ·
                refine ⟨44868312643080499935921557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29912208428720333290614371 44868312643080499935921557)
                ·
                  refine ⟨2103202155144398434496323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44868312643080499935921557 2103202155144398434496323)
                  ·
                    refine ⟨3154803232716597651744485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2103202155144398434496323 3154803232716597651744485)
                    ·
                      refine ⟨591525606134362059702091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3154803232716597651744485 591525606134362059702091)
                      ·
                        rfl

theorem cell23_1151992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_1151992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1151992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1151992 prefixEnd_1151992 := by exact prefixLift 1151992
  have htrace : WordTrace (prefixWord ++ tailWord_1151992) baseStart_1151992 baseEnd_1151992 := by
    simpa [prefixWord, tailWord_1151992, baseEnd_1151992] using wordTrace_append hprefix tailTrace_1151992
  have hstable : (prefixWord ++ tailWord_1151992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1151992).length < 2 ^ (prefixWord ++ tailWord_1151992).sum := by decide
  have hdescent : baseEnd_1151992 < baseStart_1151992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1151992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152070 : List Nat := [6, 1, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1152070 : Nat := 118140960795 + 1152070 * 2 ^ 59
def prefixEnd_1152070 : Nat := 4983230072969 + 3 ^ 40 * 1152070 * 2
def baseEnd_1152070 : Nat := 197188552541804251508911

theorem tailTrace_1152070 : CollatzResearch.WordTrace tailWord_1152070 prefixEnd_1152070 197188552541804251508911 := by
  unfold tailWord_1152070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1313107654257956960512927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28012963290836415157609109 1313107654257956960512927)
  ·
    refine ⟨1969661481386935440769391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1313107654257956960512927 1969661481386935440769391)
    ·
      refine ⟨2954492222080403161154087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1969661481386935440769391 2954492222080403161154087)
      ·
        refine ⟨4431738333120604741731131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954492222080403161154087 4431738333120604741731131)
        ·
          refine ⟨6647607499680907112596697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4431738333120604741731131 6647607499680907112596697)
          ·
            refine ⟨4985705624760680334447523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6647607499680907112596697 4985705624760680334447523)
            ·
              refine ⟨7478558437141020501671285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4985705624760680334447523 7478558437141020501671285)
              ·
                refine ⟨701114853481970672031683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7478558437141020501671285 701114853481970672031683)
                ·
                  refine ⟨1051672280222956008047525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701114853481970672031683 1051672280222956008047525)
                  ·
                    refine ⟨197188552541804251508911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1051672280222956008047525 197188552541804251508911)
                    ·
                      rfl

theorem cell23_1152070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1152070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152070 prefixEnd_1152070 := by exact prefixLift 1152070
  have htrace : WordTrace (prefixWord ++ tailWord_1152070) baseStart_1152070 baseEnd_1152070 := by
    simpa [prefixWord, tailWord_1152070, baseEnd_1152070] using wordTrace_append hprefix tailTrace_1152070
  have hstable : (prefixWord ++ tailWord_1152070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152070).length < 2 ^ (prefixWord ++ tailWord_1152070).sum := by decide
  have hdescent : baseEnd_1152070 < baseStart_1152070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152149 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_1152149 : Nat := 118140960795 + 1152149 * 2 ^ 59
def prefixEnd_1152149 : Nat := 4983230072969 + 3 ^ 40 * 1152149 * 2
def baseEnd_1152149 : Nat := 591606222597117945438869

theorem tailTrace_1152149 : CollatzResearch.WordTrace tailWord_1152149 prefixEnd_1152149 591606222597117945438869 := by
  unfold tailWord_1152149
  simp only [CollatzResearch.WordTrace]
  refine ⟨42022326302968419228539501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28014884201978946152359667 42022326302968419228539501)
  ·
    refine ⟨15758372363613157210702313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42022326302968419228539501 15758372363613157210702313)
    ·
      refine ⟨11818779272709867908026735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15758372363613157210702313 11818779272709867908026735)
      ·
        refine ⟨17728168909064801862040103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11818779272709867908026735 17728168909064801862040103)
        ·
          refine ⟨26592253363597202793060155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17728168909064801862040103 26592253363597202793060155)
          ·
            refine ⟨39888380045395804189590233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26592253363597202793060155 39888380045395804189590233)
            ·
              refine ⟨29916285034046853142192675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39888380045395804189590233 29916285034046853142192675)
              ·
                refine ⟨44874427551070279713289013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29916285034046853142192675 44874427551070279713289013)
                ·
                  refine ⟨4206977582912838723120845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44874427551070279713289013 4206977582912838723120845)
                  ·
                    refine ⟨1577616593592314521170317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4206977582912838723120845 1577616593592314521170317)
                    ·
                      refine ⟨591606222597117945438869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1577616593592314521170317 591606222597117945438869)
                      ·
                        rfl

theorem cell23_1152149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_1152149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152149 prefixEnd_1152149 := by exact prefixLift 1152149
  have htrace : WordTrace (prefixWord ++ tailWord_1152149) baseStart_1152149 baseEnd_1152149 := by
    simpa [prefixWord, tailWord_1152149, baseEnd_1152149] using wordTrace_append hprefix tailTrace_1152149
  have hstable : (prefixWord ++ tailWord_1152149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152149).length < 2 ^ (prefixWord ++ tailWord_1152149).sum := by decide
  have hdescent : baseEnd_1152149 < baseStart_1152149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152170 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1152170 : Nat := 118140960795 + 1152170 * 2 ^ 59
def prefixEnd_1152170 : Nat := 4983230072969 + 3 ^ 40 * 1152170 * 2
def baseEnd_1152170 : Nat := 591617005690862363276273

theorem tailTrace_1152170 : CollatzResearch.WordTrace tailWord_1152170 prefixEnd_1152170 591617005690862363276273 := by
  unfold tailWord_1152170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10505773058973084953763491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28015394823928226543369309 10505773058973084953763491)
  ·
    refine ⟨15758659588459627430645237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10505773058973084953763491 15758659588459627430645237)
    ·
      refine ⟨1477374336418090071622991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15758659588459627430645237 1477374336418090071622991)
      ·
        refine ⟨2216061504627135107434487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1477374336418090071622991 2216061504627135107434487)
        ·
          refine ⟨3324092256940702661151731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216061504627135107434487 3324092256940702661151731)
          ·
            refine ⟨4986138385411053991727597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324092256940702661151731 4986138385411053991727597)
            ·
              refine ⟨1869801894529145246897849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4986138385411053991727597 1869801894529145246897849)
              ·
                refine ⟨1402351420896858935173387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1869801894529145246897849 1402351420896858935173387)
                ·
                  refine ⟨2103527131345288402760081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402351420896858935173387 2103527131345288402760081)
                  ·
                    refine ⟨1577645348508966302070061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2103527131345288402760081 1577645348508966302070061)
                    ·
                      refine ⟨591617005690862363276273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1577645348508966302070061 591617005690862363276273)
                      ·
                        rfl

theorem cell23_1152170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1152170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152170 prefixEnd_1152170 := by exact prefixLift 1152170
  have htrace : WordTrace (prefixWord ++ tailWord_1152170) baseStart_1152170 baseEnd_1152170 := by
    simpa [prefixWord, tailWord_1152170, baseEnd_1152170] using wordTrace_append hprefix tailTrace_1152170
  have hstable : (prefixWord ++ tailWord_1152170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152170).length < 2 ^ (prefixWord ++ tailWord_1152170).sum := by decide
  have hdescent : baseEnd_1152170 < baseStart_1152170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152176 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 3, 3, 2]
def baseStart_1152176 : Nat := 118140960795 + 1152176 * 2 ^ 59
def prefixEnd_1152176 : Nat := 4983230072969 + 3 ^ 40 * 1152176 * 2
def baseEnd_1152176 : Nat := 591620086574789339801245

theorem tailTrace_1152176 : CollatzResearch.WordTrace tailWord_1152176 prefixEnd_1152176 591620086574789339801245 := by
  unfold tailWord_1152176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21011655536935301419886191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28015540715913735226514921 21011655536935301419886191)
  ·
    refine ⟨31517483305402952129829287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21011655536935301419886191 31517483305402952129829287)
    ·
      refine ⟨47276224958104428194743931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31517483305402952129829287 47276224958104428194743931)
      ·
        refine ⟨70914337437156642292115897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47276224958104428194743931 70914337437156642292115897)
        ·
          refine ⟨53185753077867481719086923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70914337437156642292115897 53185753077867481719086923)
          ·
            refine ⟨79778629616801222578630385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53185753077867481719086923 79778629616801222578630385)
            ·
              refine ⟨59833972212600916933972789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79778629616801222578630385 59833972212600916933972789)
              ·
                refine ⟨5609434894931335962559949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59833972212600916933972789 5609434894931335962559949)
                ·
                  refine ⟨2103538085599250985959981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5609434894931335962559949 2103538085599250985959981)
                  ·
                    refine ⟨788826782099719119734993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2103538085599250985959981 788826782099719119734993)
                    ·
                      refine ⟨591620086574789339801245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788826782099719119734993 591620086574789339801245)
                      ·
                        rfl

theorem cell23_1152176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 3, 2].length) (baseStart_1152176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152176 prefixEnd_1152176 := by exact prefixLift 1152176
  have htrace : WordTrace (prefixWord ++ tailWord_1152176) baseStart_1152176 baseEnd_1152176 := by
    simpa [prefixWord, tailWord_1152176, baseEnd_1152176] using wordTrace_append hprefix tailTrace_1152176
  have hstable : (prefixWord ++ tailWord_1152176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152176).length < 2 ^ (prefixWord ++ tailWord_1152176).sum := by decide
  have hdescent : baseEnd_1152176 < baseStart_1152176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152216 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 2, 6]
def baseStart_1152216 : Nat := 118140960795 + 1152216 * 2 ^ 59
def prefixEnd_1152216 : Nat := 4983230072969 + 3 ^ 40 * 1152216 * 2
def baseEnd_1152216 : Nat := 197213541933656394433687

theorem tailTrace_1152216 : CollatzResearch.WordTrace tailWord_1152216 prefixEnd_1152216 197213541933656394433687 := by
  unfold tailWord_1152216
  simp only [CollatzResearch.WordTrace]
  refine ⟨21012384996862844835614251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28016513329150459780819001 21012384996862844835614251)
  ·
    refine ⟨31518577495294267253421377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21012384996862844835614251 31518577495294267253421377)
    ·
      refine ⟨23638933121470700440066033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31518577495294267253421377 23638933121470700440066033)
      ·
        refine ⟨17729199841103025330049525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23638933121470700440066033 17729199841103025330049525)
        ·
          refine ⟨1662112485103408624692143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17729199841103025330049525 1662112485103408624692143)
          ·
            refine ⟨2493168727655112937038215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662112485103408624692143 2493168727655112937038215)
            ·
              refine ⟨3739753091482669405557323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493168727655112937038215 3739753091482669405557323)
              ·
                refine ⟨5609629637224004108335985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3739753091482669405557323 5609629637224004108335985)
                ·
                  refine ⟨4207222227918003081251989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5609629637224004108335985 4207222227918003081251989)
                  ·
                    refine ⟨197213541933656394433687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4207222227918003081251989 197213541933656394433687)
                    ·
                      rfl

theorem cell23_1152216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_1152216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152216 prefixEnd_1152216 := by exact prefixLift 1152216
  have htrace : WordTrace (prefixWord ++ tailWord_1152216) baseStart_1152216 baseEnd_1152216 := by
    simpa [prefixWord, tailWord_1152216, baseEnd_1152216] using wordTrace_append hprefix tailTrace_1152216
  have hstable : (prefixWord ++ tailWord_1152216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152216).length < 2 ^ (prefixWord ++ tailWord_1152216).sum := by decide
  have hdescent : baseEnd_1152216 < baseStart_1152216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152257 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_1152257 : Nat := 118140960795 + 1152257 * 2 ^ 59
def prefixEnd_1152257 : Nat := 4983230072969 + 3 ^ 40 * 1152257 * 2
def baseEnd_1152257 : Nat := 591661678507803522888373

theorem tailTrace_1152257 : CollatzResearch.WordTrace tailWord_1152257 prefixEnd_1152257 591661678507803522888373 := by
  unfold tailWord_1152257
  simp only [CollatzResearch.WordTrace]
  refine ⟨42026265386577153673471025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28017510257718102448980683 42026265386577153673471025)
  ·
    refine ⟨31519699039932865255103269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42026265386577153673471025 31519699039932865255103269)
    ·
      refine ⟨5909943569987412235331863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31519699039932865255103269 5909943569987412235331863)
      ·
        refine ⟨8864915354981118352997795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5909943569987412235331863 8864915354981118352997795)
        ·
          refine ⟨13297373032471677529496693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8864915354981118352997795 13297373032471677529496693)
          ·
            refine ⟨1246628721794219768390315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13297373032471677529496693 1246628721794219768390315)
            ·
              refine ⟨1869943082691329652585473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246628721794219768390315 1869943082691329652585473)
              ·
                refine ⟨1402457312018497239439105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1869943082691329652585473 1402457312018497239439105)
                ·
                  refine ⟨1051842984013872929579329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1402457312018497239439105 1051842984013872929579329)
                  ·
                    refine ⟨788882238010404697184497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1051842984013872929579329 788882238010404697184497)
                    ·
                      refine ⟨591661678507803522888373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788882238010404697184497 591661678507803522888373)
                      ·
                        rfl

theorem cell23_1152257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_1152257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152257 prefixEnd_1152257 := by exact prefixLift 1152257
  have htrace : WordTrace (prefixWord ++ tailWord_1152257) baseStart_1152257 baseEnd_1152257 := by
    simpa [prefixWord, tailWord_1152257, baseEnd_1152257] using wordTrace_append hprefix tailTrace_1152257
  have hstable : (prefixWord ++ tailWord_1152257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152257).length < 2 ^ (prefixWord ++ tailWord_1152257).sum := by decide
  have hdescent : baseEnd_1152257 < baseStart_1152257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152274 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1152274 : Nat := 118140960795 + 1152274 * 2 ^ 59
def prefixEnd_1152274 : Nat := 4983230072969 + 3 ^ 40 * 1152274 * 2
def baseEnd_1152274 : Nat := 591670407678929956375795

theorem tailTrace_1152274 : CollatzResearch.WordTrace tailWord_1152274 prefixEnd_1152274 591670407678929956375795 := by
  unfold tailWord_1152274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10506721356878891394209969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28017923618343710384559917 10506721356878891394209969)
  ·
    refine ⟨7880041017659168545657477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10506721356878891394209969 7880041017659168545657477)
    ·
      refine ⟨1477507690811094102310777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7880041017659168545657477 1477507690811094102310777)
      ·
        refine ⟨1108130768108320576733083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1477507690811094102310777 1108130768108320576733083)
        ·
          refine ⟨1662196152162480865099625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108130768108320576733083 1662196152162480865099625)
          ·
            refine ⟨1246647114121860648824719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1662196152162480865099625 1246647114121860648824719)
            ·
              refine ⟨1869970671182790973237079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246647114121860648824719 1869970671182790973237079)
              ·
                refine ⟨2804956006774186459855619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869970671182790973237079 2804956006774186459855619)
                ·
                  refine ⟨4207434010161279689783429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804956006774186459855619 4207434010161279689783429)
                  ·
                    refine ⟨788893876905239941834393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4207434010161279689783429 788893876905239941834393)
                    ·
                      refine ⟨591670407678929956375795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788893876905239941834393 591670407678929956375795)
                      ·
                        rfl

theorem cell23_1152274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1152274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152274 prefixEnd_1152274 := by exact prefixLift 1152274
  have htrace : WordTrace (prefixWord ++ tailWord_1152274) baseStart_1152274 baseEnd_1152274 := by
    simpa [prefixWord, tailWord_1152274, baseEnd_1152274] using wordTrace_append hprefix tailTrace_1152274
  have hstable : (prefixWord ++ tailWord_1152274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152274).length < 2 ^ (prefixWord ++ tailWord_1152274).sum := by decide
  have hdescent : baseEnd_1152274 < baseStart_1152274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152289 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 1, 10]
def baseStart_1152289 : Nat := 118140960795 + 1152289 * 2 ^ 59
def prefixEnd_1152289 : Nat := 4983230072969 + 3 ^ 40 * 1152289 * 2
def baseEnd_1152289 : Nat := 197226036629582465896075

theorem tailTrace_1152289 : CollatzResearch.WordTrace tailWord_1152289 prefixEnd_1152289 197226036629582465896075 := by
  unfold tailWord_1152289
  simp only [CollatzResearch.WordTrace]
  refine ⟨42027432522461223138635921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28018288348307482092423947 42027432522461223138635921)
  ·
    refine ⟨31520574391845917353976941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42027432522461223138635921 31520574391845917353976941)
    ·
      refine ⟨11820215396942219007741353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31520574391845917353976941 11820215396942219007741353)
      ·
        refine ⟨8865161547706664255806015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11820215396942219007741353 8865161547706664255806015)
        ·
          refine ⟨13297742321559996383709023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8865161547706664255806015 13297742321559996383709023)
          ·
            refine ⟨19946613482339994575563535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13297742321559996383709023 19946613482339994575563535)
            ·
              refine ⟨29919920223509991863345303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19946613482339994575563535 29919920223509991863345303)
              ·
                refine ⟨44879880335264987795017955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29919920223509991863345303 44879880335264987795017955)
                ·
                  refine ⟨67319820502897481692526933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44879880335264987795017955 67319820502897481692526933)
                  ·
                    refine ⟨197226036629582465896075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 67319820502897481692526933 197226036629582465896075)
                    ·
                      rfl

theorem cell23_1152289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_1152289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152289 prefixEnd_1152289 := by exact prefixLift 1152289
  have htrace : WordTrace (prefixWord ++ tailWord_1152289) baseStart_1152289 baseEnd_1152289 := by
    simpa [prefixWord, tailWord_1152289, baseEnd_1152289] using wordTrace_append hprefix tailTrace_1152289
  have hstable : (prefixWord ++ tailWord_1152289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152289).length < 2 ^ (prefixWord ++ tailWord_1152289).sum := by decide
  have hdescent : baseEnd_1152289 < baseStart_1152289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152336 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 6]
def baseStart_1152336 : Nat := 118140960795 + 1152336 * 2 ^ 59
def prefixEnd_1152336 : Nat := 4983230072969 + 3 ^ 40 * 1152336 * 2
def baseEnd_1152336 : Nat := 65744693719945412644501

theorem tailTrace_1152336 : CollatzResearch.WordTrace tailWord_1152336 prefixEnd_1152336 65744693719945412644501 := by
  unfold tailWord_1152336
  simp only [CollatzResearch.WordTrace]
  refine ⟨21014573376645475082798431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28019431168860633443731241 21014573376645475082798431)
  ·
    refine ⟨31521860064968212624197647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21014573376645475082798431 31521860064968212624197647)
    ·
      refine ⟨47282790097452318936296471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31521860064968212624197647 47282790097452318936296471)
      ·
        refine ⟨70924185146178478404444707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47282790097452318936296471 70924185146178478404444707)
        ·
          refine ⟨106386277719267717606667061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70924185146178478404444707 106386277719267717606667061)
          ·
            refine ⟨9973713536181348525625037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106386277719267717606667061 9973713536181348525625037)
            ·
              refine ⟨3740142576068005697109389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9973713536181348525625037 3740142576068005697109389)
              ·
                refine ⟨1402553466025502136416021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3740142576068005697109389 1402553466025502136416021)
                ·
                  refine ⟨65744693719945412644501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1402553466025502136416021 65744693719945412644501)
                  ·
                    rfl

theorem cell23_1152336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 6].length) (baseStart_1152336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152336 prefixEnd_1152336 := by exact prefixLift 1152336
  have htrace : WordTrace (prefixWord ++ tailWord_1152336) baseStart_1152336 baseEnd_1152336 := by
    simpa [prefixWord, tailWord_1152336, baseEnd_1152336] using wordTrace_append hprefix tailTrace_1152336
  have hstable : (prefixWord ++ tailWord_1152336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152336).length < 2 ^ (prefixWord ++ tailWord_1152336).sum := by decide
  have hdescent : baseEnd_1152336 < baseStart_1152336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152346 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3]
def baseStart_1152346 : Nat := 118140960795 + 1152346 * 2 ^ 59
def prefixEnd_1152346 : Nat := 4983230072969 + 3 ^ 40 * 1152346 * 2
def baseEnd_1152346 : Nat := 591707378286053674675463

theorem tailTrace_1152346 : CollatzResearch.WordTrace tailWord_1152346 prefixEnd_1152346 591707378286053674675463 := by
  unfold tailWord_1152346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10507377870813680468365223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28019674322169814582307261 10507377870813680468365223)
  ·
    refine ⟨15761066806220520702547835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10507377870813680468365223 15761066806220520702547835)
    ·
      refine ⟨23641600209330781053821753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15761066806220520702547835 23641600209330781053821753)
      ·
        refine ⟨17731200156998085790366315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23641600209330781053821753 17731200156998085790366315)
        ·
          refine ⟨26596800235497128685549473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17731200156998085790366315 26596800235497128685549473)
          ·
            refine ⟨19947600176622846514162105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26596800235497128685549473 19947600176622846514162105)
            ·
              refine ⟨14960700132467134885621579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19947600176622846514162105 14960700132467134885621579)
              ·
                refine ⟨22441050198700702328432369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14960700132467134885621579 22441050198700702328432369)
                ·
                  refine ⟨16830787649025526746324277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22441050198700702328432369 16830787649025526746324277)
                  ·
                    refine ⟨1577886342096143132467901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16830787649025526746324277 1577886342096143132467901)
                    ·
                      refine ⟨591707378286053674675463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1577886342096143132467901 591707378286053674675463)
                      ·
                        rfl

theorem cell23_1152346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_1152346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152346 prefixEnd_1152346 := by exact prefixLift 1152346
  have htrace : WordTrace (prefixWord ++ tailWord_1152346) baseStart_1152346 baseEnd_1152346 := by
    simpa [prefixWord, tailWord_1152346, baseEnd_1152346] using wordTrace_append hprefix tailTrace_1152346
  have hstable : (prefixWord ++ tailWord_1152346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152346).length < 2 ^ (prefixWord ++ tailWord_1152346).sum := by decide
  have hdescent : baseEnd_1152346 < baseStart_1152346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152413 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1152413 : Nat := 118140960795 + 1152413 * 2 ^ 59
def prefixEnd_1152413 : Nat := 4983230072969 + 3 ^ 40 * 1152413 * 2
def baseEnd_1152413 : Nat := 197247260496634970845885

theorem tailTrace_1152413 : CollatzResearch.WordTrace tailWord_1152413 prefixEnd_1152413 197247260496634970845885 := by
  unfold tailWord_1152413
  simp only [CollatzResearch.WordTrace]
  refine ⟨42031955174011992316149893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28021303449341328210766595 42031955174011992316149893)
  ·
    refine ⟨7880991595127248559278105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42031955174011992316149893 7880991595127248559278105)
    ·
      refine ⟨5910743696345436419458579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7880991595127248559278105 5910743696345436419458579)
      ·
        refine ⟨8866115544518154629187869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5910743696345436419458579 8866115544518154629187869)
        ·
          refine ⟨3324793329194307985945451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8866115544518154629187869 3324793329194307985945451)
          ·
            refine ⟨4987189993791461978918177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324793329194307985945451 4987189993791461978918177)
            ·
              refine ⟨3740392495343596484188633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4987189993791461978918177 3740392495343596484188633)
              ·
                refine ⟨2805294371507697363141475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3740392495343596484188633 2805294371507697363141475)
                ·
                  refine ⟨4207941557261546044712213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805294371507697363141475 4207941557261546044712213)
                  ·
                    refine ⟨197247260496634970845885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4207941557261546044712213 197247260496634970845885)
                    ·
                      rfl

theorem cell23_1152413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1152413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152413 prefixEnd_1152413 := by exact prefixLift 1152413
  have htrace : WordTrace (prefixWord ++ tailWord_1152413) baseStart_1152413 baseEnd_1152413 := by
    simpa [prefixWord, tailWord_1152413, baseEnd_1152413] using wordTrace_append hprefix tailTrace_1152413
  have hstable : (prefixWord ++ tailWord_1152413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152413).length < 2 ^ (prefixWord ++ tailWord_1152413).sum := by decide
  have hdescent : baseEnd_1152413 < baseStart_1152413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152420 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 7, 2, 2]
def baseStart_1152420 : Nat := 118140960795 + 1152420 * 2 ^ 59
def prefixEnd_1152420 : Nat := 4983230072969 + 3 ^ 40 * 1152420 * 2
def baseEnd_1152420 : Nat := 591745375854486385150123

theorem tailTrace_1152420 : CollatzResearch.WordTrace tailWord_1152420 prefixEnd_1152420 591745375854486385150123 := by
  unfold tailWord_1152420
  simp only [CollatzResearch.WordTrace]
  refine ⟨21016105242493316255827357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28021473656657755007769809 21016105242493316255827357)
  ·
    refine ⟨7881039465934993595935259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21016105242493316255827357 7881039465934993595935259)
    ·
      refine ⟨11821559198902490393902889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7881039465934993595935259 11821559198902490393902889)
      ·
        refine ⟨8866169399176867795427167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11821559198902490393902889 8866169399176867795427167)
        ·
          refine ⟨13299254098765301693140751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8866169399176867795427167 13299254098765301693140751)
          ·
            refine ⟨19948881148147952539711127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13299254098765301693140751 19948881148147952539711127)
            ·
              refine ⟨29923321722221928809566691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19948881148147952539711127 29923321722221928809566691)
              ·
                refine ⟨44884982583332893214350037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29923321722221928809566691 44884982583332893214350037)
                ·
                  refine ⟨1051991779296864684711329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 44884982583332893214350037 1051991779296864684711329)
                  ·
                    refine ⟨788993834472648513533497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1051991779296864684711329 788993834472648513533497)
                    ·
                      refine ⟨591745375854486385150123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 788993834472648513533497 591745375854486385150123)
                      ·
                        rfl

theorem cell23_1152420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_1152420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152420 prefixEnd_1152420 := by exact prefixLift 1152420
  have htrace : WordTrace (prefixWord ++ tailWord_1152420) baseStart_1152420 baseEnd_1152420 := by
    simpa [prefixWord, tailWord_1152420, baseEnd_1152420] using wordTrace_append hprefix tailTrace_1152420
  have hstable : (prefixWord ++ tailWord_1152420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152420).length < 2 ^ (prefixWord ++ tailWord_1152420).sum := by decide
  have hdescent : baseEnd_1152420 < baseStart_1152420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152423 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1152423 : Nat := 118140960795 + 1152423 * 2 ^ 59
def prefixEnd_1152423 : Nat := 4983230072969 + 3 ^ 40 * 1152423 * 2
def baseEnd_1152423 : Nat := 591746916296449873412609

theorem tailTrace_1152423 : CollatzResearch.WordTrace tailWord_1152423 prefixEnd_1152423 591746916296449873412609 := by
  unfold tailWord_1152423
  simp only [CollatzResearch.WordTrace]
  refine ⟨42032319903975764024013923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28021546602650509349342615 42032319903975764024013923)
  ·
    refine ⟨63048479855963646036020885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42032319903975764024013923 63048479855963646036020885)
    ·
      refine ⟨2955397493248295907938479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63048479855963646036020885 2955397493248295907938479)
      ·
        refine ⟨4433096239872443861907719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2955397493248295907938479 4433096239872443861907719)
        ·
          refine ⟨6649644359808665792861579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4433096239872443861907719 6649644359808665792861579)
          ·
            refine ⟨9974466539712998689292369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6649644359808665792861579 9974466539712998689292369)
            ·
              refine ⟨7480849904784749016969277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9974466539712998689292369 7480849904784749016969277)
              ·
                refine ⟨2805318714294280881363479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7480849904784749016969277 2805318714294280881363479)
                ·
                  refine ⟨4207978071441421322045219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805318714294280881363479 4207978071441421322045219)
                  ·
                    refine ⟨6311967107162131983067829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4207978071441421322045219 6311967107162131983067829)
                    ·
                      refine ⟨591746916296449873412609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6311967107162131983067829 591746916296449873412609)
                      ·
                        rfl

theorem cell23_1152423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1152423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152423 prefixEnd_1152423 := by exact prefixLift 1152423
  have htrace : WordTrace (prefixWord ++ tailWord_1152423) baseStart_1152423 baseEnd_1152423 := by
    simpa [prefixWord, tailWord_1152423, baseEnd_1152423] using wordTrace_append hprefix tailTrace_1152423
  have hstable : (prefixWord ++ tailWord_1152423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152423).length < 2 ^ (prefixWord ++ tailWord_1152423).sum := by decide
  have hdescent : baseEnd_1152423 < baseStart_1152423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152437 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_1152437 : Nat := 118140960795 + 1152437 * 2 ^ 59
def prefixEnd_1152437 : Nat := 4983230072969 + 3 ^ 40 * 1152437 * 2
def baseEnd_1152437 : Nat := 591754105025612818637545

theorem tailTrace_1152437 : CollatzResearch.WordTrace tailWord_1152437 prefixEnd_1152437 591754105025612818637545 := by
  unfold tailWord_1152437
  simp only [CollatzResearch.WordTrace]
  refine ⟨42032830525925044415023565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28021887017283362943349043 42032830525925044415023565)
  ·
    refine ⟨15762311447221891655633837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42032830525925044415023565 15762311447221891655633837)
    ·
      refine ⟨5910866792708209370862689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15762311447221891655633837 5910866792708209370862689)
      ·
        refine ⟨4433150094531157028147017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5910866792708209370862689 4433150094531157028147017)
        ·
          refine ⟨3324862570898367771110263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4433150094531157028147017 3324862570898367771110263)
          ·
            refine ⟨4987293856347551656665395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324862570898367771110263 4987293856347551656665395)
            ·
              refine ⟨7480940784521327484998093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4987293856347551656665395 7480940784521327484998093)
              ·
                refine ⟨2805352794195497806874285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7480940784521327484998093 2805352794195497806874285)
                ·
                  refine ⟨1052007297823311677577857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2805352794195497806874285 1052007297823311677577857)
                  ·
                    refine ⟨789005473367483758183393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1052007297823311677577857 789005473367483758183393)
                    ·
                      refine ⟨591754105025612818637545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 789005473367483758183393 591754105025612818637545)
                      ·
                        rfl

theorem cell23_1152437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_1152437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152437 prefixEnd_1152437 := by exact prefixLift 1152437
  have htrace : WordTrace (prefixWord ++ tailWord_1152437) baseStart_1152437 baseEnd_1152437 := by
    simpa [prefixWord, tailWord_1152437, baseEnd_1152437] using wordTrace_append hprefix tailTrace_1152437
  have hstable : (prefixWord ++ tailWord_1152437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152437).length < 2 ^ (prefixWord ++ tailWord_1152437).sum := by decide
  have hdescent : baseEnd_1152437 < baseStart_1152437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152460 : List Nat := [2, 2, 1, 4, 2, 3, 2, 7]
def baseStart_1152460 : Nat := 118140960795 + 1152460 * 2 ^ 59
def prefixEnd_1152460 : Nat := 4983230072969 + 3 ^ 40 * 1152460 * 2
def baseEnd_1152460 : Nat := 21917256114098749209257

theorem tailTrace_1152460 : CollatzResearch.WordTrace tailWord_1152460 prefixEnd_1152460 21917256114098749209257 := by
  unfold tailWord_1152460
  simp only [CollatzResearch.WordTrace]
  refine ⟨21016834702420859671555417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28022446269894479562073889 21016834702420859671555417)
  ·
    refine ⟨15762626026815644753666563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21016834702420859671555417 15762626026815644753666563)
    ·
      refine ⟨23643939040223467130499845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15762626026815644753666563 23643939040223467130499845)
      ·
        refine ⟨4433238570041900086968721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23643939040223467130499845 4433238570041900086968721)
        ·
          refine ⟨3324928927531425065226541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4433238570041900086968721 3324928927531425065226541)
          ·
            refine ⟨1246848347824284399459953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3324928927531425065226541 1246848347824284399459953)
            ·
              refine ⟨935136260868213299594965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246848347824284399459953 935136260868213299594965)
              ·
                refine ⟨21917256114098749209257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 935136260868213299594965 21917256114098749209257)
                ·
                  rfl

theorem cell23_1152460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 7].length) (baseStart_1152460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152460 prefixEnd_1152460 := by exact prefixLift 1152460
  have htrace : WordTrace (prefixWord ++ tailWord_1152460) baseStart_1152460 baseEnd_1152460 := by
    simpa [prefixWord, tailWord_1152460, baseEnd_1152460] using wordTrace_append hprefix tailTrace_1152460
  have hstable : (prefixWord ++ tailWord_1152460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152460).length < 2 ^ (prefixWord ++ tailWord_1152460).sum := by decide
  have hdescent : baseEnd_1152460 < baseStart_1152460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152504 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 2, 1, 3]
def baseStart_1152504 : Nat := 118140960795 + 1152504 * 2 ^ 59
def prefixEnd_1152504 : Nat := 4983230072969 + 3 ^ 40 * 1152504 * 2
def baseEnd_1152504 : Nat := 591788508229464056499737

theorem tailTrace_1152504 : CollatzResearch.WordTrace tailWord_1152504 prefixEnd_1152504 591788508229464056499737 := by
  unfold tailWord_1152504
  simp only [CollatzResearch.WordTrace]
  refine ⟨21017637108341157428856283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28023516144454876571808377 21017637108341157428856283)
  ·
    refine ⟨31526455662511736143284425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21017637108341157428856283 31526455662511736143284425)
    ·
      refine ⟨23644841746883802107463319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31526455662511736143284425 23644841746883802107463319)
      ·
        refine ⟨35467262620325703161194979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23644841746883802107463319 35467262620325703161194979)
        ·
          refine ⟨53200893930488554741792469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35467262620325703161194979 53200893930488554741792469)
          ·
            refine ⟨1246895951495825501760761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53200893930488554741792469 1246895951495825501760761)
            ·
              refine ⟨935171963621869126320571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246895951495825501760761 935171963621869126320571)
              ·
                refine ⟨1402757945432803689480857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935171963621869126320571 1402757945432803689480857)
                ·
                  refine ⟨1052068459074602767110643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1402757945432803689480857 1052068459074602767110643)
                  ·
                    refine ⟨1578102688611904150665965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1052068459074602767110643 1578102688611904150665965)
                    ·
                      refine ⟨591788508229464056499737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1578102688611904150665965 591788508229464056499737)
                      ·
                        rfl

theorem cell23_1152504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 2, 1, 3].length) (baseStart_1152504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152504 prefixEnd_1152504 := by exact prefixLift 1152504
  have htrace : WordTrace (prefixWord ++ tailWord_1152504) baseStart_1152504 baseEnd_1152504 := by
    simpa [prefixWord, tailWord_1152504, baseEnd_1152504] using wordTrace_append hprefix tailTrace_1152504
  have hstable : (prefixWord ++ tailWord_1152504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152504).length < 2 ^ (prefixWord ++ tailWord_1152504).sum := by decide
  have hdescent : baseEnd_1152504 < baseStart_1152504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152514 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1152514 : Nat := 118140960795 + 1152514 * 2 ^ 59
def prefixEnd_1152514 : Nat := 4983230072969 + 3 ^ 40 * 1152514 * 2
def baseEnd_1152514 : Nat := 591793643036009017374691

theorem tailTrace_1152514 : CollatzResearch.WordTrace tailWord_1152514 prefixEnd_1152514 591793643036009017374691 := by
  unfold tailWord_1152514
  simp only [CollatzResearch.WordTrace]
  refine ⟨10508909736661521641394149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28023759297764057710384397 10508909736661521641394149)
  ·
    refine ⟨1970420575624035307761403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10508909736661521641394149 1970420575624035307761403)
    ·
      refine ⟨2955630863436052961642105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1970420575624035307761403 2955630863436052961642105)
      ·
        refine ⟨2216723147577039721231579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2955630863436052961642105 2216723147577039721231579)
        ·
          refine ⟨3325084721365559581847369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216723147577039721231579 3325084721365559581847369)
          ·
            refine ⟨2493813541024169686385527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3325084721365559581847369 2493813541024169686385527)
            ·
              refine ⟨3740720311536254529578291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493813541024169686385527 3740720311536254529578291)
              ·
                refine ⟨5611080467304381794367437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3740720311536254529578291 5611080467304381794367437)
                ·
                  refine ⟨2104155175239143172887789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5611080467304381794367437 2104155175239143172887789)
                  ·
                    refine ⟨789058190714678689832921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2104155175239143172887789 789058190714678689832921)
                    ·
                      refine ⟨591793643036009017374691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 789058190714678689832921 591793643036009017374691)
                      ·
                        rfl

theorem cell23_1152514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1152514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152514 prefixEnd_1152514 := by exact prefixLift 1152514
  have htrace : WordTrace (prefixWord ++ tailWord_1152514) baseStart_1152514 baseEnd_1152514 := by
    simpa [prefixWord, tailWord_1152514, baseEnd_1152514] using wordTrace_append hprefix tailTrace_1152514
  have hstable : (prefixWord ++ tailWord_1152514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152514).length < 2 ^ (prefixWord ++ tailWord_1152514).sum := by decide
  have hdescent : baseEnd_1152514 < baseStart_1152514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152544 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 2, 2, 2]
def baseStart_1152544 : Nat := 118140960795 + 1152544 * 2 ^ 59
def prefixEnd_1152544 : Nat := 4983230072969 + 3 ^ 40 * 1152544 * 2
def baseEnd_1152544 : Nat := 591809047455643899999553

theorem tailTrace_1152544 : CollatzResearch.WordTrace tailWord_1152544 prefixEnd_1152544 591809047455643899999553 := by
  unfold tailWord_1152544
  simp only [CollatzResearch.WordTrace]
  refine ⟨21018366568268700844584343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28024488757691601126112457 21018366568268700844584343)
  ·
    refine ⟨31527549852403051266876515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21018366568268700844584343 31527549852403051266876515)
    ·
      refine ⟨47291324778604576900314773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31527549852403051266876515 47291324778604576900314773)
      ·
        refine ⟨2216780848997089542202255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47291324778604576900314773 2216780848997089542202255)
        ·
          refine ⟨3325171273495634313303383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216780848997089542202255 3325171273495634313303383)
          ·
            refine ⟨4987756910243451469955075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325171273495634313303383 4987756910243451469955075)
            ·
              refine ⟨7481635365365177204932613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4987756910243451469955075 7481635365365177204932613)
              ·
                refine ⟨1402806631005970725924865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7481635365365177204932613 1402806631005970725924865)
                ·
                  refine ⟨1052104973254478044443649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1402806631005970725924865 1052104973254478044443649)
                  ·
                    refine ⟨789078729940858533332737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1052104973254478044443649 789078729940858533332737)
                    ·
                      refine ⟨591809047455643899999553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 789078729940858533332737 591809047455643899999553)
                      ·
                        rfl

theorem cell23_1152544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_1152544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152544 prefixEnd_1152544 := by exact prefixLift 1152544
  have htrace : WordTrace (prefixWord ++ tailWord_1152544) baseStart_1152544 baseEnd_1152544 := by
    simpa [prefixWord, tailWord_1152544, baseEnd_1152544] using wordTrace_append hprefix tailTrace_1152544
  have hstable : (prefixWord ++ tailWord_1152544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152544).length < 2 ^ (prefixWord ++ tailWord_1152544).sum := by decide
  have hdescent : baseEnd_1152544 < baseStart_1152544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152570 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2]
def baseStart_1152570 : Nat := 118140960795 + 1152570 * 2 ^ 59
def prefixEnd_1152570 : Nat := 4983230072969 + 3 ^ 40 * 1152570 * 2
def baseEnd_1152570 : Nat := 591822397952660798274433

theorem tailTrace_1152570 : CollatzResearch.WordTrace tailWord_1152570 prefixEnd_1152570 591822397952660798274433 := by
  unfold tailWord_1152570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10509420358610802032403791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28025120956295472086410109 10509420358610802032403791)
  ·
    refine ⟨15764130537916203048605687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10509420358610802032403791 15764130537916203048605687)
    ·
      refine ⟨23646195806874304572908531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15764130537916203048605687 23646195806874304572908531)
      ·
        refine ⟨35469293710311456859362797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23646195806874304572908531 35469293710311456859362797)
        ·
          refine ⟨13300985141366796322261049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35469293710311456859362797 13300985141366796322261049)
          ·
            refine ⟨9975738856025097241695787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13300985141366796322261049 9975738856025097241695787)
            ·
              refine ⟨14963608284037645862543681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9975738856025097241695787 14963608284037645862543681)
              ·
                refine ⟨11222706213028234396907761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14963608284037645862543681 11222706213028234396907761)
                ·
                  refine ⟨8417029659771175797680821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11222706213028234396907761 8417029659771175797680821)
                  ·
                    refine ⟨789096530603547731032577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8417029659771175797680821 789096530603547731032577)
                    ·
                      refine ⟨591822397952660798274433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 789096530603547731032577 591822397952660798274433)
                      ·
                        rfl

theorem cell23_1152570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2].length) (baseStart_1152570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152570 prefixEnd_1152570 := by exact prefixLift 1152570
  have htrace : WordTrace (prefixWord ++ tailWord_1152570) baseStart_1152570 baseEnd_1152570 := by
    simpa [prefixWord, tailWord_1152570, baseEnd_1152570] using wordTrace_append hprefix tailTrace_1152570
  have hstable : (prefixWord ++ tailWord_1152570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152570).length < 2 ^ (prefixWord ++ tailWord_1152570).sum := by decide
  have hdescent : baseEnd_1152570 < baseStart_1152570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152674 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 6]
def baseStart_1152674 : Nat := 118140960795 + 1152674 * 2 ^ 59
def prefixEnd_1152674 : Nat := 4983230072969 + 3 ^ 40 * 1152674 * 2
def baseEnd_1152674 : Nat := 65763977771192043485995

theorem tailTrace_1152674 : CollatzResearch.WordTrace tailWord_1152674 prefixEnd_1152674 65763977771192043485995 := by
  unfold tailWord_1152674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10510368656516608472850269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28027649750710955927600717 10510368656516608472850269)
  ·
    refine ⟨3941388246193728177318851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10510368656516608472850269 3941388246193728177318851)
    ·
      refine ⟨5912082369290592265978277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3941388246193728177318851 5912082369290592265978277)
      ·
        refine ⟨1108515444241986049870927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5912082369290592265978277 1108515444241986049870927)
        ·
          refine ⟨1662773166362979074806391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108515444241986049870927 1662773166362979074806391)
          ·
            refine ⟨2494159749544468612209587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662773166362979074806391 2494159749544468612209587)
            ·
              refine ⟨3741239624316702918314381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494159749544468612209587 3741239624316702918314381)
              ·
                refine ⟨1402964859118763594367893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3741239624316702918314381 1402964859118763594367893)
                ·
                  refine ⟨65763977771192043485995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1402964859118763594367893 65763977771192043485995)
                  ·
                    rfl

theorem cell23_1152674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_1152674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152674 prefixEnd_1152674 := by exact prefixLift 1152674
  have htrace : WordTrace (prefixWord ++ tailWord_1152674) baseStart_1152674 baseEnd_1152674 := by
    simpa [prefixWord, tailWord_1152674, baseEnd_1152674] using wordTrace_append hprefix tailTrace_1152674
  have hstable : (prefixWord ++ tailWord_1152674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152674).length < 2 ^ (prefixWord ++ tailWord_1152674).sum := by decide
  have hdescent : baseEnd_1152674 < baseStart_1152674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152700 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_1152700 : Nat := 118140960795 + 1152700 * 2 ^ 59
def prefixEnd_1152700 : Nat := 4983230072969 + 3 ^ 40 * 1152700 * 2
def baseEnd_1152700 : Nat := 197296383479248429882945

theorem tailTrace_1152700 : CollatzResearch.WordTrace tailWord_1152700 prefixEnd_1152700 197296383479248429882945 := by
  unfold tailWord_1152700
  simp only [CollatzResearch.WordTrace]
  refine ⟨21021211461986120165923777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28028281949314826887898369 21021211461986120165923777)
  ·
    refine ⟨15765908596489590124442833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21021211461986120165923777 15765908596489590124442833)
    ·
      refine ⟨11824431447367192593332125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15765908596489590124442833 11824431447367192593332125)
      ·
        refine ⟨4434161792762697222499547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11824431447367192593332125 4434161792762697222499547)
        ·
          refine ⟨6651242689144045833749321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4434161792762697222499547 6651242689144045833749321)
          ·
            refine ⟨4988432016858034375311991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6651242689144045833749321 4988432016858034375311991)
            ·
              refine ⟨7482648025287051562967987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4988432016858034375311991 7482648025287051562967987)
              ·
                refine ⟨11223972037930577344451981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7482648025287051562967987 11223972037930577344451981)
                ·
                  refine ⟨4208989514223966504169493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11223972037930577344451981 4208989514223966504169493)
                  ·
                    refine ⟨197296383479248429882945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4208989514223966504169493 197296383479248429882945)
                    ·
                      rfl

theorem cell23_1152700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_1152700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152700 prefixEnd_1152700 := by exact prefixLift 1152700
  have htrace : WordTrace (prefixWord ++ tailWord_1152700) baseStart_1152700 baseEnd_1152700 := by
    simpa [prefixWord, tailWord_1152700, baseEnd_1152700] using wordTrace_append hprefix tailTrace_1152700
  have hstable : (prefixWord ++ tailWord_1152700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152700).length < 2 ^ (prefixWord ++ tailWord_1152700).sum := by decide
  have hdescent : baseEnd_1152700 < baseStart_1152700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152730 : List Nat := [3, 1, 1, 2, 2, 3, 3, 8]
def baseStart_1152730 : Nat := 118140960795 + 1152730 * 2 ^ 59
def prefixEnd_1152730 : Nat := 4983230072969 + 3 ^ 40 * 1152730 * 2
def baseEnd_1152730 : Nat := 21922390920643710084211

theorem tailTrace_1152730 : CollatzResearch.WordTrace tailWord_1152730 prefixEnd_1152730 21922390920643710084211 := by
  unfold tailWord_1152730
  simp only [CollatzResearch.WordTrace]
  refine ⟨10510879278465888863859911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28029011409242370303626429 10510879278465888863859911)
  ·
    refine ⟨15766318917698833295789867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10510879278465888863859911 15766318917698833295789867)
    ·
      refine ⟨23649478376548249943684801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15766318917698833295789867 23649478376548249943684801)
      ·
        refine ⟨17737108782411187457763601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23649478376548249943684801 17737108782411187457763601)
        ·
          refine ⟨13302831586808390593322701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17737108782411187457763601 13302831586808390593322701)
          ·
            refine ⟨4988561845053146472496013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13302831586808390593322701 4988561845053146472496013)
            ·
              refine ⟨1870710691894929927186005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4988561845053146472496013 1870710691894929927186005)
              ·
                refine ⟨21922390920643710084211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1870710691894929927186005 21922390920643710084211)
                ·
                  rfl

theorem cell23_1152730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 8].length) (baseStart_1152730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152730 prefixEnd_1152730 := by exact prefixLift 1152730
  have htrace : WordTrace (prefixWord ++ tailWord_1152730) baseStart_1152730 baseEnd_1152730 := by
    simpa [prefixWord, tailWord_1152730, baseEnd_1152730] using wordTrace_append hprefix tailTrace_1152730
  have hstable : (prefixWord ++ tailWord_1152730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152730).length < 2 ^ (prefixWord ++ tailWord_1152730).sum := by decide
  have hdescent : baseEnd_1152730 < baseStart_1152730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152758 : List Nat := [5, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_1152758 : Nat := 118140960795 + 1152758 * 2 ^ 59
def prefixEnd_1152758 : Nat := 4983230072969 + 3 ^ 40 * 1152758 * 2
def baseEnd_1152758 : Nat := 591918932315706062723569

theorem tailTrace_1152758 : CollatzResearch.WordTrace tailWord_1152758 prefixEnd_1152758 591918932315706062723569 := by
  unfold tailWord_1152758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2627783647360132264841183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28029692238508077491639285 2627783647360132264841183)
  ·
    refine ⟨3941675471040198397261775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2627783647360132264841183 3941675471040198397261775)
    ·
      refine ⟨5912513206560297595892663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3941675471040198397261775 5912513206560297595892663)
      ·
        refine ⟨8868769809840446393838995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5912513206560297595892663 8868769809840446393838995)
        ·
          refine ⟨13303154714760669590758493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8868769809840446393838995 13303154714760669590758493)
          ·
            refine ⟨4988683018035251096534435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13303154714760669590758493 4988683018035251096534435)
            ·
              refine ⟨7483024527052876644801653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4988683018035251096534435 7483024527052876644801653)
              ·
                refine ⟨701533549411207185450155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7483024527052876644801653 701533549411207185450155)
                ·
                  refine ⟨1052300324116810778175233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701533549411207185450155 1052300324116810778175233)
                  ·
                    refine ⟨789225243087608083631425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1052300324116810778175233 789225243087608083631425)
                    ·
                      refine ⟨591918932315706062723569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 789225243087608083631425 591918932315706062723569)
                      ·
                        rfl

theorem cell23_1152758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_1152758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152758 prefixEnd_1152758 := by exact prefixLift 1152758
  have htrace : WordTrace (prefixWord ++ tailWord_1152758) baseStart_1152758 baseEnd_1152758 := by
    simpa [prefixWord, tailWord_1152758, baseEnd_1152758] using wordTrace_append hprefix tailTrace_1152758
  have hstable : (prefixWord ++ tailWord_1152758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152758).length < 2 ^ (prefixWord ++ tailWord_1152758).sum := by decide
  have hdescent : baseEnd_1152758 < baseStart_1152758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152780 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_1152780 : Nat := 118140960795 + 1152780 * 2 ^ 59
def prefixEnd_1152780 : Nat := 4983230072969 + 3 ^ 40 * 1152780 * 2
def baseEnd_1152780 : Nat := 591930228890104976648467

theorem tailTrace_1152780 : CollatzResearch.WordTrace tailWord_1152780 prefixEnd_1152780 591930228890104976648467 := by
  unfold tailWord_1152780
  simp only [CollatzResearch.WordTrace]
  refine ⟨21022670381841206997379897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28030227175788275996506529 21022670381841206997379897)
  ·
    refine ⟨15767002786380905248034923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21022670381841206997379897 15767002786380905248034923)
    ·
      refine ⟨23650504179571357872052385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15767002786380905248034923 23650504179571357872052385)
      ·
        refine ⟨17737878134678518404039289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23650504179571357872052385 17737878134678518404039289)
        ·
          refine ⟨13303408601008888803029467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17737878134678518404039289 13303408601008888803029467)
          ·
            refine ⟨19955112901513333204544201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13303408601008888803029467 19955112901513333204544201)
            ·
              refine ⟨14966334676134999903408151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19955112901513333204544201 14966334676134999903408151)
              ·
                refine ⟨22449502014202499855112227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14966334676134999903408151 22449502014202499855112227)
                ·
                  refine ⟨33674253021303749782668341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22449502014202499855112227 33674253021303749782668341)
                  ·
                    refine ⟨3156961220747226542125157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33674253021303749782668341 3156961220747226542125157)
                    ·
                      refine ⟨591930228890104976648467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3156961220747226542125157 591930228890104976648467)
                      ·
                        rfl

theorem cell23_1152780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_1152780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152780 prefixEnd_1152780 := by exact prefixLift 1152780
  have htrace : WordTrace (prefixWord ++ tailWord_1152780) baseStart_1152780 baseEnd_1152780 := by
    simpa [prefixWord, tailWord_1152780, baseEnd_1152780] using wordTrace_append hprefix tailTrace_1152780
  have hstable : (prefixWord ++ tailWord_1152780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152780).length < 2 ^ (prefixWord ++ tailWord_1152780).sum := by decide
  have hdescent : baseEnd_1152780 < baseStart_1152780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152798 : List Nat := [4, 3, 2, 2, 1, 2, 2, 7]
def baseStart_1152798 : Nat := 118140960795 + 1152798 * 2 ^ 59
def prefixEnd_1152798 : Nat := 4983230072969 + 3 ^ 40 * 1152798 * 2
def baseEnd_1152798 : Nat := 21923684131180959489755

theorem tailTrace_1152798 : CollatzResearch.WordTrace tailWord_1152798 prefixEnd_1152798 21923684131180959489755 := by
  unfold tailWord_1152798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5255749659702150383614381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28030664851744802045943365 5255749659702150383614381)
  ·
    refine ⟨1970906122388306393855393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5255749659702150383614381 1970906122388306393855393)
    ·
      refine ⟨1478179591791229795391545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1970906122388306393855393 1478179591791229795391545)
      ·
        refine ⟨1108634693843422346543659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1478179591791229795391545 1108634693843422346543659)
        ·
          refine ⟨1662952040765133519815489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108634693843422346543659 1662952040765133519815489)
          ·
            refine ⟨1247214030573850139861617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1662952040765133519815489 1247214030573850139861617)
            ·
              refine ⟨935410522930387604896213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247214030573850139861617 935410522930387604896213)
              ·
                refine ⟨21923684131180959489755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 935410522930387604896213 21923684131180959489755)
                ·
                  rfl

theorem cell23_1152798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_1152798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152798 prefixEnd_1152798 := by exact prefixLift 1152798
  have htrace : WordTrace (prefixWord ++ tailWord_1152798) baseStart_1152798 baseEnd_1152798 := by
    simpa [prefixWord, tailWord_1152798, baseEnd_1152798] using wordTrace_append hprefix tailTrace_1152798
  have hstable : (prefixWord ++ tailWord_1152798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152798).length < 2 ^ (prefixWord ++ tailWord_1152798).sum := by decide
  have hdescent : baseEnd_1152798 < baseStart_1152798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152801 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 1, 3, 2]
def baseStart_1152801 : Nat := 118140960795 + 1152801 * 2 ^ 59
def prefixEnd_1152801 : Nat := 4983230072969 + 3 ^ 40 * 1152801 * 2
def baseEnd_1152801 : Nat := 591941011983849394485871

theorem tailTrace_1152801 : CollatzResearch.WordTrace tailWord_1152801 prefixEnd_1152801 591941011983849394485871 := by
  unfold tailWord_1152801
  simp only [CollatzResearch.WordTrace]
  refine ⟨42046106696606334581274257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28030737797737556387516171 42046106696606334581274257)
  ·
    refine ⟨31534580022454750935955693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42046106696606334581274257 31534580022454750935955693)
    ·
      refine ⟨11825467508420531600983385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31534580022454750935955693 11825467508420531600983385)
      ·
        refine ⟨8869100631315398700737539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11825467508420531600983385 8869100631315398700737539)
        ·
          refine ⟨13303650946973098051106309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8869100631315398700737539 13303650946973098051106309)
          ·
            refine ⟨2494434552557455884582433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13303650946973098051106309 2494434552557455884582433)
            ·
              refine ⟨1870825914418091913436825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2494434552557455884582433 1870825914418091913436825)
              ·
                refine ⟨1403119435813568935077619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1870825914418091913436825 1403119435813568935077619)
                ·
                  refine ⟨2104679153720353402616429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1403119435813568935077619 2104679153720353402616429)
                  ·
                    refine ⟨789254682645132525981161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2104679153720353402616429 789254682645132525981161)
                    ·
                      refine ⟨591941011983849394485871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 789254682645132525981161 591941011983849394485871)
                      ·
                        rfl

theorem cell23_1152801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_1152801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152801 prefixEnd_1152801 := by exact prefixLift 1152801
  have htrace : WordTrace (prefixWord ++ tailWord_1152801) baseStart_1152801 baseEnd_1152801 := by
    simpa [prefixWord, tailWord_1152801, baseEnd_1152801] using wordTrace_append hprefix tailTrace_1152801
  have hstable : (prefixWord ++ tailWord_1152801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152801).length < 2 ^ (prefixWord ++ tailWord_1152801).sum := by decide
  have hdescent : baseEnd_1152801 < baseStart_1152801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152817 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_1152817 : Nat := 118140960795 + 1152817 * 2 ^ 59
def prefixEnd_1152817 : Nat := 4983230072969 + 3 ^ 40 * 1152817 * 2
def baseEnd_1152817 : Nat := 591949227674321331885797

theorem tailTrace_1152817 : CollatzResearch.WordTrace tailWord_1152817 prefixEnd_1152817 591949227674321331885797 := by
  unfold tailWord_1152817
  simp only [CollatzResearch.WordTrace]
  refine ⟨42046690264548369313856705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28031126843032246209237803 42046690264548369313856705)
  ·
    refine ⟨31535017698411276985392529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42046690264548369313856705 31535017698411276985392529)
    ·
      refine ⟨23651263273808457739044397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31535017698411276985392529 23651263273808457739044397)
      ·
        refine ⟨8869223727678171652141649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23651263273808457739044397 8869223727678171652141649)
        ·
          refine ⟨6651917795758628739106237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8869223727678171652141649 6651917795758628739106237)
          ·
            refine ⟨2494469173409485777164839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6651917795758628739106237 2494469173409485777164839)
            ·
              refine ⟨3741703760114228665747259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494469173409485777164839 3741703760114228665747259)
              ·
                refine ⟨5612555640171342998620889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741703760114228665747259 5612555640171342998620889)
                ·
                  refine ⟨4209416730128507248965667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5612555640171342998620889 4209416730128507248965667)
                  ·
                    refine ⟨6314125095192760873448501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4209416730128507248965667 6314125095192760873448501)
                    ·
                      refine ⟨591949227674321331885797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6314125095192760873448501 591949227674321331885797)
                      ·
                        rfl

theorem cell23_1152817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_1152817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152817 prefixEnd_1152817 := by exact prefixLift 1152817
  have htrace : WordTrace (prefixWord ++ tailWord_1152817) baseStart_1152817 baseEnd_1152817 := by
    simpa [prefixWord, tailWord_1152817, baseEnd_1152817] using wordTrace_append hprefix tailTrace_1152817
  have hstable : (prefixWord ++ tailWord_1152817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152817).length < 2 ^ (prefixWord ++ tailWord_1152817).sum := by decide
  have hdescent : baseEnd_1152817 < baseStart_1152817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152877 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1152877 : Nat := 118140960795 + 1152877 * 2 ^ 59
def prefixEnd_1152877 : Nat := 4983230072969 + 3 ^ 40 * 1152877 * 2
def baseEnd_1152877 : Nat := 591980036513591097135521

theorem tailTrace_1152877 : CollatzResearch.WordTrace tailWord_1152877 prefixEnd_1152877 591980036513591097135521 := by
  unfold tailWord_1152877
  simp only [CollatzResearch.WordTrace]
  refine ⟨42048878644330999561040885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28032585762887333040693923 42048878644330999561040885)
  ·
    refine ⟨3942082372906031208847583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42048878644330999561040885 3942082372906031208847583)
    ·
      refine ⟨5913123559359046813271375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3942082372906031208847583 5913123559359046813271375)
      ·
        refine ⟨8869685339038570219907063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5913123559359046813271375 8869685339038570219907063)
        ·
          refine ⟨13304528008557855329860595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8869685339038570219907063 13304528008557855329860595)
          ·
            refine ⟨19956792012836782994790893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13304528008557855329860595 19956792012836782994790893)
            ·
              refine ⟨7483797004813793623046585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19956792012836782994790893 7483797004813793623046585)
              ·
                refine ⟨5612847753610345217284939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7483797004813793623046585 5612847753610345217284939)
                ·
                  refine ⟨8419271630415517825927409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5612847753610345217284939 8419271630415517825927409)
                  ·
                    refine ⟨6314453722811638369445557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8419271630415517825927409 6314453722811638369445557)
                    ·
                      refine ⟨591980036513591097135521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6314453722811638369445557 591980036513591097135521)
                      ·
                        rfl

theorem cell23_1152877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1152877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152877 prefixEnd_1152877 := by exact prefixLift 1152877
  have htrace : WordTrace (prefixWord ++ tailWord_1152877) baseStart_1152877 baseEnd_1152877 := by
    simpa [prefixWord, tailWord_1152877, baseEnd_1152877] using wordTrace_append hprefix tailTrace_1152877
  have hstable : (prefixWord ++ tailWord_1152877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152877).length < 2 ^ (prefixWord ++ tailWord_1152877).sum := by decide
  have hdescent : baseEnd_1152877 < baseStart_1152877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152907 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 3]
def baseStart_1152907 : Nat := 118140960795 + 1152907 * 2 ^ 59
def prefixEnd_1152907 : Nat := 4983230072969 + 3 ^ 40 * 1152907 * 2
def baseEnd_1152907 : Nat := 591995440933225979760383

theorem tailTrace_1152907 : CollatzResearch.WordTrace tailWord_1152907 prefixEnd_1152907 591995440933225979760383 := by
  unfold tailWord_1152907
  simp only [CollatzResearch.WordTrace]
  refine ⟨42049972834222314684632975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28033315222814876456421983 42049972834222314684632975)
  ·
    refine ⟨63074959251333472026949463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42049972834222314684632975 63074959251333472026949463)
    ·
      refine ⟨94612438877000208040424195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63074959251333472026949463 94612438877000208040424195)
      ·
        refine ⟨141918658315500312060636293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94612438877000208040424195 141918658315500312060636293)
        ·
          refine ⟨26609748434156308511369305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141918658315500312060636293 26609748434156308511369305)
          ·
            refine ⟨19957311325617231383526979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26609748434156308511369305 19957311325617231383526979)
            ·
              refine ⟨29935966988425847075290469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19957311325617231383526979 29935966988425847075290469)
              ·
                refine ⟨5612993810329846326616963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29935966988425847075290469 5612993810329846326616963)
                ·
                  refine ⟨8419490715494769489925445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5612993810329846326616963 8419490715494769489925445)
                  ·
                    refine ⟨1578654509155269279361021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8419490715494769489925445 1578654509155269279361021)
                    ·
                      refine ⟨591995440933225979760383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1578654509155269279361021 591995440933225979760383)
                      ·
                        rfl

theorem cell23_1152907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 3].length) (baseStart_1152907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152907 prefixEnd_1152907 := by exact prefixLift 1152907
  have htrace : WordTrace (prefixWord ++ tailWord_1152907) baseStart_1152907 baseEnd_1152907 := by
    simpa [prefixWord, tailWord_1152907, baseEnd_1152907] using wordTrace_append hprefix tailTrace_1152907
  have hstable : (prefixWord ++ tailWord_1152907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152907).length < 2 ^ (prefixWord ++ tailWord_1152907).sum := by decide
  have hdescent : baseEnd_1152907 < baseStart_1152907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152918 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1152918 : Nat := 118140960795 + 1152918 * 2 ^ 59
def prefixEnd_1152918 : Nat := 4983230072969 + 3 ^ 40 * 1152918 * 2
def baseEnd_1152918 : Nat := 197333696406808478907611

theorem tailTrace_1152918 : CollatzResearch.WordTrace tailWord_1152918 prefixEnd_1152918 197333696406808478907611 := by
  unfold tailWord_1152918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2628148377323903972705213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28033582691454975708855605 2628148377323903972705213)
  ·
    refine ⟨985555641496463989764455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2628148377323903972705213 985555641496463989764455)
    ·
      refine ⟨1478333462244695984646683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 985555641496463989764455 1478333462244695984646683)
      ·
        refine ⟨2217500193367043976970025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1478333462244695984646683 2217500193367043976970025)
        ·
          refine ⟨1663125145025282982727519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2217500193367043976970025 1663125145025282982727519)
          ·
            refine ⟨2494687717537924474091279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663125145025282982727519 2494687717537924474091279)
            ·
              refine ⟨3742031576306886711136919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494687717537924474091279 3742031576306886711136919)
              ·
                refine ⟨5613047364460330066705379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742031576306886711136919 5613047364460330066705379)
                ·
                  refine ⟨8419571046690495100058069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5613047364460330066705379 8419571046690495100058069)
                  ·
                    refine ⟨197333696406808478907611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8419571046690495100058069 197333696406808478907611)
                    ·
                      rfl

theorem cell23_1152918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1152918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152918 prefixEnd_1152918 := by exact prefixLift 1152918
  have htrace : WordTrace (prefixWord ++ tailWord_1152918) baseStart_1152918 baseEnd_1152918 := by
    simpa [prefixWord, tailWord_1152918, baseEnd_1152918] using wordTrace_append hprefix tailTrace_1152918
  have hstable : (prefixWord ++ tailWord_1152918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152918).length < 2 ^ (prefixWord ++ tailWord_1152918).sum := by decide
  have hdescent : baseEnd_1152918 < baseStart_1152918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152981 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 1, 5, 2]
def baseStart_1152981 : Nat := 118140960795 + 1152981 * 2 ^ 59
def prefixEnd_1152981 : Nat := 4983230072969 + 3 ^ 40 * 1152981 * 2
def baseEnd_1152981 : Nat := 592033438501658690235043

theorem tailTrace_1152981 : CollatzResearch.WordTrace tailWord_1152981 prefixEnd_1152981 592033438501658690235043 := by
  unfold tailWord_1152981
  simp only [CollatzResearch.WordTrace]
  refine ⟨42052671835954225322826797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28035114557302816881884531 42052671835954225322826797)
  ·
    refine ⟨15769751938482834496060049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42052671835954225322826797 15769751938482834496060049)
    ·
      refine ⟨11827313953862125872045037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15769751938482834496060049 11827313953862125872045037)
      ·
        refine ⟨4435242732698297202016889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11827313953862125872045037 4435242732698297202016889)
        ·
          refine ⟨3326432049523722901512667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4435242732698297202016889 3326432049523722901512667)
          ·
            refine ⟨4989648074285584352269001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326432049523722901512667 4989648074285584352269001)
            ·
              refine ⟨3742236055714188264201751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4989648074285584352269001 3742236055714188264201751)
              ·
                refine ⟨5613354083571282396302627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742236055714188264201751 5613354083571282396302627)
                ·
                  refine ⟨8420031125356923594453941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5613354083571282396302627 8420031125356923594453941)
                  ·
                    refine ⟨789377918002211586980057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8420031125356923594453941 789377918002211586980057)
                    ·
                      refine ⟨592033438501658690235043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 789377918002211586980057 592033438501658690235043)
                      ·
                        rfl

theorem cell23_1152981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_1152981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152981 prefixEnd_1152981 := by exact prefixLift 1152981
  have htrace : WordTrace (prefixWord ++ tailWord_1152981) baseStart_1152981 baseEnd_1152981 := by
    simpa [prefixWord, tailWord_1152981, baseEnd_1152981] using wordTrace_append hprefix tailTrace_1152981
  have hstable : (prefixWord ++ tailWord_1152981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152981).length < 2 ^ (prefixWord ++ tailWord_1152981).sum := by decide
  have hdescent : baseEnd_1152981 < baseStart_1152981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1152982 : List Nat := [5, 2, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_1152982 : Nat := 118140960795 + 1152982 * 2 ^ 59
def prefixEnd_1152982 : Nat := 4983230072969 + 3 ^ 40 * 1152982 * 2
def baseEnd_1152982 : Nat := 197344650660771062107513

theorem tailTrace_1152982 : CollatzResearch.WordTrace tailWord_1152982 prefixEnd_1152982 197344650660771062107513 := by
  unfold tailWord_1152982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2628294269309412655850825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28035138872633734995742133 2628294269309412655850825)
  ·
    refine ⟨1971220701982059491888119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2628294269309412655850825 1971220701982059491888119)
    ·
      refine ⟨2956831052973089237832179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1971220701982059491888119 2956831052973089237832179)
      ·
        refine ⟨4435246579459633856748269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2956831052973089237832179 4435246579459633856748269)
        ·
          refine ⟨1663217467297362696280601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4435246579459633856748269 1663217467297362696280601)
          ·
            refine ⟨1247413100473022022210451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663217467297362696280601 1247413100473022022210451)
            ·
              refine ⟨1871119650709533033315677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247413100473022022210451 1871119650709533033315677)
              ·
                refine ⟨701669869016074887493379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1871119650709533033315677 701669869016074887493379)
                ·
                  refine ⟨1052504803524112331240069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701669869016074887493379 1052504803524112331240069)
                  ·
                    refine ⟨197344650660771062107513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1052504803524112331240069 197344650660771062107513)
                    ·
                      rfl

theorem cell23_1152982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_1152982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1152982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1152982 prefixEnd_1152982 := by exact prefixLift 1152982
  have htrace : WordTrace (prefixWord ++ tailWord_1152982) baseStart_1152982 baseEnd_1152982 := by
    simpa [prefixWord, tailWord_1152982, baseEnd_1152982] using wordTrace_append hprefix tailTrace_1152982
  have hstable : (prefixWord ++ tailWord_1152982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1152982).length < 2 ^ (prefixWord ++ tailWord_1152982).sum := by decide
  have hdescent : baseEnd_1152982 < baseStart_1152982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1152982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153007 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_1153007 : Nat := 118140960795 + 1153007 * 2 ^ 59
def prefixEnd_1153007 : Nat := 4983230072969 + 3 ^ 40 * 1153007 * 2
def baseEnd_1153007 : Nat := 592046788998675588509923

theorem tailTrace_1153007 : CollatzResearch.WordTrace tailWord_1153007 prefixEnd_1153007 592046788998675588509923 := by
  unfold tailWord_1153007
  simp only [CollatzResearch.WordTrace]
  refine ⟨42053620133860031763273275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28035746755906687842182183 42053620133860031763273275)
  ·
    refine ⟨63080430200790047644909913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42053620133860031763273275 63080430200790047644909913)
    ·
      refine ⟨47310322650592535733682435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63080430200790047644909913 47310322650592535733682435)
      ·
        refine ⟨70965483975888803600523653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47310322650592535733682435 70965483975888803600523653)
        ·
          refine ⟨13306028245479150675098185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70965483975888803600523653 13306028245479150675098185)
          ·
            refine ⟨9979521184109363006323639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13306028245479150675098185 9979521184109363006323639)
            ·
              refine ⟨14969281776164044509485459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9979521184109363006323639 14969281776164044509485459)
              ·
                refine ⟨22453922664246066764228189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14969281776164044509485459 22453922664246066764228189)
                ·
                  refine ⟨8420220999092275036585571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22453922664246066764228189 8420220999092275036585571)
                  ·
                    refine ⟨12630331498638412554878357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8420220999092275036585571 12630331498638412554878357)
                    ·
                      refine ⟨592046788998675588509923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12630331498638412554878357 592046788998675588509923)
                      ·
                        rfl

theorem cell23_1153007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_1153007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153007 prefixEnd_1153007 := by exact prefixLift 1153007
  have htrace : WordTrace (prefixWord ++ tailWord_1153007) baseStart_1153007 baseEnd_1153007 := by
    simpa [prefixWord, tailWord_1153007, baseEnd_1153007] using wordTrace_append hprefix tailTrace_1153007
  have hstable : (prefixWord ++ tailWord_1153007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153007).length < 2 ^ (prefixWord ++ tailWord_1153007).sum := by decide
  have hdescent : baseEnd_1153007 < baseStart_1153007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153017 : List Nat := [1, 2, 1, 3, 1, 4, 1, 10]
def baseStart_1153017 : Nat := 118140960795 + 1153017 * 2 ^ 59
def prefixEnd_1153017 : Nat := 4983230072969 + 3 ^ 40 * 1153017 * 2
def baseEnd_1153017 : Nat := 21927849029822983310551

theorem tailTrace_1153017 : CollatzResearch.WordTrace tailWord_1153017 prefixEnd_1153017 21927849029822983310551 := by
  unfold tailWord_1153017
  simp only [CollatzResearch.WordTrace]
  refine ⟨42053984863823803471137305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28035989909215868980758203 42053984863823803471137305)
  ·
    refine ⟨31540488647867852603352979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42053984863823803471137305 31540488647867852603352979)
    ·
      refine ⟨47310732971801778905029469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31540488647867852603352979 47310732971801778905029469)
      ·
        refine ⟨17741524864425667089386051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47310732971801778905029469 17741524864425667089386051)
        ·
          refine ⟨26612287296638500634079077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17741524864425667089386051 26612287296638500634079077)
          ·
            refine ⟨4989803868119718868889827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26612287296638500634079077 4989803868119718868889827)
            ·
              refine ⟨7484705802179578303334741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4989803868119718868889827 7484705802179578303334741)
              ·
                refine ⟨21927849029822983310551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7484705802179578303334741 21927849029822983310551)
                ·
                  rfl

theorem cell23_1153017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 10].length) (baseStart_1153017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153017 prefixEnd_1153017 := by exact prefixLift 1153017
  have htrace : WordTrace (prefixWord ++ tailWord_1153017) baseStart_1153017 baseEnd_1153017 := by
    simpa [prefixWord, tailWord_1153017, baseEnd_1153017] using wordTrace_append hprefix tailTrace_1153017
  have hstable : (prefixWord ++ tailWord_1153017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153017).length < 2 ^ (prefixWord ++ tailWord_1153017).sum := by decide
  have hdescent : baseEnd_1153017 < baseStart_1153017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153028 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1153028 : Nat := 118140960795 + 1153028 * 2 ^ 59
def prefixEnd_1153028 : Nat := 4983230072969 + 3 ^ 40 * 1153028 * 2
def baseEnd_1153028 : Nat := 592057572092420006347327

theorem tailTrace_1153028 : CollatzResearch.WordTrace tailWord_1153028 prefixEnd_1153028 592057572092420006347327 := by
  unfold tailWord_1153028
  simp only [CollatzResearch.WordTrace]
  refine ⟨21027193033391976174893869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28036257377855968233191825 21027193033391976174893869)
  ·
    refine ⟨7885197387521991065585201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21027193033391976174893869 7885197387521991065585201)
    ·
      refine ⟨5913898040641493299188901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7885197387521991065585201 5913898040641493299188901)
      ·
        refine ⟨1108855882620279993597919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5913898040641493299188901 1108855882620279993597919)
        ·
          refine ⟨1663283823930419990396879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108855882620279993597919 1663283823930419990396879)
          ·
            refine ⟨2494925735895629985595319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663283823930419990396879 2494925735895629985595319)
            ·
              refine ⟨3742388603843444978392979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494925735895629985595319 3742388603843444978392979)
              ·
                refine ⟨5613582905765167467589469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742388603843444978392979 5613582905765167467589469)
                ·
                  refine ⟨2105093589661937800346051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5613582905765167467589469 2105093589661937800346051)
                  ·
                    refine ⟨3157640384492906700519077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2105093589661937800346051 3157640384492906700519077)
                    ·
                      refine ⟨592057572092420006347327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3157640384492906700519077 592057572092420006347327)
                      ·
                        rfl

theorem cell23_1153028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1153028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153028 prefixEnd_1153028 := by exact prefixLift 1153028
  have htrace : WordTrace (prefixWord ++ tailWord_1153028) baseStart_1153028 baseEnd_1153028 := by
    simpa [prefixWord, tailWord_1153028, baseEnd_1153028] using wordTrace_append hprefix tailTrace_1153028
  have hstable : (prefixWord ++ tailWord_1153028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153028).length < 2 ^ (prefixWord ++ tailWord_1153028).sum := by decide
  have hdescent : baseEnd_1153028 < baseStart_1153028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153031 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1153031 : Nat := 118140960795 + 1153031 * 2 ^ 59
def prefixEnd_1153031 : Nat := 4983230072969 + 3 ^ 40 * 1153031 * 2
def baseEnd_1153031 : Nat := 592059112534383494609813

theorem tailTrace_1153031 : CollatzResearch.WordTrace tailWord_1153031 prefixEnd_1153031 592059112534383494609813 := by
  unfold tailWord_1153031
  simp only [CollatzResearch.WordTrace]
  refine ⟨42054495485773083862146947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28036330323848722574764631 42054495485773083862146947)
  ·
    refine ⟨63081743228659625793220421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42054495485773083862146947 63081743228659625793220421)
    ·
      refine ⟨11827826855373679836228829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63081743228659625793220421 11827826855373679836228829)
      ·
        refine ⟨4435435070765129938585811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11827826855373679836228829 4435435070765129938585811)
        ·
          refine ⟨6653152606147694907878717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4435435070765129938585811 6653152606147694907878717)
          ·
            refine ⟨2494932227305385590454519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6653152606147694907878717 2494932227305385590454519)
            ·
              refine ⟨3742398340958078385681779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494932227305385590454519 3742398340958078385681779)
              ·
                refine ⟨5613597511437117578522669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742398340958078385681779 5613597511437117578522669)
                ·
                  refine ⟨2105099066788919091946001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5613597511437117578522669 2105099066788919091946001)
                  ·
                    refine ⟨1578824300091689318959501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105099066788919091946001 1578824300091689318959501)
                    ·
                      refine ⟨592059112534383494609813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1578824300091689318959501 592059112534383494609813)
                      ·
                        rfl

theorem cell23_1153031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1153031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153031 prefixEnd_1153031 := by exact prefixLift 1153031
  have htrace : WordTrace (prefixWord ++ tailWord_1153031) baseStart_1153031 baseEnd_1153031 := by
    simpa [prefixWord, tailWord_1153031, baseEnd_1153031] using wordTrace_append hprefix tailTrace_1153031
  have hstable : (prefixWord ++ tailWord_1153031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153031).length < 2 ^ (prefixWord ++ tailWord_1153031).sum := by decide
  have hdescent : baseEnd_1153031 < baseStart_1153031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153048 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 1, 2, 3]
def baseStart_1153048 : Nat := 118140960795 + 1153048 * 2 ^ 59
def prefixEnd_1153048 : Nat := 4983230072969 + 3 ^ 40 * 1153048 * 2
def baseEnd_1153048 : Nat := 592067841705509928097235

theorem tailTrace_1153048 : CollatzResearch.WordTrace tailWord_1153048 prefixEnd_1153048 592067841705509928097235 := by
  unfold tailWord_1153048
  simp only [CollatzResearch.WordTrace]
  refine ⟨21027557763355747882757899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28036743684474330510343865 21027557763355747882757899)
  ·
    refine ⟨31541336645033621824136849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21027557763355747882757899 31541336645033621824136849)
    ·
      refine ⟨23656002483775216368102637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31541336645033621824136849 23656002483775216368102637)
      ·
        refine ⟨8871000931415706138038489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23656002483775216368102637 8871000931415706138038489)
        ·
          refine ⟨6653250698561779603528867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8871000931415706138038489 6653250698561779603528867)
          ·
            refine ⟨9979876047842669405293301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6653250698561779603528867 9979876047842669405293301)
            ·
              refine ⟨935613379485250256746247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9979876047842669405293301 935613379485250256746247)
              ·
                refine ⟨1403420069227875385119371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935613379485250256746247 1403420069227875385119371)
                ·
                  refine ⟨2105130103841813077679057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1403420069227875385119371 2105130103841813077679057)
                  ·
                    refine ⟨1578847577881359808259293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105130103841813077679057 1578847577881359808259293)
                    ·
                      refine ⟨592067841705509928097235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1578847577881359808259293 592067841705509928097235)
                      ·
                        rfl

theorem cell23_1153048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_1153048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153048 prefixEnd_1153048 := by exact prefixLift 1153048
  have htrace : WordTrace (prefixWord ++ tailWord_1153048) baseStart_1153048 baseEnd_1153048 := by
    simpa [prefixWord, tailWord_1153048, baseEnd_1153048] using wordTrace_append hprefix tailTrace_1153048
  have hstable : (prefixWord ++ tailWord_1153048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153048).length < 2 ^ (prefixWord ++ tailWord_1153048).sum := by decide
  have hdescent : baseEnd_1153048 < baseStart_1153048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153078 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1153078 : Nat := 118140960795 + 1153078 * 2 ^ 59
def prefixEnd_1153078 : Nat := 4983230072969 + 3 ^ 40 * 1153078 * 2
def baseEnd_1153078 : Nat := 592083246125144810722097

theorem tailTrace_1153078 : CollatzResearch.WordTrace tailWord_1153078 prefixEnd_1153078 592083246125144810722097 := by
  unfold tailWord_1153078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2628513107287675680569243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28037473144401873926071925 2628513107287675680569243)
  ·
    refine ⟨3942769660931513520853865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2628513107287675680569243 3942769660931513520853865)
    ·
      refine ⟨2957077245698635140640399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3942769660931513520853865 2957077245698635140640399)
      ·
        refine ⟨4435615868547952710960599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957077245698635140640399 4435615868547952710960599)
        ·
          refine ⟨6653423802821929066440899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4435615868547952710960599 6653423802821929066440899)
          ·
            refine ⟨9980135704232893599661349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6653423802821929066440899 9980135704232893599661349)
            ·
              refine ⟨1871275444543667549936503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9980135704232893599661349 1871275444543667549936503)
              ·
                refine ⟨2806913166815501324904755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871275444543667549936503 2806913166815501324904755)
                ·
                  refine ⟨4210369750223251987357133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2806913166815501324904755 4210369750223251987357133)
                  ·
                    refine ⟨1578888656333719495258925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4210369750223251987357133 1578888656333719495258925)
                    ·
                      refine ⟨592083246125144810722097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1578888656333719495258925 592083246125144810722097)
                      ·
                        rfl

theorem cell23_1153078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1153078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153078 prefixEnd_1153078 := by exact prefixLift 1153078
  have htrace : WordTrace (prefixWord ++ tailWord_1153078) baseStart_1153078 baseEnd_1153078 := by
    simpa [prefixWord, tailWord_1153078, baseEnd_1153078] using wordTrace_append hprefix tailTrace_1153078
  have hstable : (prefixWord ++ tailWord_1153078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153078).length < 2 ^ (prefixWord ++ tailWord_1153078).sum := by decide
  have hdescent : baseEnd_1153078 < baseStart_1153078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153084 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_1153084 : Nat := 118140960795 + 1153084 * 2 ^ 59
def prefixEnd_1153084 : Nat := 4983230072969 + 3 ^ 40 * 1153084 * 2
def baseEnd_1153084 : Nat := 592086327009071787247069

theorem tailTrace_1153084 : CollatzResearch.WordTrace tailWord_1153084 prefixEnd_1153084 592086327009071787247069 := by
  unfold tailWord_1153084
  simp only [CollatzResearch.WordTrace]
  refine ⟨21028214277290536956913153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28037619036387382609217537 21028214277290536956913153)
  ·
    refine ⟨15771160707967902717684865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21028214277290536956913153 15771160707967902717684865)
    ·
      refine ⟨11828370530975927038263649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15771160707967902717684865 11828370530975927038263649)
      ·
        refine ⟨8871277898231945278697737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11828370530975927038263649 8871277898231945278697737)
        ·
          refine ⟨6653458423673958959023303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8871277898231945278697737 6653458423673958959023303)
          ·
            refine ⟨9980187635510938438534955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6653458423673958959023303 9980187635510938438534955)
            ·
              refine ⟨14970281453266407657802433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9980187635510938438534955 14970281453266407657802433)
              ·
                refine ⟨11227711089949805743351825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14970281453266407657802433 11227711089949805743351825)
                ·
                  refine ⟨8420783317462354307513869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11227711089949805743351825 8420783317462354307513869)
                  ·
                    refine ⟨3157793744048382865317701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8420783317462354307513869 3157793744048382865317701)
                    ·
                      refine ⟨592086327009071787247069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3157793744048382865317701 592086327009071787247069)
                      ·
                        rfl

theorem cell23_1153084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_1153084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153084 prefixEnd_1153084 := by exact prefixLift 1153084
  have htrace : WordTrace (prefixWord ++ tailWord_1153084) baseStart_1153084 baseEnd_1153084 := by
    simpa [prefixWord, tailWord_1153084, baseEnd_1153084] using wordTrace_append hprefix tailTrace_1153084
  have hstable : (prefixWord ++ tailWord_1153084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153084).length < 2 ^ (prefixWord ++ tailWord_1153084).sum := by decide
  have hdescent : baseEnd_1153084 < baseStart_1153084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153114 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_1153114 : Nat := 118140960795 + 1153114 * 2 ^ 59
def prefixEnd_1153114 : Nat := 4983230072969 + 3 ^ 40 * 1153114 * 2
def baseEnd_1153114 : Nat := 592101731428706669871931

theorem tailTrace_1153114 : CollatzResearch.WordTrace tailWord_1153114 prefixEnd_1153114 592101731428706669871931 := by
  unfold tailWord_1153114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10514380686118097259354599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28038348496314926024945597 10514380686118097259354599)
  ·
    refine ⟨15771571029177145889031899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10514380686118097259354599 15771571029177145889031899)
    ·
      refine ⟨23657356543765718833547849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15771571029177145889031899 23657356543765718833547849)
      ·
        refine ⟨17743017407824289125160887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23657356543765718833547849 17743017407824289125160887)
        ·
          refine ⟨26614526111736433687741331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17743017407824289125160887 26614526111736433687741331)
          ·
            refine ⟨39921789167604650531611997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26614526111736433687741331 39921789167604650531611997)
            ·
              refine ⟨14970670937851743949354499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39921789167604650531611997 14970670937851743949354499)
              ·
                refine ⟨22456006406777615924031749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14970670937851743949354499 22456006406777615924031749)
                ·
                  refine ⟨4210501201270802985755953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22456006406777615924031749 4210501201270802985755953)
                  ·
                    refine ⟨3157875900953102239316965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4210501201270802985755953 3157875900953102239316965)
                    ·
                      refine ⟨592101731428706669871931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3157875900953102239316965 592101731428706669871931)
                      ·
                        rfl

theorem cell23_1153114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_1153114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153114 prefixEnd_1153114 := by exact prefixLift 1153114
  have htrace : WordTrace (prefixWord ++ tailWord_1153114) baseStart_1153114 baseEnd_1153114 := by
    simpa [prefixWord, tailWord_1153114, baseEnd_1153114] using wordTrace_append hprefix tailTrace_1153114
  have hstable : (prefixWord ++ tailWord_1153114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153114).length < 2 ^ (prefixWord ++ tailWord_1153114).sum := by decide
  have hdescent : baseEnd_1153114 < baseStart_1153114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153124 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 7]
def baseStart_1153124 : Nat := 118140960795 + 1153124 * 2 ^ 59
def prefixEnd_1153124 : Nat := 4983230072969 + 3 ^ 40 * 1153124 * 2
def baseEnd_1153124 : Nat := 65789651803916847860765

theorem tailTrace_1153124 : CollatzResearch.WordTrace tailWord_1153124 prefixEnd_1153124 65789651803916847860765 := by
  unfold tailWord_1153124
  simp only [CollatzResearch.WordTrace]
  refine ⟨21028943737218080372641213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28038591649624107163521617 21028943737218080372641213)
  ·
    refine ⟨7885853901456780139740455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21028943737218080372641213 7885853901456780139740455)
    ·
      refine ⟨11828780852185170209610683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7885853901456780139740455 11828780852185170209610683)
      ·
        refine ⟨17743171278277755314416025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11828780852185170209610683 17743171278277755314416025)
        ·
          refine ⟨13307378458708316485812019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17743171278277755314416025 13307378458708316485812019)
          ·
            refine ⟨19961067688062474728718029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13307378458708316485812019 19961067688062474728718029)
            ·
              refine ⟨7485400383023428023269261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19961067688062474728718029 7485400383023428023269261)
              ·
                refine ⟨2807025143633785508725973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7485400383023428023269261 2807025143633785508725973)
                ·
                  refine ⟨65789651803916847860765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2807025143633785508725973 65789651803916847860765)
                  ·
                    rfl

theorem cell23_1153124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_1153124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153124 prefixEnd_1153124 := by exact prefixLift 1153124
  have htrace : WordTrace (prefixWord ++ tailWord_1153124) baseStart_1153124 baseEnd_1153124 := by
    simpa [prefixWord, tailWord_1153124, baseEnd_1153124] using wordTrace_append hprefix tailTrace_1153124
  have hstable : (prefixWord ++ tailWord_1153124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153124).length < 2 ^ (prefixWord ++ tailWord_1153124).sum := by decide
  have hdescent : baseEnd_1153124 < baseStart_1153124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153175 : List Nat := [1, 1, 3, 3, 4, 1, 3, 2, 5]
def baseStart_1153175 : Nat := 118140960795 + 1153175 * 2 ^ 59
def prefixEnd_1153175 : Nat := 4983230072969 + 3 ^ 40 * 1153175 * 2
def baseEnd_1153175 : Nat := 65792561527625659023239

theorem tailTrace_1153175 : CollatzResearch.WordTrace tailWord_1153175 prefixEnd_1153175 65792561527625659023239 := by
  unfold tailWord_1153175
  simp only [CollatzResearch.WordTrace]
  refine ⟨42059747597251396455388979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28039831731500930970259319 42059747597251396455388979)
  ·
    refine ⟨63089621395877094683083469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42059747597251396455388979 63089621395877094683083469)
    ·
      refine ⟨23658608023453910506156301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63089621395877094683083469 23658608023453910506156301)
      ·
        refine ⟨8871978008795216439808613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23658608023453910506156301 8871978008795216439808613)
        ·
          refine ⟨1663495876649103082464115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8871978008795216439808613 1663495876649103082464115)
          ·
            refine ⟨2495243814973654623696173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663495876649103082464115 2495243814973654623696173)
            ·
              refine ⟨935716430615120483886065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2495243814973654623696173 935716430615120483886065)
              ·
                refine ⟨701787322961340362914549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935716430615120483886065 701787322961340362914549)
                ·
                  refine ⟨65792561527625659023239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 701787322961340362914549 65792561527625659023239)
                  ·
                    rfl

theorem cell23_1153175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 5].length) (baseStart_1153175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153175 prefixEnd_1153175 := by exact prefixLift 1153175
  have htrace : WordTrace (prefixWord ++ tailWord_1153175) baseStart_1153175 baseEnd_1153175 := by
    simpa [prefixWord, tailWord_1153175, baseEnd_1153175] using wordTrace_append hprefix tailTrace_1153175
  have hstable : (prefixWord ++ tailWord_1153175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153175).length < 2 ^ (prefixWord ++ tailWord_1153175).sum := by decide
  have hdescent : baseEnd_1153175 < baseStart_1153175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153181 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1153181 : Nat := 118140960795 + 1153181 * 2 ^ 59
def prefixEnd_1153181 : Nat := 4983230072969 + 3 ^ 40 * 1153181 * 2
def baseEnd_1153181 : Nat := 592136134632557907734123

theorem tailTrace_1153181 : CollatzResearch.WordTrace tailWord_1153181 prefixEnd_1153181 592136134632557907734123 := by
  unfold tailWord_1153181
  simp only [CollatzResearch.WordTrace]
  refine ⟨42059966435229659480107397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28039977623486439653404931 42059966435229659480107397)
  ·
    refine ⟨7886243706605561152520137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42059966435229659480107397 7886243706605561152520137)
    ·
      refine ⟨5914682779954170864390103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7886243706605561152520137 5914682779954170864390103)
      ·
        refine ⟨8872024169931256296585155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5914682779954170864390103 8872024169931256296585155)
        ·
          refine ⟨13308036254896884444877733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8872024169931256296585155 13308036254896884444877733)
          ·
            refine ⟨2495256797793165833414575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13308036254896884444877733 2495256797793165833414575)
            ·
              refine ⟨3742885196689748750121863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2495256797793165833414575 3742885196689748750121863)
              ·
                refine ⟨5614327795034623125182795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742885196689748750121863 5614327795034623125182795)
                ·
                  refine ⟨8421491692551934687774193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5614327795034623125182795 8421491692551934687774193)
                  ·
                    refine ⟨6316118769413951015830645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8421491692551934687774193 6316118769413951015830645)
                    ·
                      refine ⟨592136134632557907734123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6316118769413951015830645 592136134632557907734123)
                      ·
                        rfl

theorem cell23_1153181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1153181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153181 prefixEnd_1153181 := by exact prefixLift 1153181
  have htrace : WordTrace (prefixWord ++ tailWord_1153181) baseStart_1153181 baseEnd_1153181 := by
    simpa [prefixWord, tailWord_1153181, baseEnd_1153181] using wordTrace_append hprefix tailTrace_1153181
  have hstable : (prefixWord ++ tailWord_1153181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153181).length < 2 ^ (prefixWord ++ tailWord_1153181).sum := by decide
  have hdescent : baseEnd_1153181 < baseStart_1153181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153205 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 2, 5]
def baseStart_1153205 : Nat := 118140960795 + 1153205 * 2 ^ 59
def prefixEnd_1153205 : Nat := 4983230072969 + 3 ^ 40 * 1153205 * 2
def baseEnd_1153205 : Nat := 197382819389421937944671

theorem tailTrace_1153205 : CollatzResearch.WordTrace tailWord_1153205 prefixEnd_1153205 197382819389421937944671 := by
  unfold tailWord_1153205
  simp only [CollatzResearch.WordTrace]
  refine ⟨42060841787142711578981069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28040561191428474385987379 42060841787142711578981069)
  ·
    refine ⟨15772815670178516842117901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42060841787142711578981069 15772815670178516842117901)
    ·
      refine ⟨5914805876316943815794213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15772815670178516842117901 5914805876316943815794213)
      ·
        refine ⟨1109026101809426965461415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5914805876316943815794213 1109026101809426965461415)
        ·
          refine ⟨1663539152714140448192123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109026101809426965461415 1663539152714140448192123)
          ·
            refine ⟨2495308729071210672288185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663539152714140448192123 2495308729071210672288185)
            ·
              refine ⟨1871481546803408004216139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2495308729071210672288185 1871481546803408004216139)
              ·
                refine ⟨2807222320205112006324209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871481546803408004216139 2807222320205112006324209)
                ·
                  refine ⟨2105416740153834004743157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2807222320205112006324209 2105416740153834004743157)
                  ·
                    refine ⟨197382819389421937944671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2105416740153834004743157 197382819389421937944671)
                    ·
                      rfl

theorem cell23_1153205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_1153205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153205 prefixEnd_1153205 := by exact prefixLift 1153205
  have htrace : WordTrace (prefixWord ++ tailWord_1153205) baseStart_1153205 baseEnd_1153205 := by
    simpa [prefixWord, tailWord_1153205, baseEnd_1153205] using wordTrace_append hprefix tailTrace_1153205
  have hstable : (prefixWord ++ tailWord_1153205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153205).length < 2 ^ (prefixWord ++ tailWord_1153205).sum := by decide
  have hdescent : baseEnd_1153205 < baseStart_1153205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153231 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 6]
def baseStart_1153231 : Nat := 118140960795 + 1153231 * 2 ^ 59
def prefixEnd_1153231 : Nat := 4983230072969 + 3 ^ 40 * 1153231 * 2
def baseEnd_1153231 : Nat := 65795756518364745789877

theorem tailTrace_1153231 : CollatzResearch.WordTrace tailWord_1153231 prefixEnd_1153231 65795756518364745789877 := by
  unfold tailWord_1153231
  simp only [CollatzResearch.WordTrace]
  refine ⟨42061790085048518019427547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28041193390032345346285031 42061790085048518019427547)
  ·
    refine ⟨63092685127572777029141321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42061790085048518019427547 63092685127572777029141321)
    ·
      refine ⟨47319513845679582771855991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63092685127572777029141321 47319513845679582771855991)
      ·
        refine ⟨70979270768519374157783987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47319513845679582771855991 70979270768519374157783987)
        ·
          refine ⟨106468906152779061236675981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70979270768519374157783987 106468906152779061236675981)
          ·
            refine ⟨39925839807292147963753493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106468906152779061236675981 39925839807292147963753493)
            ·
              refine ⟨1871523740966819435800945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39925839807292147963753493 1871523740966819435800945)
              ·
                refine ⟨1403642805725114576850709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871523740966819435800945 1403642805725114576850709)
                ·
                  refine ⟨65795756518364745789877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1403642805725114576850709 65795756518364745789877)
                  ·
                    rfl

theorem cell23_1153231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 6].length) (baseStart_1153231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153231 prefixEnd_1153231 := by exact prefixLift 1153231
  have htrace : WordTrace (prefixWord ++ tailWord_1153231) baseStart_1153231 baseEnd_1153231 := by
    simpa [prefixWord, tailWord_1153231, baseEnd_1153231] using wordTrace_append hprefix tailTrace_1153231
  have hstable : (prefixWord ++ tailWord_1153231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153231).length < 2 ^ (prefixWord ++ tailWord_1153231).sum := by decide
  have hdescent : baseEnd_1153231 < baseStart_1153231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153301 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_1153301 : Nat := 118140960795 + 1153301 * 2 ^ 59
def prefixEnd_1153301 : Nat := 4983230072969 + 3 ^ 40 * 1153301 * 2
def baseEnd_1153301 : Nat := 592197752311097438233571

theorem tailTrace_1153301 : CollatzResearch.WordTrace tailWord_1153301 prefixEnd_1153301 592197752311097438233571 := by
  unfold tailWord_1153301
  simp only [CollatzResearch.WordTrace]
  refine ⟨42064343194794919974475757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28042895463196613316317171 42064343194794919974475757)
  ·
    refine ⟨15774128698048094990428409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42064343194794919974475757 15774128698048094990428409)
    ·
      refine ⟨11830596523536071242821307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15774128698048094990428409 11830596523536071242821307)
      ·
        refine ⟨17745894785304106864231961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11830596523536071242821307 17745894785304106864231961)
        ·
          refine ⟨13309421088978080148173971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17745894785304106864231961 13309421088978080148173971)
          ·
            refine ⟨19964131633467120222260957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13309421088978080148173971 19964131633467120222260957)
            ·
              refine ⟨7486549362550170083347859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19964131633467120222260957 7486549362550170083347859)
              ·
                refine ⟨11229824043825255125021789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7486549362550170083347859 11229824043825255125021789)
                ·
                  refine ⟨4211184016434470671883171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11229824043825255125021789 4211184016434470671883171)
                  ·
                    refine ⟨6316776024651706007824757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4211184016434470671883171 6316776024651706007824757)
                    ·
                      refine ⟨592197752311097438233571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6316776024651706007824757 592197752311097438233571)
                      ·
                        rfl

theorem cell23_1153301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_1153301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153301 prefixEnd_1153301 := by exact prefixLift 1153301
  have htrace : WordTrace (prefixWord ++ tailWord_1153301) baseStart_1153301 baseEnd_1153301 := by
    simpa [prefixWord, tailWord_1153301, baseEnd_1153301] using wordTrace_append hprefix tailTrace_1153301
  have hstable : (prefixWord ++ tailWord_1153301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153301).length < 2 ^ (prefixWord ++ tailWord_1153301).sum := by decide
  have hdescent : baseEnd_1153301 < baseStart_1153301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153315 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 3, 2, 2]
def baseStart_1153315 : Nat := 118140960795 + 1153315 * 2 ^ 59
def prefixEnd_1153315 : Nat := 4983230072969 + 3 ^ 40 * 1153315 * 2
def baseEnd_1153315 : Nat := 592204941040260383458507

theorem tailTrace_1153315 : CollatzResearch.WordTrace tailWord_1153315 prefixEnd_1153315 592204941040260383458507 := by
  unfold tailWord_1153315
  simp only [CollatzResearch.WordTrace]
  refine ⟨42064853816744200365485399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28043235877829466910323599 42064853816744200365485399)
  ·
    refine ⟨63097280725116300548228099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42064853816744200365485399 63097280725116300548228099)
    ·
      refine ⟨94645921087674450822342149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63097280725116300548228099 94645921087674450822342149)
      ·
        refine ⟨17746110203938959529189153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94645921087674450822342149 17746110203938959529189153)
        ·
          refine ⟨13309582652954219646891865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17746110203938959529189153 13309582652954219646891865)
          ·
            refine ⟨9982186989715664735168899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13309582652954219646891865 9982186989715664735168899)
            ·
              refine ⟨14973280484573497102753349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9982186989715664735168899 14973280484573497102753349)
              ·
                refine ⟨2807490090857530706766253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14973280484573497102753349 2807490090857530706766253)
                ·
                  refine ⟨1052808784071574015037345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2807490090857530706766253 1052808784071574015037345)
                  ·
                    refine ⟨789606588053680511278009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1052808784071574015037345 789606588053680511278009)
                    ·
                      refine ⟨592204941040260383458507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 789606588053680511278009 592204941040260383458507)
                      ·
                        rfl

theorem cell23_1153315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_1153315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153315 prefixEnd_1153315 := by exact prefixLift 1153315
  have htrace : WordTrace (prefixWord ++ tailWord_1153315) baseStart_1153315 baseEnd_1153315 := by
    simpa [prefixWord, tailWord_1153315, baseEnd_1153315] using wordTrace_append hprefix tailTrace_1153315
  have hstable : (prefixWord ++ tailWord_1153315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153315).length < 2 ^ (prefixWord ++ tailWord_1153315).sum := by decide
  have hdescent : baseEnd_1153315 < baseStart_1153315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153351 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 2, 7]
def baseStart_1153351 : Nat := 118140960795 + 1153351 * 2 ^ 59
def prefixEnd_1153351 : Nat := 4983230072969 + 3 ^ 40 * 1153351 * 2
def baseEnd_1153351 : Nat := 197407808781274080869447

theorem tailTrace_1153351 : CollatzResearch.WordTrace tailWord_1153351 prefixEnd_1153351 197407808781274080869447 := by
  unfold tailWord_1153351
  simp only [CollatzResearch.WordTrace]
  refine ⟨42066166844613778513795907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28044111229742519009197271 42066166844613778513795907)
  ·
    refine ⟨63099250266920667770693861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42066166844613778513795907 63099250266920667770693861)
    ·
      refine ⟨11831109425047625207005099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63099250266920667770693861 11831109425047625207005099)
      ·
        refine ⟨17746664137571437810507649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11831109425047625207005099 17746664137571437810507649)
        ·
          refine ⟨13309998103178578357880737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17746664137571437810507649 13309998103178578357880737)
          ·
            refine ⟨9982498577383933768410553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13309998103178578357880737 9982498577383933768410553)
            ·
              refine ⟨7486873933037950326307915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9982498577383933768410553 7486873933037950326307915)
              ·
                refine ⟨11230310899556925489461873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7486873933037950326307915 11230310899556925489461873)
                ·
                  refine ⟨8422733174667694117096405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11230310899556925489461873 8422733174667694117096405)
                  ·
                    refine ⟨197407808781274080869447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8422733174667694117096405 197407808781274080869447)
                    ·
                      rfl

theorem cell23_1153351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_1153351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153351 prefixEnd_1153351 := by exact prefixLift 1153351
  have htrace : WordTrace (prefixWord ++ tailWord_1153351) baseStart_1153351 baseEnd_1153351 := by
    simpa [prefixWord, tailWord_1153351, baseEnd_1153351] using wordTrace_append hprefix tailTrace_1153351
  have hstable : (prefixWord ++ tailWord_1153351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153351).length < 2 ^ (prefixWord ++ tailWord_1153351).sum := by decide
  have hdescent : baseEnd_1153351 < baseStart_1153351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153391 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_1153391 : Nat := 118140960795 + 1153391 * 2 ^ 59
def prefixEnd_1153391 : Nat := 4983230072969 + 3 ^ 40 * 1153391 * 2
def baseEnd_1153391 : Nat := 592243965570002086108157

theorem tailTrace_1153391 : CollatzResearch.WordTrace tailWord_1153391 prefixEnd_1153391 592243965570002086108157 := by
  unfold tailWord_1153391
  simp only [CollatzResearch.WordTrace]
  refine ⟨42067625764468865345252027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28045083842979243563501351 42067625764468865345252027)
  ·
    refine ⟨63101438646703298017878041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42067625764468865345252027 63101438646703298017878041)
    ·
      refine ⟨47326078985027473513408531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63101438646703298017878041 47326078985027473513408531)
      ·
        refine ⟨70989118477541210270112797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47326078985027473513408531 70989118477541210270112797)
        ·
          refine ⟨26620919429077953851292299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70989118477541210270112797 26620919429077953851292299)
          ·
            refine ⟨39931379143616930776938449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26620919429077953851292299 39931379143616930776938449)
            ·
              refine ⟨29948534357712698082703837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39931379143616930776938449 29948534357712698082703837)
              ·
                refine ⟨11230700384142261781013939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29948534357712698082703837 11230700384142261781013939)
                ·
                  refine ⟨16846050576213392671520909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11230700384142261781013939 16846050576213392671520909)
                  ·
                    refine ⟨6317268966080022251820341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16846050576213392671520909 6317268966080022251820341)
                    ·
                      refine ⟨592243965570002086108157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6317268966080022251820341 592243965570002086108157)
                      ·
                        rfl

theorem cell23_1153391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_1153391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153391 prefixEnd_1153391 := by exact prefixLift 1153391
  have htrace : WordTrace (prefixWord ++ tailWord_1153391) baseStart_1153391 baseEnd_1153391 := by
    simpa [prefixWord, tailWord_1153391, baseEnd_1153391] using wordTrace_append hprefix tailTrace_1153391
  have hstable : (prefixWord ++ tailWord_1153391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153391).length < 2 ^ (prefixWord ++ tailWord_1153391).sum := by decide
  have hdescent : baseEnd_1153391 < baseStart_1153391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153401 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_1153401 : Nat := 118140960795 + 1153401 * 2 ^ 59
def prefixEnd_1153401 : Nat := 4983230072969 + 3 ^ 40 * 1153401 * 2
def baseEnd_1153401 : Nat := 592249100376547046983111

theorem tailTrace_1153401 : CollatzResearch.WordTrace tailWord_1153401 prefixEnd_1153401 592249100376547046983111 := by
  unfold tailWord_1153401
  simp only [CollatzResearch.WordTrace]
  refine ⟨42067990494432637053116057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28045326996288424702077371 42067990494432637053116057)
  ·
    refine ⟨31550992870824477789837043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42067990494432637053116057 31550992870824477789837043)
    ·
      refine ⟨47326489306236716684755565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31550992870824477789837043 47326489306236716684755565)
      ·
        refine ⟨17747433489838768756783337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47326489306236716684755565 17747433489838768756783337)
        ·
          refine ⟨13310575117379076567587503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17747433489838768756783337 13310575117379076567587503)
          ·
            refine ⟨19965862676068614851381255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13310575117379076567587503 19965862676068614851381255)
            ·
              refine ⟨29948794014102922277071883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19965862676068614851381255 29948794014102922277071883)
              ·
                refine ⟨44923191021154383415607825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29948794014102922277071883 44923191021154383415607825)
                ·
                  refine ⟨33692393265865787561705869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44923191021154383415607825 33692393265865787561705869)
                  ·
                    refine ⟨12634647474699670335639701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33692393265865787561705869 12634647474699670335639701)
                    ·
                      refine ⟨592249100376547046983111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12634647474699670335639701 592249100376547046983111)
                      ·
                        rfl

theorem cell23_1153401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1153401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153401 prefixEnd_1153401 := by exact prefixLift 1153401
  have htrace : WordTrace (prefixWord ++ tailWord_1153401) baseStart_1153401 baseEnd_1153401 := by
    simpa [prefixWord, tailWord_1153401, baseEnd_1153401] using wordTrace_append hprefix tailTrace_1153401
  have hstable : (prefixWord ++ tailWord_1153401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153401).length < 2 ^ (prefixWord ++ tailWord_1153401).sum := by decide
  have hdescent : baseEnd_1153401 < baseStart_1153401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153422 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1153422 : Nat := 118140960795 + 1153422 * 2 ^ 59
def prefixEnd_1153422 : Nat := 4983230072969 + 3 ^ 40 * 1153422 * 2
def baseEnd_1153422 : Nat := 592259883470291464820515

theorem tailTrace_1153422 : CollatzResearch.WordTrace tailWord_1153422 prefixEnd_1153422 592259883470291464820515 := by
  unfold tailWord_1153422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5258594553419569704953815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28045837618237705093087013 5258594553419569704953815)
  ·
    refine ⟨7887891830129354557430723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5258594553419569704953815 7887891830129354557430723)
    ·
      refine ⟨11831837745194031836146085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7887891830129354557430723 11831837745194031836146085)
      ·
        refine ⟨2218469577223880969277391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11831837745194031836146085 2218469577223880969277391)
        ·
          refine ⟨3327704365835821453916087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2218469577223880969277391 3327704365835821453916087)
          ·
            refine ⟨4991556548753732180874131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327704365835821453916087 4991556548753732180874131)
            ·
              refine ⟨7487334823130598271311197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4991556548753732180874131 7487334823130598271311197)
              ·
                refine ⟨2807750558673974351741699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7487334823130598271311197 2807750558673974351741699)
                ·
                  refine ⟨4211625838010961527612549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807750558673974351741699 4211625838010961527612549)
                  ·
                    refine ⟨789679844627055286427353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4211625838010961527612549 789679844627055286427353)
                    ·
                      refine ⟨592259883470291464820515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 789679844627055286427353 592259883470291464820515)
                      ·
                        rfl

theorem cell23_1153422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1153422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153422 prefixEnd_1153422 := by exact prefixLift 1153422
  have htrace : WordTrace (prefixWord ++ tailWord_1153422) baseStart_1153422 baseEnd_1153422 := by
    simpa [prefixWord, tailWord_1153422, baseEnd_1153422] using wordTrace_append hprefix tailTrace_1153422
  have hstable : (prefixWord ++ tailWord_1153422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153422).length < 2 ^ (prefixWord ++ tailWord_1153422).sum := by decide
  have hdescent : baseEnd_1153422 < baseStart_1153422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153445 : List Nat := [1, 3, 1, 2, 1, 1, 6, 3, 5]
def baseStart_1153445 : Nat := 118140960795 + 1153445 * 2 ^ 59
def prefixEnd_1153445 : Nat := 4983230072969 + 3 ^ 40 * 1153445 * 2
def baseEnd_1153445 : Nat := 65807965947260541648101

theorem tailTrace_1153445 : CollatzResearch.WordTrace tailWord_1153445 prefixEnd_1153445 65807965947260541648101 := by
  unfold tailWord_1153445
  simp only [CollatzResearch.WordTrace]
  refine ⟨42069595306273232567717789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28046396870848821711811859 42069595306273232567717789)
  ·
    refine ⟨15776098239852462212894171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42069595306273232567717789 15776098239852462212894171)
    ·
      refine ⟨23664147359778693319341257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15776098239852462212894171 23664147359778693319341257)
      ·
        refine ⟨17748110519834019989505943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23664147359778693319341257 17748110519834019989505943)
        ·
          refine ⟨26622165779751029984258915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17748110519834019989505943 26622165779751029984258915)
          ·
            refine ⟨39933248669626544976388373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26622165779751029984258915 39933248669626544976388373)
            ·
              refine ⟨1871871031388744295768205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39933248669626544976388373 1871871031388744295768205)
              ·
                refine ⟨701951636770779110913077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1871871031388744295768205 701951636770779110913077)
                ·
                  refine ⟨65807965947260541648101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 701951636770779110913077 65807965947260541648101)
                  ·
                    rfl

theorem cell23_1153445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_1153445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153445 prefixEnd_1153445 := by exact prefixLift 1153445
  have htrace : WordTrace (prefixWord ++ tailWord_1153445) baseStart_1153445 baseEnd_1153445 := by
    simpa [prefixWord, tailWord_1153445, baseEnd_1153445] using wordTrace_append hprefix tailTrace_1153445
  have hstable : (prefixWord ++ tailWord_1153445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153445).length < 2 ^ (prefixWord ++ tailWord_1153445).sum := by decide
  have hdescent : baseEnd_1153445 < baseStart_1153445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153450 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1153450 : Nat := 118140960795 + 1153450 * 2 ^ 59
def prefixEnd_1153450 : Nat := 4983230072969 + 3 ^ 40 * 1153450 * 2
def baseEnd_1153450 : Nat := 592274260928617355270387

theorem tailTrace_1153450 : CollatzResearch.WordTrace tailWord_1153450 prefixEnd_1153450 592274260928617355270387 := by
  unfold tailWord_1153450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517444417813779605412451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28046518447503412281099869 10517444417813779605412451)
  ·
    refine ⟨15776166626720669408118677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10517444417813779605412451 15776166626720669408118677)
    ·
      refine ⟨739507810627531378505563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15776166626720669408118677 739507810627531378505563)
      ·
        refine ⟨1109261715941297067758345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739507810627531378505563 1109261715941297067758345)
        ·
          refine ⟨831946286955972800818759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1109261715941297067758345 831946286955972800818759)
          ·
            refine ⟨1247919430433959201228139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831946286955972800818759 1247919430433959201228139)
            ·
              refine ⟨1871879145650938801842209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247919430433959201228139 1871879145650938801842209)
              ·
                refine ⟨1403909359238204101381657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871879145650938801842209 1403909359238204101381657)
                ·
                  refine ⟨1052932019428653076036243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1403909359238204101381657 1052932019428653076036243)
                  ·
                    refine ⟨1579398029142979614054365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1052932019428653076036243 1579398029142979614054365)
                    ·
                      refine ⟨592274260928617355270387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1579398029142979614054365 592274260928617355270387)
                      ·
                        rfl

theorem cell23_1153450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1153450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153450 prefixEnd_1153450 := by exact prefixLift 1153450
  have htrace : WordTrace (prefixWord ++ tailWord_1153450) baseStart_1153450 baseEnd_1153450 := by
    simpa [prefixWord, tailWord_1153450, baseEnd_1153450] using wordTrace_append hprefix tailTrace_1153450
  have hstable : (prefixWord ++ tailWord_1153450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153450).length < 2 ^ (prefixWord ++ tailWord_1153450).sum := by decide
  have hdescent : baseEnd_1153450 < baseStart_1153450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153458 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_1153458 : Nat := 118140960795 + 1153458 * 2 ^ 59
def prefixEnd_1153458 : Nat := 4983230072969 + 3 ^ 40 * 1153458 * 2
def baseEnd_1153458 : Nat := 197426122924617774656783

theorem tailTrace_1153458 : CollatzResearch.WordTrace tailWord_1153458 prefixEnd_1153458 197426122924617774656783 := by
  unfold tailWord_1153458
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517517363806533946985257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28046712970150757191960685 10517517363806533946985257)
  ·
    refine ⟨7888138022854900460238943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10517517363806533946985257 7888138022854900460238943)
    ·
      refine ⟨11832207034282350690358415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7888138022854900460238943 11832207034282350690358415)
      ·
        refine ⟨17748310551423526035537623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11832207034282350690358415 17748310551423526035537623)
        ·
          refine ⟨26622465827135289053306435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17748310551423526035537623 26622465827135289053306435)
          ·
            refine ⟨39933698740702933579959653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26622465827135289053306435 39933698740702933579959653)
            ·
              refine ⟨7487568513881800046242435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39933698740702933579959653 7487568513881800046242435)
              ·
                refine ⟨11231352770822700069363653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7487568513881800046242435 11231352770822700069363653)
                ·
                  refine ⟨2105878644529256263005685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11231352770822700069363653 2105878644529256263005685)
                  ·
                    refine ⟨197426122924617774656783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2105878644529256263005685 197426122924617774656783)
                    ·
                      rfl

theorem cell23_1153458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_1153458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153458 prefixEnd_1153458 := by exact prefixLift 1153458
  have htrace : WordTrace (prefixWord ++ tailWord_1153458) baseStart_1153458 baseEnd_1153458 := by
    simpa [prefixWord, tailWord_1153458, baseEnd_1153458] using wordTrace_append hprefix tailTrace_1153458
  have hstable : (prefixWord ++ tailWord_1153458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153458).length < 2 ^ (prefixWord ++ tailWord_1153458).sum := by decide
  have hdescent : baseEnd_1153458 < baseStart_1153458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153473 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1153473 : Nat := 118140960795 + 1153473 * 2 ^ 59
def prefixEnd_1153473 : Nat := 4983230072969 + 3 ^ 40 * 1153473 * 2
def baseEnd_1153473 : Nat := 592286070983670765282781

theorem tailTrace_1153473 : CollatzResearch.WordTrace tailWord_1153473 prefixEnd_1153473 592286070983670765282781 := by
  unfold tailWord_1153473
  simp only [CollatzResearch.WordTrace]
  refine ⟨42070616550171793349737073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28047077700114528899824715 42070616550171793349737073)
  ·
    refine ⟨31552962412628845012302805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42070616550171793349737073 31552962412628845012302805)
    ·
      refine ⟨739522556545988554975847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 31552962412628845012302805 739522556545988554975847)
      ·
        refine ⟨1109283834818982832463771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739522556545988554975847 1109283834818982832463771)
        ·
          refine ⟨1663925752228474248695657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109283834818982832463771 1663925752228474248695657)
          ·
            refine ⟨1247944314171355686521743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663925752228474248695657 1247944314171355686521743)
            ·
              refine ⟨1871916471257033529782615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247944314171355686521743 1871916471257033529782615)
              ·
                refine ⟨2807874706885550294673923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871916471257033529782615 2807874706885550294673923)
                ·
                  refine ⟨4211812060328325442010885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807874706885550294673923 4211812060328325442010885)
                  ·
                    refine ⟨789714761311561020377041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4211812060328325442010885 789714761311561020377041)
                    ·
                      refine ⟨592286070983670765282781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 789714761311561020377041 592286070983670765282781)
                      ·
                        rfl

theorem cell23_1153473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1153473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153473 prefixEnd_1153473 := by exact prefixLift 1153473
  have htrace : WordTrace (prefixWord ++ tailWord_1153473) baseStart_1153473 baseEnd_1153473 := by
    simpa [prefixWord, tailWord_1153473, baseEnd_1153473] using wordTrace_append hprefix tailTrace_1153473
  have hstable : (prefixWord ++ tailWord_1153473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153473).length < 2 ^ (prefixWord ++ tailWord_1153473).sum := by decide
  have hdescent : baseEnd_1153473 < baseStart_1153473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153515 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 3]
def baseStart_1153515 : Nat := 118140960795 + 1153515 * 2 ^ 59
def prefixEnd_1153515 : Nat := 4983230072969 + 3 ^ 40 * 1153515 * 2
def baseEnd_1153515 : Nat := 592307637171159600957587

theorem tailTrace_1153515 : CollatzResearch.WordTrace tailWord_1153515 prefixEnd_1153515 592307637171159600957587 := by
  unfold tailWord_1153515
  simp only [CollatzResearch.WordTrace]
  refine ⟨42072148416019634522765999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28048098944013089681843999 42072148416019634522765999)
  ·
    refine ⟨63108222624029451784148999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42072148416019634522765999 63108222624029451784148999)
    ·
      refine ⟨94662333936044177676223499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63108222624029451784148999 94662333936044177676223499)
      ·
        refine ⟨141993500904066266514335249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94662333936044177676223499 141993500904066266514335249)
        ·
          refine ⟨106495125678049699885751437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141993500904066266514335249 106495125678049699885751437)
          ·
            refine ⟨39935672129268637457156789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106495125678049699885751437 39935672129268637457156789)
            ·
              refine ⟨3743969262118934761608449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39935672129268637457156789 3743969262118934761608449)
              ·
                refine ⟨2807976946589201071206337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3743969262118934761608449 2807976946589201071206337)
                ·
                  refine ⟨2105982709941900803404753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2807976946589201071206337 2105982709941900803404753)
                  ·
                    refine ⟨1579487032456425602553565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105982709941900803404753 1579487032456425602553565)
                    ·
                      refine ⟨592307637171159600957587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1579487032456425602553565 592307637171159600957587)
                      ·
                        rfl

theorem cell23_1153515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 3].length) (baseStart_1153515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153515 prefixEnd_1153515 := by exact prefixLift 1153515
  have htrace : WordTrace (prefixWord ++ tailWord_1153515) baseStart_1153515 baseEnd_1153515 := by
    simpa [prefixWord, tailWord_1153515, baseEnd_1153515] using wordTrace_append hprefix tailTrace_1153515
  have hstable : (prefixWord ++ tailWord_1153515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153515).length < 2 ^ (prefixWord ++ tailWord_1153515).sum := by decide
  have hdescent : baseEnd_1153515 < baseStart_1153515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153585 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_1153585 : Nat := 118140960795 + 1153585 * 2 ^ 59
def prefixEnd_1153585 : Nat := 4983230072969 + 3 ^ 40 * 1153585 * 2
def baseEnd_1153585 : Nat := 592343580816974327082265

theorem tailTrace_1153585 : CollatzResearch.WordTrace tailWord_1153585 prefixEnd_1153585 592343580816974327082265 := by
  unfold tailWord_1153585
  simp only [CollatzResearch.WordTrace]
  refine ⟨42074701525766036477814209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28049801017177357651876139 42074701525766036477814209)
  ·
    refine ⟨31556026144324527358360657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42074701525766036477814209 31556026144324527358360657)
    ·
      refine ⟨23667019608243395518770493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31556026144324527358360657 23667019608243395518770493)
      ·
        refine ⟨8875132353091273319538935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23667019608243395518770493 8875132353091273319538935)
        ·
          refine ⟨13312698529636909979308403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8875132353091273319538935 13312698529636909979308403)
          ·
            refine ⟨19969047794455364968962605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13312698529636909979308403 19969047794455364968962605)
            ·
              refine ⟨7488392922920761863360977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19969047794455364968962605 7488392922920761863360977)
              ·
                refine ⟨5616294692190571397520733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7488392922920761863360977 5616294692190571397520733)
                ·
                  refine ⟨2106110509571464274070275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5616294692190571397520733 2106110509571464274070275)
                  ·
                    refine ⟨3159165764357196411105413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2106110509571464274070275 3159165764357196411105413)
                    ·
                      refine ⟨592343580816974327082265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3159165764357196411105413 592343580816974327082265)
                      ·
                        rfl

theorem cell23_1153585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_1153585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153585 prefixEnd_1153585 := by exact prefixLift 1153585
  have htrace : WordTrace (prefixWord ++ tailWord_1153585) baseStart_1153585 baseEnd_1153585 := by
    simpa [prefixWord, tailWord_1153585, baseEnd_1153585] using wordTrace_append hprefix tailTrace_1153585
  have hstable : (prefixWord ++ tailWord_1153585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153585).length < 2 ^ (prefixWord ++ tailWord_1153585).sum := by decide
  have hdescent : baseEnd_1153585 < baseStart_1153585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153606 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_1153606 : Nat := 118140960795 + 1153606 * 2 ^ 59
def prefixEnd_1153606 : Nat := 4983230072969 + 3 ^ 40 * 1153606 * 2
def baseEnd_1153606 : Nat := 592354363910718744919669

theorem tailTrace_1153606 : CollatzResearch.WordTrace tailWord_1153606 prefixEnd_1153606 592354363910718744919669 := by
  unfold tailWord_1153606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1314858358084061158260271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28050311639126638042885781 1314858358084061158260271)
  ·
    refine ⟨1972287537126091737390407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1314858358084061158260271 1972287537126091737390407)
    ·
      refine ⟨2958431305689137606085611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1972287537126091737390407 2958431305689137606085611)
      ·
        refine ⟨4437646958533706409128417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2958431305689137606085611 4437646958533706409128417)
        ·
          refine ⟨3328235218900279806846313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4437646958533706409128417 3328235218900279806846313)
          ·
            refine ⟨2496176414175209855134735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3328235218900279806846313 2496176414175209855134735)
            ·
              refine ⟨3744264621262814782702103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496176414175209855134735 3744264621262814782702103)
              ·
                refine ⟨5616396931894222174053155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3744264621262814782702103 5616396931894222174053155)
                ·
                  refine ⟨8424595397841333261079733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5616396931894222174053155 8424595397841333261079733)
                  ·
                    refine ⟨789805818547624993226225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8424595397841333261079733 789805818547624993226225)
                    ·
                      refine ⟨592354363910718744919669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 789805818547624993226225 592354363910718744919669)
                      ·
                        rfl

theorem cell23_1153606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_1153606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153606 prefixEnd_1153606 := by exact prefixLift 1153606
  have htrace : WordTrace (prefixWord ++ tailWord_1153606) baseStart_1153606 baseEnd_1153606 := by
    simpa [prefixWord, tailWord_1153606, baseEnd_1153606] using wordTrace_append hprefix tailTrace_1153606
  have hstable : (prefixWord ++ tailWord_1153606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153606).length < 2 ^ (prefixWord ++ tailWord_1153606).sum := by decide
  have hdescent : baseEnd_1153606 < baseStart_1153606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153608 : List Nat := [2, 1, 3, 1, 1, 1, 1, 13]
def baseStart_1153608 : Nat := 118140960795 + 1153608 * 2 ^ 59
def prefixEnd_1153608 : Nat := 4983230072969 + 3 ^ 40 * 1153608 * 2
def baseEnd_1153608 : Nat := 21939088550815842114617

theorem tailTrace_1153608 : CollatzResearch.WordTrace tailWord_1153608 prefixEnd_1153608 21939088550815842114617 := by
  unfold tailWord_1153608
  simp only [CollatzResearch.WordTrace]
  refine ⟨21037770202341355702950739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28050360269788474270600985 21037770202341355702950739)
  ·
    refine ⟨31556655303512033554426109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21037770202341355702950739 31556655303512033554426109)
    ·
      refine ⟨11833745738817012582909791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31556655303512033554426109 11833745738817012582909791)
      ·
        refine ⟨17750618608225518874364687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11833745738817012582909791 17750618608225518874364687)
        ·
          refine ⟨26625927912338278311547031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17750618608225518874364687 26625927912338278311547031)
          ·
            refine ⟨39938891868507417467320547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26625927912338278311547031 39938891868507417467320547)
            ·
              refine ⟨59908337802761126200980821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39938891868507417467320547 59908337802761126200980821)
              ·
                refine ⟨21939088550815842114617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 59908337802761126200980821 21939088550815842114617)
                ·
                  rfl

theorem cell23_1153608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 13].length) (baseStart_1153608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153608 prefixEnd_1153608 := by exact prefixLift 1153608
  have htrace : WordTrace (prefixWord ++ tailWord_1153608) baseStart_1153608 baseEnd_1153608 := by
    simpa [prefixWord, tailWord_1153608, baseEnd_1153608] using wordTrace_append hprefix tailTrace_1153608
  have hstable : (prefixWord ++ tailWord_1153608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153608).length < 2 ^ (prefixWord ++ tailWord_1153608).sum := by decide
  have hdescent : baseEnd_1153608 < baseStart_1153608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153613 : List Nat := [1, 6, 1, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_1153613 : Nat := 118140960795 + 1153613 * 2 ^ 59
def prefixEnd_1153613 : Nat := 4983230072969 + 3 ^ 40 * 1153613 * 2
def baseEnd_1153613 : Nat := 592357958275300217532137

theorem tailTrace_1153613 : CollatzResearch.WordTrace tailWord_1153613 prefixEnd_1153613 592357958275300217532137 := by
  unfold tailWord_1153613
  simp only [CollatzResearch.WordTrace]
  refine ⟨42075722769664597259833493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28050481846443064839888995 42075722769664597259833493)
  ·
    refine ⟨1972299504828027996554695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42075722769664597259833493 1972299504828027996554695)
    ·
      refine ⟨2958449257242041994832043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1972299504828027996554695 2958449257242041994832043)
      ·
        refine ⟨4437673885863062992248065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2958449257242041994832043 4437673885863062992248065)
        ·
          refine ⟨3328255414397297244186049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4437673885863062992248065 3328255414397297244186049)
          ·
            refine ⟨2496191560797972933139537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3328255414397297244186049 2496191560797972933139537)
            ·
              refine ⟨1872143670598479699854653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496191560797972933139537 1872143670598479699854653)
              ·
                refine ⟨702053876474429887445495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1872143670598479699854653 702053876474429887445495)
                ·
                  refine ⟨1053080814711644831168243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702053876474429887445495 1053080814711644831168243)
                  ·
                    refine ⟨1579621222067467246752365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1053080814711644831168243 1579621222067467246752365)
                    ·
                      refine ⟨592357958275300217532137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1579621222067467246752365 592357958275300217532137)
                      ·
                        rfl

theorem cell23_1153613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_1153613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153613 prefixEnd_1153613 := by exact prefixLift 1153613
  have htrace : WordTrace (prefixWord ++ tailWord_1153613) baseStart_1153613 baseEnd_1153613 := by
    simpa [prefixWord, tailWord_1153613, baseEnd_1153613] using wordTrace_append hprefix tailTrace_1153613
  have hstable : (prefixWord ++ tailWord_1153613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153613).length < 2 ^ (prefixWord ++ tailWord_1153613).sum := by decide
  have hdescent : baseEnd_1153613 < baseStart_1153613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153615 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 4]
def baseStart_1153615 : Nat := 118140960795 + 1153615 * 2 ^ 59
def prefixEnd_1153615 : Nat := 4983230072969 + 3 ^ 40 * 1153615 * 2
def baseEnd_1153615 : Nat := 592358985236609209707127

theorem tailTrace_1153615 : CollatzResearch.WordTrace tailWord_1153615 prefixEnd_1153615 592358985236609209707127 := by
  unfold tailWord_1153615
  simp only [CollatzResearch.WordTrace]
  refine ⟨42075795715657351601406299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28050530477104901067604199 42075795715657351601406299)
  ·
    refine ⟨63113693573486027402109449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42075795715657351601406299 63113693573486027402109449)
    ·
      refine ⟨47335270180114520551582087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63113693573486027402109449 47335270180114520551582087)
      ·
        refine ⟨71002905270171780827373131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47335270180114520551582087 71002905270171780827373131)
        ·
          refine ⟨106504357905257671241059697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71002905270171780827373131 106504357905257671241059697)
          ·
            refine ⟨79878268428943253430794773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106504357905257671241059697 79878268428943253430794773)
            ·
              refine ⟨3744293832606715004568505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79878268428943253430794773 3744293832606715004568505)
              ·
                refine ⟨2808220374455036253426379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3744293832606715004568505 2808220374455036253426379)
                ·
                  refine ⟨4212330561682554380139569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808220374455036253426379 4212330561682554380139569)
                  ·
                    refine ⟨3159247921261915785104677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4212330561682554380139569 3159247921261915785104677)
                    ·
                      refine ⟨592358985236609209707127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3159247921261915785104677 592358985236609209707127)
                      ·
                        rfl

theorem cell23_1153615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_1153615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153615 prefixEnd_1153615 := by exact prefixLift 1153615
  have htrace : WordTrace (prefixWord ++ tailWord_1153615) baseStart_1153615 baseEnd_1153615 := by
    simpa [prefixWord, tailWord_1153615, baseEnd_1153615] using wordTrace_append hprefix tailTrace_1153615
  have hstable : (prefixWord ++ tailWord_1153615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153615).length < 2 ^ (prefixWord ++ tailWord_1153615).sum := by decide
  have hdescent : baseEnd_1153615 < baseStart_1153615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153630 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1153630 : Nat := 118140960795 + 1153630 * 2 ^ 59
def prefixEnd_1153630 : Nat := 4983230072969 + 3 ^ 40 * 1153630 * 2
def baseEnd_1153630 : Nat := 592366687446426651019559

theorem tailTrace_1153630 : CollatzResearch.WordTrace tailWord_1153630 prefixEnd_1153630 592366687446426651019559 := by
  unfold tailWord_1153630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5259542851325376145400293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28050895207068672775468229 5259542851325376145400293)
  ·
    refine ⟨986164284623508027262555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5259542851325376145400293 986164284623508027262555)
    ·
      refine ⟨1479246426935262040893833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 986164284623508027262555 1479246426935262040893833)
      ·
        refine ⟨1109434820201446530670375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1479246426935262040893833 1109434820201446530670375)
        ·
          refine ⟨1664152230302169796005563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109434820201446530670375 1664152230302169796005563)
          ·
            refine ⟨2496228345453254694008345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664152230302169796005563 2496228345453254694008345)
            ·
              refine ⟨1872171259089941020506259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496228345453254694008345 1872171259089941020506259)
              ·
                refine ⟨2808256888634911530759389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872171259089941020506259 2808256888634911530759389)
                ·
                  refine ⟨1053096333238091824034771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2808256888634911530759389 1053096333238091824034771)
                  ·
                    refine ⟨1579644499857137736052157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1053096333238091824034771 1579644499857137736052157)
                    ·
                      refine ⟨592366687446426651019559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1579644499857137736052157 592366687446426651019559)
                      ·
                        rfl

theorem cell23_1153630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1153630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153630 prefixEnd_1153630 := by exact prefixLift 1153630
  have htrace : WordTrace (prefixWord ++ tailWord_1153630) baseStart_1153630 baseEnd_1153630 := by
    simpa [prefixWord, tailWord_1153630, baseEnd_1153630] using wordTrace_append hprefix tailTrace_1153630
  have hstable : (prefixWord ++ tailWord_1153630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153630).length < 2 ^ (prefixWord ++ tailWord_1153630).sum := by decide
  have hdescent : baseEnd_1153630 < baseStart_1153630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153636 : List Nat := [2, 3, 1, 1, 2, 2, 1, 6, 1, 2, 2]
def baseStart_1153636 : Nat := 118140960795 + 1153636 * 2 ^ 59
def prefixEnd_1153636 : Nat := 4983230072969 + 3 ^ 40 * 1153636 * 2
def baseEnd_1153636 : Nat := 592369768330353627544531

theorem tailTrace_1153636 : CollatzResearch.WordTrace tailWord_1153636 prefixEnd_1153636 592369768330353627544531 := by
  unfold tailWord_1153636
  simp only [CollatzResearch.WordTrace]
  refine ⟨21038280824290636093960381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28051041099054181458613841 21038280824290636093960381)
  ·
    refine ⟨7889355309108988535235143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21038280824290636093960381 7889355309108988535235143)
    ·
      refine ⟨11834032963663482802852715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7889355309108988535235143 11834032963663482802852715)
      ·
        refine ⟨17751049445495224204279073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11834032963663482802852715 17751049445495224204279073)
        ·
          refine ⟨13313287084121418153209305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17751049445495224204279073 13313287084121418153209305)
          ·
            refine ⟨9984965313091063614906979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13313287084121418153209305 9984965313091063614906979)
            ·
              refine ⟨14977447969636595422360469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9984965313091063614906979 14977447969636595422360469)
              ·
                refine ⟨702067873576715410423147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14977447969636595422360469 702067873576715410423147)
                ·
                  refine ⟨1053101810365073115634721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702067873576715410423147 1053101810365073115634721)
                  ·
                    refine ⟨789826357773804836726041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1053101810365073115634721 789826357773804836726041)
                    ·
                      refine ⟨592369768330353627544531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 789826357773804836726041 592369768330353627544531)
                      ·
                        rfl

theorem cell23_1153636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_1153636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153636 prefixEnd_1153636 := by exact prefixLift 1153636
  have htrace : WordTrace (prefixWord ++ tailWord_1153636) baseStart_1153636 baseEnd_1153636 := by
    simpa [prefixWord, tailWord_1153636, baseEnd_1153636] using wordTrace_append hprefix tailTrace_1153636
  have hstable : (prefixWord ++ tailWord_1153636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153636).length < 2 ^ (prefixWord ++ tailWord_1153636).sum := by decide
  have hdescent : baseEnd_1153636 < baseStart_1153636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153646 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_1153646 : Nat := 118140960795 + 1153646 * 2 ^ 59
def prefixEnd_1153646 : Nat := 4983230072969 + 3 ^ 40 * 1153646 * 2
def baseEnd_1153646 : Nat := 197458301045632862806495

theorem tailTrace_1153646 : CollatzResearch.WordTrace tailWord_1153646 prefixEnd_1153646 197458301045632862806495 := by
  unfold tailWord_1153646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5259615797318130486973099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28051284252363362597189861 5259615797318130486973099)
  ·
    refine ⟨7889423695977195730459649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5259615797318130486973099 7889423695977195730459649)
    ·
      refine ⟨5917067771982896797844737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7889423695977195730459649 5917067771982896797844737)
      ·
        refine ⟨4437800828987172598383553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5917067771982896797844737 4437800828987172598383553)
        ·
          refine ⟨3328350621740379448787665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4437800828987172598383553 3328350621740379448787665)
          ·
            refine ⟨2496262966305284586590749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3328350621740379448787665 2496262966305284586590749)
            ·
              refine ⟨936098612364481719971531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2496262966305284586590749 936098612364481719971531)
              ·
                refine ⟨1404147918546722579957297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936098612364481719971531 1404147918546722579957297)
                ·
                  refine ⟨1053110938910041934967973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1404147918546722579957297 1053110938910041934967973)
                  ·
                    refine ⟨197458301045632862806495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1053110938910041934967973 197458301045632862806495)
                    ·
                      rfl

theorem cell23_1153646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_1153646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153646 prefixEnd_1153646 := by exact prefixLift 1153646
  have htrace : WordTrace (prefixWord ++ tailWord_1153646) baseStart_1153646 baseEnd_1153646 := by
    simpa [prefixWord, tailWord_1153646, baseEnd_1153646] using wordTrace_append hprefix tailTrace_1153646
  have hstable : (prefixWord ++ tailWord_1153646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153646).length < 2 ^ (prefixWord ++ tailWord_1153646).sum := by decide
  have hdescent : baseEnd_1153646 < baseStart_1153646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153665 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1153665 : Nat := 118140960795 + 1153665 * 2 ^ 59
def prefixEnd_1153665 : Nat := 4983230072969 + 3 ^ 40 * 1153665 * 2
def baseEnd_1153665 : Nat := 592384659269334014081897

theorem tailTrace_1153665 : CollatzResearch.WordTrace tailWord_1153665 prefixEnd_1153665 592384659269334014081897 := by
  unfold tailWord_1153665
  simp only [CollatzResearch.WordTrace]
  refine ⟨42077619365476210140726449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28051746243650806760484299 42077619365476210140726449)
  ·
    refine ⟨31558214524107157605544837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42077619365476210140726449 31558214524107157605544837)
    ·
      refine ⟨5917165223270092051039657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31558214524107157605544837 5917165223270092051039657)
      ·
        refine ⟨4437873917452569038279743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5917165223270092051039657 4437873917452569038279743)
        ·
          refine ⟨6656810876178853557419615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4437873917452569038279743 6656810876178853557419615)
          ·
            refine ⟨9985216314268280336129423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6656810876178853557419615 9985216314268280336129423)
            ·
              refine ⟨14977824471402420504194135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9985216314268280336129423 14977824471402420504194135)
              ·
                refine ⟨22466736707103630756291203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14977824471402420504194135 22466736707103630756291203)
                ·
                  refine ⟨33700105060655446134436805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22466736707103630756291203 33700105060655446134436805)
                  ·
                    refine ⟨6318769698872896150206901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33700105060655446134436805 6318769698872896150206901)
                    ·
                      refine ⟨592384659269334014081897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6318769698872896150206901 592384659269334014081897)
                      ·
                        rfl

theorem cell23_1153665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1153665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153665 prefixEnd_1153665 := by exact prefixLift 1153665
  have htrace : WordTrace (prefixWord ++ tailWord_1153665) baseStart_1153665 baseEnd_1153665 := by
    simpa [prefixWord, tailWord_1153665, baseEnd_1153665] using wordTrace_append hprefix tailTrace_1153665
  have hstable : (prefixWord ++ tailWord_1153665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153665).length < 2 ^ (prefixWord ++ tailWord_1153665).sum := by decide
  have hdescent : baseEnd_1153665 < baseStart_1153665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153703 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1153703 : Nat := 118140960795 + 1153703 * 2 ^ 59
def prefixEnd_1153703 : Nat := 4983230072969 + 3 ^ 40 * 1153703 * 2
def baseEnd_1153703 : Nat := 592404171534204865406723

theorem tailTrace_1153703 : CollatzResearch.WordTrace tailWord_1153703 prefixEnd_1153703 592404171534204865406723 := by
  unfold tailWord_1153703
  simp only [CollatzResearch.WordTrace]
  refine ⟨42079005339338542630609763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28052670226225695087073175 42079005339338542630609763)
  ·
    refine ⟨63118508009007813945914645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42079005339338542630609763 63118508009007813945914645)
    ·
      refine ⟨2958680062922241278714749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63118508009007813945914645 2958680062922241278714749)
      ·
        refine ⟨1109505023595840479518031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2958680062922241278714749 1109505023595840479518031)
        ·
          refine ⟨1664257535393760719277047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109505023595840479518031 1664257535393760719277047)
          ·
            refine ⟨2496386303090641078915571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664257535393760719277047 2496386303090641078915571)
            ·
              refine ⟨3744579454635961618373357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2496386303090641078915571 3744579454635961618373357)
              ·
                refine ⟨1404217295488485606890009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3744579454635961618373357 1404217295488485606890009)
                ·
                  refine ⟨1053162971616364205167507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1404217295488485606890009 1053162971616364205167507)
                  ·
                    refine ⟨1579744457424546307751261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1053162971616364205167507 1579744457424546307751261)
                    ·
                      refine ⟨592404171534204865406723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1579744457424546307751261 592404171534204865406723)
                      ·
                        rfl

theorem cell23_1153703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1153703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153703 prefixEnd_1153703 := by exact prefixLift 1153703
  have htrace : WordTrace (prefixWord ++ tailWord_1153703) baseStart_1153703 baseEnd_1153703 := by
    simpa [prefixWord, tailWord_1153703, baseEnd_1153703] using wordTrace_append hprefix tailTrace_1153703
  have hstable : (prefixWord ++ tailWord_1153703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153703).length < 2 ^ (prefixWord ++ tailWord_1153703).sum := by decide
  have hdescent : baseEnd_1153703 < baseStart_1153703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153843 : List Nat := [1, 1, 1, 2, 6, 3, 1, 3, 1, 4]
def baseStart_1153843 : Nat := 118140960795 + 1153843 * 2 ^ 59
def prefixEnd_1153843 : Nat := 4983230072969 + 3 ^ 40 * 1153843 * 2
def baseEnd_1153843 : Nat := 197492019608611439218693

theorem tailTrace_1153843 : CollatzResearch.WordTrace tailWord_1153843 prefixEnd_1153843 197492019608611439218693 := by
  unfold tailWord_1153843
  simp only [CollatzResearch.WordTrace]
  refine ⟨42084111558831346540706183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28056074372554231027137455 42084111558831346540706183)
  ·
    refine ⟨63126167338247019811059275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42084111558831346540706183 63126167338247019811059275)
    ·
      refine ⟨94689251007370529716588913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63126167338247019811059275 94689251007370529716588913)
      ·
        refine ⟨71016938255527897287441685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94689251007370529716588913 71016938255527897287441685)
        ·
          refine ⟨3328918980727870185348829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71016938255527897287441685 3328918980727870185348829)
          ·
            refine ⟨1248344617772951319505811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3328918980727870185348829 1248344617772951319505811)
            ·
              refine ⟨1872516926659426979258717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248344617772951319505811 1872516926659426979258717)
              ·
                refine ⟨702193847497285117222019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1872516926659426979258717 702193847497285117222019)
                ·
                  refine ⟨1053290771245927675833029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702193847497285117222019 1053290771245927675833029)
                  ·
                    refine ⟨197492019608611439218693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1053290771245927675833029 197492019608611439218693)
                    ·
                      rfl

theorem cell23_1153843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 1, 4].length) (baseStart_1153843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153843 prefixEnd_1153843 := by exact prefixLift 1153843
  have htrace : WordTrace (prefixWord ++ tailWord_1153843) baseStart_1153843 baseEnd_1153843 := by
    simpa [prefixWord, tailWord_1153843, baseEnd_1153843] using wordTrace_append hprefix tailTrace_1153843
  have hstable : (prefixWord ++ tailWord_1153843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153843).length < 2 ^ (prefixWord ++ tailWord_1153843).sum := by decide
  have hdescent : baseEnd_1153843 < baseStart_1153843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153852 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_1153852 : Nat := 118140960795 + 1153852 * 2 ^ 59
def prefixEnd_1153852 : Nat := 4983230072969 + 3 ^ 40 * 1153852 * 2
def baseEnd_1153852 : Nat := 197493560050574927481179

theorem tailTrace_1153852 : CollatzResearch.WordTrace tailWord_1153852 prefixEnd_1153852 197493560050574927481179 := by
  unfold tailWord_1153852
  simp only [CollatzResearch.WordTrace]
  refine ⟨21042219907899370538891905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28056293210532494051855873 21042219907899370538891905)
  ·
    refine ⟨15781664930924527904168929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21042219907899370538891905 15781664930924527904168929)
    ·
      refine ⟨11836248698193395928126697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15781664930924527904168929 11836248698193395928126697)
      ·
        refine ⟨8877186523645046946095023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11836248698193395928126697 8877186523645046946095023)
        ·
          refine ⟨13315779785467570419142535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8877186523645046946095023 13315779785467570419142535)
          ·
            refine ⟨19973669678201355628713803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13315779785467570419142535 19973669678201355628713803)
            ·
              refine ⟨29960504517302033443070705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19973669678201355628713803 29960504517302033443070705)
              ·
                refine ⟨22470378387976525082303029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29960504517302033443070705 22470378387976525082303029)
                ·
                  refine ⟨2106597973872799226465909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22470378387976525082303029 2106597973872799226465909)
                  ·
                    refine ⟨197493560050574927481179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2106597973872799226465909 197493560050574927481179)
                    ·
                      rfl

theorem cell23_1153852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_1153852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153852 prefixEnd_1153852 := by exact prefixLift 1153852
  have htrace : WordTrace (prefixWord ++ tailWord_1153852) baseStart_1153852 baseEnd_1153852 := by
    simpa [prefixWord, tailWord_1153852, baseEnd_1153852] using wordTrace_append hprefix tailTrace_1153852
  have hstable : (prefixWord ++ tailWord_1153852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153852).length < 2 ^ (prefixWord ++ tailWord_1153852).sum := by decide
  have hdescent : baseEnd_1153852 < baseStart_1153852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153860 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1153860 : Nat := 118140960795 + 1153860 * 2 ^ 59
def prefixEnd_1153860 : Nat := 4983230072969 + 3 ^ 40 * 1153860 * 2
def baseEnd_1153860 : Nat := 197494929332320250381167

theorem tailTrace_1153860 : CollatzResearch.WordTrace tailWord_1153860 prefixEnd_1153860 197494929332320250381167 := by
  unfold tailWord_1153860
  simp only [CollatzResearch.WordTrace]
  refine ⟨21042365799884879222037517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28056487733179838962716689 21042365799884879222037517)
  ·
    refine ⟨7890887174956829708264069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21042365799884879222037517 7890887174956829708264069)
    ·
      refine ⟨1479541345304405570299513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7890887174956829708264069 1479541345304405570299513)
      ·
        refine ⟨1109656008978304177724635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1479541345304405570299513 1109656008978304177724635)
        ·
          refine ⟨1664484013467456266586953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109656008978304177724635 1664484013467456266586953)
          ·
            refine ⟨1248363010100592199940215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664484013467456266586953 1248363010100592199940215)
            ·
              refine ⟨1872544515150888299910323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248363010100592199940215 1872544515150888299910323)
              ·
                refine ⟨2808816772726332449865485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872544515150888299910323 2808816772726332449865485)
                ·
                  refine ⟨1053306289772374668699557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2808816772726332449865485 1053306289772374668699557)
                  ·
                    refine ⟨197494929332320250381167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1053306289772374668699557 197494929332320250381167)
                    ·
                      rfl

theorem cell23_1153860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1153860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153860 prefixEnd_1153860 := by exact prefixLift 1153860
  have htrace : WordTrace (prefixWord ++ tailWord_1153860) baseStart_1153860 baseEnd_1153860 := by
    simpa [prefixWord, tailWord_1153860, baseEnd_1153860] using wordTrace_append hprefix tailTrace_1153860
  have hstable : (prefixWord ++ tailWord_1153860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153860).length < 2 ^ (prefixWord ++ tailWord_1153860).sum := by decide
  have hdescent : baseEnd_1153860 < baseStart_1153860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153873 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 6]
def baseStart_1153873 : Nat := 118140960795 + 1153873 * 2 ^ 59
def prefixEnd_1153873 : Nat := 4983230072969 + 3 ^ 40 * 1153873 * 2
def baseEnd_1153873 : Nat := 65832384805052133364549

theorem tailTrace_1153873 : CollatzResearch.WordTrace tailWord_1153873 prefixEnd_1153873 65832384805052133364549 := by
  unfold tailWord_1153873
  simp only [CollatzResearch.WordTrace]
  refine ⟨42085205748722661664298273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28056803832481774442865515 42085205748722661664298273)
  ·
    refine ⟨31563904311541996248223705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42085205748722661664298273 31563904311541996248223705)
    ·
      refine ⟨23672928233656497186167779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31563904311541996248223705 23672928233656497186167779)
      ·
        refine ⟨35509392350484745779251669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23672928233656497186167779 35509392350484745779251669)
        ·
          refine ⟨832251383214486229201211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35509392350484745779251669 832251383214486229201211)
          ·
            refine ⟨1248377074821729343801817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832251383214486229201211 1248377074821729343801817)
            ·
              refine ⟨936282806116297007851363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248377074821729343801817 936282806116297007851363)
              ·
                refine ⟨1404424209174445511777045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936282806116297007851363 1404424209174445511777045)
                ·
                  refine ⟨65832384805052133364549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1404424209174445511777045 65832384805052133364549)
                  ·
                    rfl

theorem cell23_1153873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 6].length) (baseStart_1153873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153873 prefixEnd_1153873 := by exact prefixLift 1153873
  have htrace : WordTrace (prefixWord ++ tailWord_1153873) baseStart_1153873 baseEnd_1153873 := by
    simpa [prefixWord, tailWord_1153873, baseEnd_1153873] using wordTrace_append hprefix tailTrace_1153873
  have hstable : (prefixWord ++ tailWord_1153873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153873).length < 2 ^ (prefixWord ++ tailWord_1153873).sum := by decide
  have hdescent : baseEnd_1153873 < baseStart_1153873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153889 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_1153889 : Nat := 118140960795 + 1153889 * 2 ^ 59
def prefixEnd_1153889 : Nat := 4983230072969 + 3 ^ 40 * 1153889 * 2
def baseEnd_1153889 : Nat := 592499678935941137680867

theorem tailTrace_1153889 : CollatzResearch.WordTrace tailWord_1153889 prefixEnd_1153889 592499678935941137680867 := by
  unfold tailWord_1153889
  simp only [CollatzResearch.WordTrace]
  refine ⟨42085789316664696396880721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28057192877776464264587147 42085789316664696396880721)
  ·
    refine ⟨31564341987498522297660541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42085789316664696396880721 31564341987498522297660541)
    ·
      refine ⟨11836628245311945861622703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31564341987498522297660541 11836628245311945861622703)
      ·
        refine ⟨17754942367967918792434055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11836628245311945861622703 17754942367967918792434055)
        ·
          refine ⟨26632413551951878188651083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17754942367967918792434055 26632413551951878188651083)
          ·
            refine ⟨39948620327927817282976625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26632413551951878188651083 39948620327927817282976625)
            ·
              refine ⟨29961465245945862962232469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39948620327927817282976625 29961465245945862962232469)
              ·
                refine ⟨1404443683403712326354647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29961465245945862962232469 1404443683403712326354647)
                ·
                  refine ⟨2106665525105568489531971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404443683403712326354647 2106665525105568489531971)
                  ·
                    refine ⟨3159998287658352734297957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2106665525105568489531971 3159998287658352734297957)
                    ·
                      refine ⟨592499678935941137680867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3159998287658352734297957 592499678935941137680867)
                      ·
                        rfl

theorem cell23_1153889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_1153889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153889 prefixEnd_1153889 := by exact prefixLift 1153889
  have htrace : WordTrace (prefixWord ++ tailWord_1153889) baseStart_1153889 baseEnd_1153889 := by
    simpa [prefixWord, tailWord_1153889, baseEnd_1153889] using wordTrace_append hprefix tailTrace_1153889
  have hstable : (prefixWord ++ tailWord_1153889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153889).length < 2 ^ (prefixWord ++ tailWord_1153889).sum := by decide
  have hdescent : baseEnd_1153889 < baseStart_1153889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153929 : List Nat := [1, 2, 1, 1, 5, 4, 1, 8]
def baseStart_1153929 : Nat := 118140960795 + 1153929 * 2 ^ 59
def prefixEnd_1153929 : Nat := 4983230072969 + 3 ^ 40 * 1153929 * 2
def baseEnd_1153929 : Nat := 21945193265263740043729

theorem tailTrace_1153929 : CollatzResearch.WordTrace tailWord_1153929 prefixEnd_1153929 21945193265263740043729 := by
  unfold tailWord_1153929
  simp only [CollatzResearch.WordTrace]
  refine ⟨42087248236519783228336841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28058165491013188818891227 42087248236519783228336841)
  ·
    refine ⟨31565436177389837421252631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42087248236519783228336841 31565436177389837421252631)
    ·
      refine ⟨47348154266084756131878947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31565436177389837421252631 47348154266084756131878947)
      ·
        refine ⟨71022231399127134197818421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47348154266084756131878947 71022231399127134197818421)
        ·
          refine ⟨6658334193668168831045477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71022231399127134197818421 6658334193668168831045477)
          ·
            refine ⟨1248437661312781655821027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6658334193668168831045477 1248437661312781655821027)
            ·
              refine ⟨1872656491969172483731541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248437661312781655821027 1872656491969172483731541)
              ·
                refine ⟨21945193265263740043729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1872656491969172483731541 21945193265263740043729)
                ·
                  rfl

theorem cell23_1153929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 8].length) (baseStart_1153929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153929 prefixEnd_1153929 := by exact prefixLift 1153929
  have htrace : WordTrace (prefixWord ++ tailWord_1153929) baseStart_1153929 baseEnd_1153929 := by
    simpa [prefixWord, tailWord_1153929, baseEnd_1153929] using wordTrace_append hprefix tailTrace_1153929
  have hstable : (prefixWord ++ tailWord_1153929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153929).length < 2 ^ (prefixWord ++ tailWord_1153929).sum := by decide
  have hdescent : baseEnd_1153929 < baseStart_1153929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153932 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1153932 : Nat := 118140960795 + 1153932 * 2 ^ 59
def prefixEnd_1153932 : Nat := 4983230072969 + 3 ^ 40 * 1153932 * 2
def baseEnd_1153932 : Nat := 592521758604084469443169

theorem tailTrace_1153932 : CollatzResearch.WordTrace tailWord_1153932 prefixEnd_1153932 592521758604084469443169 := by
  unfold tailWord_1153932
  simp only [CollatzResearch.WordTrace]
  refine ⟨21043678827754457370348025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28058238437005943160464033 21043678827754457370348025)
  ·
    refine ⟨15782759120815843027761019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21043678827754457370348025 15782759120815843027761019)
    ·
      refine ⟨23674138681223764541641529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15782759120815843027761019 23674138681223764541641529)
      ·
        refine ⟨17755604010917823406231147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23674138681223764541641529 17755604010917823406231147)
        ·
          refine ⟨26633406016376735109346721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17755604010917823406231147 26633406016376735109346721)
          ·
            refine ⟨19975054512282551332010041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26633406016376735109346721 19975054512282551332010041)
            ·
              refine ⟨14981290884211913499007531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19975054512282551332010041 14981290884211913499007531)
              ·
                refine ⟨22471936326317870248511297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14981290884211913499007531 22471936326317870248511297)
                ·
                  refine ⟨16853952244738402686383473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22471936326317870248511297 16853952244738402686383473)
                  ·
                    refine ⟨12640464183553802014787605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16853952244738402686383473 12640464183553802014787605)
                    ·
                      refine ⟨592521758604084469443169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12640464183553802014787605 592521758604084469443169)
                      ·
                        rfl

theorem cell23_1153932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1153932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153932 prefixEnd_1153932 := by exact prefixLift 1153932
  have htrace : WordTrace (prefixWord ++ tailWord_1153932) baseStart_1153932 baseEnd_1153932 := by
    simpa [prefixWord, tailWord_1153932, baseEnd_1153932] using wordTrace_append hprefix tailTrace_1153932
  have hstable : (prefixWord ++ tailWord_1153932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153932).length < 2 ^ (prefixWord ++ tailWord_1153932).sum := by decide
  have hdescent : baseEnd_1153932 < baseStart_1153932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153946 : List Nat := [3, 1, 1, 4, 3, 1, 3, 7]
def baseStart_1153946 : Nat := 118140960795 + 1153946 * 2 ^ 59
def prefixEnd_1153946 : Nat := 4983230072969 + 3 ^ 40 * 1153946 * 2
def baseEnd_1153946 : Nat := 21945516567898052395115

theorem tailTrace_1153946 : CollatzResearch.WordTrace tailWord_1153946 prefixEnd_1153946 21945516567898052395115 := by
  unfold tailWord_1153946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10521967069364548782926423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28058578851638796754470461 10521967069364548782926423)
  ·
    refine ⟨15782950604046823174389635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10521967069364548782926423 15782950604046823174389635)
    ·
      refine ⟨23674425906070234761584453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15782950604046823174389635 23674425906070234761584453)
      ·
        refine ⟨4438954857388169017797085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23674425906070234761584453 4438954857388169017797085)
        ·
          refine ⟨1664608071520563381673907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4438954857388169017797085 1664608071520563381673907)
          ·
            refine ⟨2496912107280845072510861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664608071520563381673907 2496912107280845072510861)
            ·
              refine ⟨936342040230316902191573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2496912107280845072510861 936342040230316902191573)
              ·
                refine ⟨21945516567898052395115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 936342040230316902191573 21945516567898052395115)
                ·
                  rfl

theorem cell23_1153946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 7].length) (baseStart_1153946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153946 prefixEnd_1153946 := by exact prefixLift 1153946
  have htrace : WordTrace (prefixWord ++ tailWord_1153946) baseStart_1153946 baseEnd_1153946 := by
    simpa [prefixWord, tailWord_1153946, baseEnd_1153946] using wordTrace_append hprefix tailTrace_1153946
  have hstable : (prefixWord ++ tailWord_1153946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153946).length < 2 ^ (prefixWord ++ tailWord_1153946).sum := by decide
  have hdescent : baseEnd_1153946 < baseStart_1153946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153956 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_1153956 : Nat := 118140960795 + 1153956 * 2 ^ 59
def prefixEnd_1153956 : Nat := 4983230072969 + 3 ^ 40 * 1153956 * 2
def baseEnd_1153956 : Nat := 592534082139792375543059

theorem tailTrace_1153956 : CollatzResearch.WordTrace tailWord_1153956 prefixEnd_1153956 592534082139792375543059 := by
  unfold tailWord_1153956
  simp only [CollatzResearch.WordTrace]
  refine ⟨21044116503710983419784861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28058822004947977893046481 21044116503710983419784861)
  ·
    refine ⟨7891543688891618782419323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21044116503710983419784861 7891543688891618782419323)
    ·
      refine ⟨11837315533337428173628985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7891543688891618782419323 11837315533337428173628985)
      ·
        refine ⟨8877986650003071130221739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11837315533337428173628985 8877986650003071130221739)
        ·
          refine ⟨13316979975004606695332609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8877986650003071130221739 13316979975004606695332609)
          ·
            refine ⟨9987734981253455021499457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13316979975004606695332609 9987734981253455021499457)
            ·
              refine ⟨7490801235940091266124593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9987734981253455021499457 7490801235940091266124593)
              ·
                refine ⟨5618100926955068449593445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7490801235940091266124593 5618100926955068449593445)
                ·
                  refine ⟨1053393923804075334298771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5618100926955068449593445 1053393923804075334298771)
                  ·
                    refine ⟨1580090885706113001448157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1053393923804075334298771 1580090885706113001448157)
                    ·
                      refine ⟨592534082139792375543059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1580090885706113001448157 592534082139792375543059)
                      ·
                        rfl

theorem cell23_1153956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_1153956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153956 prefixEnd_1153956 := by exact prefixLift 1153956
  have htrace : WordTrace (prefixWord ++ tailWord_1153956) baseStart_1153956 baseEnd_1153956 := by
    simpa [prefixWord, tailWord_1153956, baseEnd_1153956] using wordTrace_append hprefix tailTrace_1153956
  have hstable : (prefixWord ++ tailWord_1153956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153956).length < 2 ^ (prefixWord ++ tailWord_1153956).sum := by decide
  have hdescent : baseEnd_1153956 < baseStart_1153956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1153997 : List Nat := [1, 6, 3, 1, 1, 2, 2, 7]
def baseStart_1153997 : Nat := 118140960795 + 1153997 * 2 ^ 59
def prefixEnd_1153997 : Nat := 4983230072969 + 3 ^ 40 * 1153997 * 2
def baseEnd_1153997 : Nat := 21946486475800989449273

theorem tailTrace_1153997 : CollatzResearch.WordTrace tailWord_1153997 prefixEnd_1153997 21946486475800989449273 := by
  unfold tailWord_1153997
  simp only [CollatzResearch.WordTrace]
  refine ⟨42089728400273430841812245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28059818933515620561208163 42089728400273430841812245)
  ·
    refine ⟨1972956018762817070709949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42089728400273430841812245 1972956018762817070709949)
    ·
      refine ⟨739858507036056401516231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1972956018762817070709949 739858507036056401516231)
      ·
        refine ⟨1109787760554084602274347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739858507036056401516231 1109787760554084602274347)
        ·
          refine ⟨1664681640831126903411521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109787760554084602274347 1664681640831126903411521)
          ·
            refine ⟨1248511230623345177558641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664681640831126903411521 1248511230623345177558641)
            ·
              refine ⟨936383422967508883168981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248511230623345177558641 936383422967508883168981)
              ·
                refine ⟨21946486475800989449273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 936383422967508883168981 21946486475800989449273)
                ·
                  rfl

theorem cell23_1153997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 7].length) (baseStart_1153997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1153997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1153997 prefixEnd_1153997 := by exact prefixLift 1153997
  have htrace : WordTrace (prefixWord ++ tailWord_1153997) baseStart_1153997 baseEnd_1153997 := by
    simpa [prefixWord, tailWord_1153997, baseEnd_1153997] using wordTrace_append hprefix tailTrace_1153997
  have hstable : (prefixWord ++ tailWord_1153997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1153997).length < 2 ^ (prefixWord ++ tailWord_1153997).sum := by decide
  have hdescent : baseEnd_1153997 < baseStart_1153997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1153997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154087 : List Nat := [1, 1, 7, 1, 1, 3, 2, 2, 5]
def baseStart_1154087 : Nat := 118140960795 + 1154087 * 2 ^ 59
def prefixEnd_1154087 : Nat := 4983230072969 + 3 ^ 40 * 1154087 * 2
def baseEnd_1154087 : Nat := 65844594233947929222773

theorem tailTrace_1154087 : CollatzResearch.WordTrace tailWord_1154087 prefixEnd_1154087 65844594233947929222773 := by
  unfold tailWord_1154087
  simp only [CollatzResearch.WordTrace]
  refine ⟨42093010969947376212588515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28062007313298250808392343 42093010969947376212588515)
  ·
    refine ⟨63139516454921064318882773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42093010969947376212588515 63139516454921064318882773)
    ·
      refine ⟨1479832416912212444973815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 63139516454921064318882773 1479832416912212444973815)
      ·
        refine ⟨2219748625368318667460723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1479832416912212444973815 2219748625368318667460723)
        ·
          refine ⟨3329622938052478001191085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219748625368318667460723 3329622938052478001191085)
          ·
            refine ⟨1248608601769679250446657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3329622938052478001191085 1248608601769679250446657)
            ·
              refine ⟨936456451327259437834993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248608601769679250446657 936456451327259437834993)
              ·
                refine ⟨702342338495444578376245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 936456451327259437834993 702342338495444578376245)
                ·
                  refine ⟨65844594233947929222773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 702342338495444578376245 65844594233947929222773)
                  ·
                    rfl

theorem cell23_1154087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 5].length) (baseStart_1154087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154087 prefixEnd_1154087 := by exact prefixLift 1154087
  have htrace : WordTrace (prefixWord ++ tailWord_1154087) baseStart_1154087 baseEnd_1154087 := by
    simpa [prefixWord, tailWord_1154087, baseEnd_1154087] using wordTrace_append hprefix tailTrace_1154087
  have hstable : (prefixWord ++ tailWord_1154087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154087).length < 2 ^ (prefixWord ++ tailWord_1154087).sum := by decide
  have hdescent : baseEnd_1154087 < baseStart_1154087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154096 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 3, 4]
def baseStart_1154096 : Nat := 118140960795 + 1154096 * 2 ^ 59
def prefixEnd_1154096 : Nat := 4983230072969 + 3 ^ 40 * 1154096 * 2
def baseEnd_1154096 : Nat := 197535323143807275930805

theorem tailTrace_1154096 : CollatzResearch.WordTrace tailWord_1154096 prefixEnd_1154096 197535323143807275930805 := by
  unfold tailWord_1154096
  simp only [CollatzResearch.WordTrace]
  refine ⟨21046669613457385374833071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28062226151276513833110761 21046669613457385374833071)
  ·
    refine ⟨31570004420186078062249607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21046669613457385374833071 31570004420186078062249607)
    ·
      refine ⟨47355006630279117093374411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31570004420186078062249607 47355006630279117093374411)
      ·
        refine ⟨71032509945418675640061617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47355006630279117093374411 71032509945418675640061617)
        ·
          refine ⟨53274382459064006730046213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71032509945418675640061617 53274382459064006730046213)
          ·
            refine ⟨9988946711074501261883665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53274382459064006730046213 9988946711074501261883665)
            ·
              refine ⟨7491710033305875946412749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9988946711074501261883665 7491710033305875946412749)
              ·
                refine ⟨2809391262489703479904781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7491710033305875946412749 2809391262489703479904781)
                ·
                  refine ⟨1053521723433638804964293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2809391262489703479904781 1053521723433638804964293)
                  ·
                    refine ⟨197535323143807275930805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1053521723433638804964293 197535323143807275930805)
                    ·
                      rfl

theorem cell23_1154096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3, 4].length) (baseStart_1154096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154096 prefixEnd_1154096 := by exact prefixLift 1154096
  have htrace : WordTrace (prefixWord ++ tailWord_1154096) baseStart_1154096 baseEnd_1154096 := by
    simpa [prefixWord, tailWord_1154096, baseEnd_1154096] using wordTrace_append hprefix tailTrace_1154096
  have hstable : (prefixWord ++ tailWord_1154096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154096).length < 2 ^ (prefixWord ++ tailWord_1154096).sum := by decide
  have hdescent : baseEnd_1154096 < baseStart_1154096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154099 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 4]
def baseStart_1154099 : Nat := 118140960795 + 1154099 * 2 ^ 59
def prefixEnd_1154099 : Nat := 4983230072969 + 3 ^ 40 * 1154099 * 2
def baseEnd_1154099 : Nat := 592607509873385316054901

theorem tailTrace_1154099 : CollatzResearch.WordTrace tailWord_1154099 prefixEnd_1154099 592607509873385316054901 := by
  unfold tailWord_1154099
  simp only [CollatzResearch.WordTrace]
  refine ⟨42093448645903902262025351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28062299097269268174683567 42093448645903902262025351)
  ·
    refine ⟨63140172968855853393038027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42093448645903902262025351 63140172968855853393038027)
    ·
      refine ⟨94710259453283780089557041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63140172968855853393038027 94710259453283780089557041)
      ·
        refine ⟨71032694589962835067167781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94710259453283780089557041 71032694589962835067167781)
        ·
          refine ⟨13318630235618031575093959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71032694589962835067167781 13318630235618031575093959)
          ·
            refine ⟨19977945353427047362640939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13318630235618031575093959 19977945353427047362640939)
            ·
              refine ⟨29966918030140571043961409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19977945353427047362640939 29966918030140571043961409)
              ·
                refine ⟨22475188522605428282971057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29966918030140571043961409 22475188522605428282971057)
                ·
                  refine ⟨16856391391954071212228293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22475188522605428282971057 16856391391954071212228293)
                  ·
                    refine ⟨3160573385991388352292805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16856391391954071212228293 3160573385991388352292805)
                    ·
                      refine ⟨592607509873385316054901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3160573385991388352292805 592607509873385316054901)
                      ·
                        rfl

theorem cell23_1154099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_1154099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154099 prefixEnd_1154099 := by exact prefixLift 1154099
  have htrace : WordTrace (prefixWord ++ tailWord_1154099) baseStart_1154099 baseEnd_1154099 := by
    simpa [prefixWord, tailWord_1154099, baseEnd_1154099] using wordTrace_append hprefix tailTrace_1154099
  have hstable : (prefixWord ++ tailWord_1154099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154099).length < 2 ^ (prefixWord ++ tailWord_1154099).sum := by decide
  have hdescent : baseEnd_1154099 < baseStart_1154099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154106 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3]
def baseStart_1154106 : Nat := 118140960795 + 1154106 * 2 ^ 59
def prefixEnd_1154106 : Nat := 4983230072969 + 3 ^ 40 * 1154106 * 2
def baseEnd_1154106 : Nat := 592611104237966788667369

theorem tailTrace_1154106 : CollatzResearch.WordTrace tailWord_1154106 prefixEnd_1154106 592611104237966788667369 := by
  unfold tailWord_1154106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10523425989219635614382543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28062469304585694971686781 10523425989219635614382543)
  ·
    refine ⟨15785138983829453421573815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10523425989219635614382543 15785138983829453421573815)
    ·
      refine ⟨23677708475744180132360723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15785138983829453421573815 23677708475744180132360723)
      ·
        refine ⟨35516562713616270198541085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23677708475744180132360723 35516562713616270198541085)
        ·
          refine ⟨13318711017606101324452907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35516562713616270198541085 13318711017606101324452907)
          ·
            refine ⟨19978066526409151986679361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13318711017606101324452907 19978066526409151986679361)
            ·
              refine ⟨14983549894806863990009521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19978066526409151986679361 14983549894806863990009521)
              ·
                refine ⟨11237662421105147992507141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14983549894806863990009521 11237662421105147992507141)
                ·
                  refine ⟨2107061703957215248595089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11237662421105147992507141 2107061703957215248595089)
                  ·
                    refine ⟨1580296277967911436446317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2107061703957215248595089 1580296277967911436446317)
                    ·
                      refine ⟨592611104237966788667369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1580296277967911436446317 592611104237966788667369)
                      ·
                        rfl

theorem cell23_1154106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_1154106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154106 prefixEnd_1154106 := by exact prefixLift 1154106
  have htrace : WordTrace (prefixWord ++ tailWord_1154106) baseStart_1154106 baseEnd_1154106 := by
    simpa [prefixWord, tailWord_1154106, baseEnd_1154106] using wordTrace_append hprefix tailTrace_1154106
  have hstable : (prefixWord ++ tailWord_1154106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154106).length < 2 ^ (prefixWord ++ tailWord_1154106).sum := by decide
  have hdescent : baseEnd_1154106 < baseStart_1154106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154130 : List Nat := [3, 2, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_1154130 : Nat := 118140960795 + 1154130 * 2 ^ 59
def prefixEnd_1154130 : Nat := 4983230072969 + 3 ^ 40 * 1154130 * 2
def baseEnd_1154130 : Nat := 197541142591224898255753

theorem tailTrace_1154130 : CollatzResearch.WordTrace tailWord_1154130 prefixEnd_1154130 197541142591224898255753 := by
  unfold tailWord_1154130
  simp only [CollatzResearch.WordTrace]
  refine ⟨10523644827197898639100961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28063052872527729704269229 10523644827197898639100961)
  ·
    refine ⟨7892733620398423979325721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10523644827197898639100961 7892733620398423979325721)
    ·
      refine ⟨5919550215298817984494291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7892733620398423979325721 5919550215298817984494291)
      ·
        refine ⟨8879325322948226976741437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5919550215298817984494291 8879325322948226976741437)
        ·
          refine ⟨3329746996105585116278039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8879325322948226976741437 3329746996105585116278039)
          ·
            refine ⟨4994620494158377674417059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3329746996105585116278039 4994620494158377674417059)
            ·
              refine ⟨7491930741237566511625589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4994620494158377674417059 7491930741237566511625589)
              ·
                refine ⟨702368506991021860464899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7491930741237566511625589 702368506991021860464899)
                ·
                  refine ⟨1053552760486532790697349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702368506991021860464899 1053552760486532790697349)
                  ·
                    refine ⟨197541142591224898255753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1053552760486532790697349 197541142591224898255753)
                    ·
                      rfl

theorem cell23_1154130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_1154130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154130 prefixEnd_1154130 := by exact prefixLift 1154130
  have htrace : WordTrace (prefixWord ++ tailWord_1154130) baseStart_1154130 baseEnd_1154130 := by
    simpa [prefixWord, tailWord_1154130, baseEnd_1154130] using wordTrace_append hprefix tailTrace_1154130
  have hstable : (prefixWord ++ tailWord_1154130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154130).length < 2 ^ (prefixWord ++ tailWord_1154130).sum := by decide
  have hdescent : baseEnd_1154130 < baseStart_1154130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154153 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 3, 1, 3]
def baseStart_1154153 : Nat := 118140960795 + 1154153 * 2 ^ 59
def prefixEnd_1154153 : Nat := 4983230072969 + 3 ^ 40 * 1154153 * 2
def baseEnd_1154153 : Nat := 592635237828728104779653

theorem tailTrace_1154153 : CollatzResearch.WordTrace tailWord_1154153 prefixEnd_1154153 592635237828728104779653 := by
  unfold tailWord_1154153
  simp only [CollatzResearch.WordTrace]
  refine ⟨42095418187708269484491113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28063612125138846322994075 42095418187708269484491113)
  ·
    refine ⟨31571563640781202113368335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42095418187708269484491113 31571563640781202113368335)
    ·
      refine ⟨47357345461171803170052503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31571563640781202113368335 47357345461171803170052503)
      ·
        refine ⟨71036018191757704755078755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47357345461171803170052503 71036018191757704755078755)
        ·
          refine ⟨106554027287636557132618133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71036018191757704755078755 106554027287636557132618133)
          ·
            refine ⟨4994720029107963615591475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106554027287636557132618133 4994720029107963615591475)
            ·
              refine ⟨7492080043661945423387213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4994720029107963615591475 7492080043661945423387213)
              ·
                refine ⟨2809530016373229533770205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7492080043661945423387213 2809530016373229533770205)
                ·
                  refine ⟨1053573756139961075163827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2809530016373229533770205 1053573756139961075163827)
                  ·
                    refine ⟨1580360634209941612745741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1053573756139961075163827 1580360634209941612745741)
                    ·
                      refine ⟨592635237828728104779653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1580360634209941612745741 592635237828728104779653)
                      ·
                        rfl

theorem cell23_1154153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 1, 3].length) (baseStart_1154153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154153 prefixEnd_1154153 := by exact prefixLift 1154153
  have htrace : WordTrace (prefixWord ++ tailWord_1154153) baseStart_1154153 baseEnd_1154153 := by
    simpa [prefixWord, tailWord_1154153, baseEnd_1154153] using wordTrace_append hprefix tailTrace_1154153
  have hstable : (prefixWord ++ tailWord_1154153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154153).length < 2 ^ (prefixWord ++ tailWord_1154153).sum := by decide
  have hdescent : baseEnd_1154153 < baseStart_1154153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154173 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_1154173 : Nat := 118140960795 + 1154173 * 2 ^ 59
def prefixEnd_1154173 : Nat := 4983230072969 + 3 ^ 40 * 1154173 * 2
def baseEnd_1154173 : Nat := 197548502480606008843187

theorem tailTrace_1154173 : CollatzResearch.WordTrace tailWord_1154173 prefixEnd_1154173 197548502480606008843187 := by
  unfold tailWord_1154173
  simp only [CollatzResearch.WordTrace]
  refine ⟨42096147647635812900219173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28064098431757208600146115 42096147647635812900219173)
  ·
    refine ⟨7893027683931714918791095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42096147647635812900219173 7893027683931714918791095)
    ·
      refine ⟨11839541525897572378186643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7893027683931714918791095 11839541525897572378186643)
      ·
        refine ⟨17759312288846358567279965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11839541525897572378186643 17759312288846358567279965)
        ·
          refine ⟨6659742108317384462729987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17759312288846358567279965 6659742108317384462729987)
          ·
            refine ⟨9989613162476076694094981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6659742108317384462729987 9989613162476076694094981)
            ·
              refine ⟨1873052467964264380142809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9989613162476076694094981 1873052467964264380142809)
              ·
                refine ⟨1404789350973198285107107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1873052467964264380142809 1404789350973198285107107)
                ·
                  refine ⟨2107184026459797427660661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404789350973198285107107 2107184026459797427660661)
                  ·
                    refine ⟨197548502480606008843187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2107184026459797427660661 197548502480606008843187)
                    ·
                      rfl

theorem cell23_1154173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_1154173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154173 prefixEnd_1154173 := by exact prefixLift 1154173
  have htrace : WordTrace (prefixWord ++ tailWord_1154173) baseStart_1154173 baseEnd_1154173 := by
    simpa [prefixWord, tailWord_1154173, baseEnd_1154173] using wordTrace_append hprefix tailTrace_1154173
  have hstable : (prefixWord ++ tailWord_1154173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154173).length < 2 ^ (prefixWord ++ tailWord_1154173).sum := by decide
  have hdescent : baseEnd_1154173 < baseStart_1154173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154176 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 4]
def baseStart_1154176 : Nat := 118140960795 + 1154176 * 2 ^ 59
def prefixEnd_1154176 : Nat := 4983230072969 + 3 ^ 40 * 1154176 * 2
def baseEnd_1154176 : Nat := 592647047883781514792047

theorem tailTrace_1154176 : CollatzResearch.WordTrace tailWord_1154176 prefixEnd_1154176 592647047883781514792047 := by
  unfold tailWord_1154176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21048128533312472206289191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28064171377749962941718921 21048128533312472206289191)
  ·
    refine ⟨31572192799968708309433787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21048128533312472206289191 31572192799968708309433787)
    ·
      refine ⟨47358289199953062464150681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31572192799968708309433787 47358289199953062464150681)
      ·
        refine ⟨35518716899964796848113011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47358289199953062464150681 35518716899964796848113011)
        ·
          refine ⟨53278075349947195272169517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35518716899964796848113011 53278075349947195272169517)
          ·
            refine ⟨19979278256230198227063569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53278075349947195272169517 19979278256230198227063569)
            ·
              refine ⟨14984458692172648670297677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19979278256230198227063569 14984458692172648670297677)
              ·
                refine ⟨5619172009564743251361629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14984458692172648670297677 5619172009564743251361629)
                ·
                  refine ⟨2107189503586778719260611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5619172009564743251361629 2107189503586778719260611)
                  ·
                    refine ⟨3160784255380168078890917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2107189503586778719260611 3160784255380168078890917)
                    ·
                      refine ⟨592647047883781514792047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3160784255380168078890917 592647047883781514792047)
                      ·
                        rfl

theorem cell23_1154176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_1154176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154176 prefixEnd_1154176 := by exact prefixLift 1154176
  have htrace : WordTrace (prefixWord ++ tailWord_1154176) baseStart_1154176 baseEnd_1154176 := by
    simpa [prefixWord, tailWord_1154176, baseEnd_1154176] using wordTrace_append hprefix tailTrace_1154176
  have hstable : (prefixWord ++ tailWord_1154176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154176).length < 2 ^ (prefixWord ++ tailWord_1154176).sum := by decide
  have hdescent : baseEnd_1154176 < baseStart_1154176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154186 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_1154186 : Nat := 118140960795 + 1154186 * 2 ^ 59
def prefixEnd_1154186 : Nat := 4983230072969 + 3 ^ 40 * 1154186 * 2
def baseEnd_1154186 : Nat := 197550727563442158555667

theorem tailTrace_1154186 : CollatzResearch.WordTrace tailWord_1154186 prefixEnd_1154186 197550727563442158555667 := by
  unfold tailWord_1154186
  simp only [CollatzResearch.WordTrace]
  refine ⟨10524155449147179030110603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28064414531059144080294941 10524155449147179030110603)
  ·
    refine ⟨15786233173720768545165905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10524155449147179030110603 15786233173720768545165905)
    ·
      refine ⟨11839674880290576408874429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15786233173720768545165905 11839674880290576408874429)
      ·
        refine ⟨4439878080108966153327911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11839674880290576408874429 4439878080108966153327911)
        ·
          refine ⟨6659817120163449229991867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4439878080108966153327911 6659817120163449229991867)
          ·
            refine ⟨9989725680245173844987801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6659817120163449229991867 9989725680245173844987801)
            ·
              refine ⟨7492294260183880383740851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9989725680245173844987801 7492294260183880383740851)
              ·
                refine ⟨11238441390275820575611277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7492294260183880383740851 11238441390275820575611277)
                ·
                  refine ⟨4214415521353432715854229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11238441390275820575611277 4214415521353432715854229)
                  ·
                    refine ⟨197550727563442158555667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4214415521353432715854229 197550727563442158555667)
                    ·
                      rfl

theorem cell23_1154186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_1154186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154186 prefixEnd_1154186 := by exact prefixLift 1154186
  have htrace : WordTrace (prefixWord ++ tailWord_1154186) baseStart_1154186 baseEnd_1154186 := by
    simpa [prefixWord, tailWord_1154186, baseEnd_1154186] using wordTrace_append hprefix tailTrace_1154186
  have hstable : (prefixWord ++ tailWord_1154186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154186).length < 2 ^ (prefixWord ++ tailWord_1154186).sum := by decide
  have hdescent : baseEnd_1154186 < baseStart_1154186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154204 : List Nat := [2, 2, 3, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_1154204 : Nat := 118140960795 + 1154204 * 2 ^ 59
def prefixEnd_1154204 : Nat := 4983230072969 + 3 ^ 40 * 1154204 * 2
def baseEnd_1154204 : Nat := 592661425342107405241919

theorem tailTrace_1154204 : CollatzResearch.WordTrace tailWord_1154204 prefixEnd_1154204 592661425342107405241919 := by
  unfold tailWord_1154204
  simp only [CollatzResearch.WordTrace]
  refine ⟨21048639155261752597298833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28064852207015670129731777 21048639155261752597298833)
  ·
    refine ⟨15786479366446314447974125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21048639155261752597298833 15786479366446314447974125)
    ·
      refine ⟨5919929762417367917990297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15786479366446314447974125 5919929762417367917990297)
      ·
        refine ⟨4439947321813025938492723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5919929762417367917990297 4439947321813025938492723)
        ·
          refine ⟨6659920982719538907739085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4439947321813025938492723 6659920982719538907739085)
          ·
            refine ⟨2497470368519827090402157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6659920982719538907739085 2497470368519827090402157)
            ·
              refine ⟨936551388194935158900809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2497470368519827090402157 936551388194935158900809)
              ·
                refine ⟨702413541146201369175607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 936551388194935158900809 702413541146201369175607)
                ·
                  refine ⟨1053620311719302053763411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702413541146201369175607 1053620311719302053763411)
                  ·
                    refine ⟨1580430467578953080645117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1053620311719302053763411 1580430467578953080645117)
                    ·
                      refine ⟨592661425342107405241919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1580430467578953080645117 592661425342107405241919)
                      ·
                        rfl

theorem cell23_1154204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_1154204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154204 prefixEnd_1154204 := by exact prefixLift 1154204
  have htrace : WordTrace (prefixWord ++ tailWord_1154204) baseStart_1154204 baseEnd_1154204 := by
    simpa [prefixWord, tailWord_1154204, baseEnd_1154204] using wordTrace_append hprefix tailTrace_1154204
  have hstable : (prefixWord ++ tailWord_1154204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154204).length < 2 ^ (prefixWord ++ tailWord_1154204).sum := by decide
  have hdescent : baseEnd_1154204 < baseStart_1154204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154243 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 4, 1, 3]
def baseStart_1154243 : Nat := 118140960795 + 1154243 * 2 ^ 59
def prefixEnd_1154243 : Nat := 4983230072969 + 3 ^ 40 * 1154243 * 2
def baseEnd_1154243 : Nat := 592681451087632752654239

theorem tailTrace_1154243 : CollatzResearch.WordTrace tailWord_1154243 prefixEnd_1154243 592681451087632752654239 := by
  unfold tailWord_1154243
  simp only [CollatzResearch.WordTrace]
  refine ⟨42098700757382214855267383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28065800504921476570178255 42098700757382214855267383)
  ·
    refine ⟨63148051136073322282901075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42098700757382214855267383 63148051136073322282901075)
    ·
      refine ⟨94722076704109983424351613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63148051136073322282901075 94722076704109983424351613)
      ·
        refine ⟨35520778764041243784131855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94722076704109983424351613 35520778764041243784131855)
        ·
          refine ⟨53281168146061865676197783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35520778764041243784131855 53281168146061865676197783)
          ·
            refine ⟨79921752219092798514296675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53281168146061865676197783 79921752219092798514296675)
            ·
              refine ⟨119882628328639197771445013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79921752219092798514296675 119882628328639197771445013)
              ·
                refine ⟨5619498202904962395536485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119882628328639197771445013 5619498202904962395536485)
                ·
                  refine ⟨1053655913044680449163091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5619498202904962395536485 1053655913044680449163091)
                  ·
                    refine ⟨1580483869567020673744637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1053655913044680449163091 1580483869567020673744637)
                    ·
                      refine ⟨592681451087632752654239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1580483869567020673744637 592681451087632752654239)
                      ·
                        rfl

theorem cell23_1154243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_1154243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154243 prefixEnd_1154243 := by exact prefixLift 1154243
  have htrace : WordTrace (prefixWord ++ tailWord_1154243) baseStart_1154243 baseEnd_1154243 := by
    simpa [prefixWord, tailWord_1154243, baseEnd_1154243] using wordTrace_append hprefix tailTrace_1154243
  have hstable : (prefixWord ++ tailWord_1154243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154243).length < 2 ^ (prefixWord ++ tailWord_1154243).sum := by decide
  have hdescent : baseEnd_1154243 < baseStart_1154243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154261 : List Nat := [1, 3, 2, 4, 1, 1, 4, 2, 1, 2, 2]
def baseStart_1154261 : Nat := 118140960795 + 1154261 * 2 ^ 59
def prefixEnd_1154261 : Nat := 4983230072969 + 3 ^ 40 * 1154261 * 2
def baseEnd_1154261 : Nat := 592690693739413682229157

theorem tailTrace_1154261 : CollatzResearch.WordTrace tailWord_1154261 prefixEnd_1154261 592690693739413682229157 := by
  unfold tailWord_1154261
  simp only [CollatzResearch.WordTrace]
  refine ⟨42099357271317003929422637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28066238180878002619615091 42099357271317003929422637)
  ·
    refine ⟨15787258976743876473533489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42099357271317003929422637 15787258976743876473533489)
    ·
      refine ⟨11840444232557907355150117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15787258976743876473533489 11840444232557907355150117)
      ·
        refine ⟨2220083293604607629090647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11840444232557907355150117 2220083293604607629090647)
        ·
          refine ⟨3330124940406911443635971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2220083293604607629090647 3330124940406911443635971)
          ·
            refine ⟨4995187410610367165453957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3330124940406911443635971 4995187410610367165453957)
            ·
              refine ⟨936597639489443843522617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4995187410610367165453957 936597639489443843522617)
              ·
                refine ⟨702448229617082882641963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 936597639489443843522617 702448229617082882641963)
                ·
                  refine ⟨1053672344425624323962945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702448229617082882641963 1053672344425624323962945)
                  ·
                    refine ⟨790254258319218242972209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1053672344425624323962945 790254258319218242972209)
                    ·
                      refine ⟨592690693739413682229157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 790254258319218242972209 592690693739413682229157)
                      ·
                        rfl

theorem cell23_1154261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_1154261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154261 prefixEnd_1154261 := by exact prefixLift 1154261
  have htrace : WordTrace (prefixWord ++ tailWord_1154261) baseStart_1154261 baseEnd_1154261 := by
    simpa [prefixWord, tailWord_1154261, baseEnd_1154261] using wordTrace_append hprefix tailTrace_1154261
  have hstable : (prefixWord ++ tailWord_1154261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154261).length < 2 ^ (prefixWord ++ tailWord_1154261).sum := by decide
  have hdescent : baseEnd_1154261 < baseStart_1154261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154276 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_1154276 : Nat := 118140960795 + 1154276 * 2 ^ 59
def prefixEnd_1154276 : Nat := 4983230072969 + 3 ^ 40 * 1154276 * 2
def baseEnd_1154276 : Nat := 197566131983077041180529

theorem tailTrace_1154276 : CollatzResearch.WordTrace tailWord_1154276 prefixEnd_1154276 197566131983077041180529 := by
  unfold tailWord_1154276
  simp only [CollatzResearch.WordTrace]
  refine ⟨21049952183131330745609341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28066602910841774327479121 21049952183131330745609341)
  ·
    refine ⟨7893732068674249029603503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21049952183131330745609341 7893732068674249029603503)
    ·
      refine ⟨11840598103011373544405255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7893732068674249029603503 11840598103011373544405255)
      ·
        refine ⟨17760897154517060316607883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11840598103011373544405255 17760897154517060316607883)
        ·
          refine ⟨26641345731775590474911825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17760897154517060316607883 26641345731775590474911825)
          ·
            refine ⟨19981009298831692856183869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26641345731775590474911825 19981009298831692856183869)
            ·
              refine ⟨7492878487061884821068951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19981009298831692856183869 7492878487061884821068951)
              ·
                refine ⟨11239317730592827231603427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7492878487061884821068951 11239317730592827231603427)
                ·
                  refine ⟨16858976595889240847405141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11239317730592827231603427 16858976595889240847405141)
                  ·
                    refine ⟨197566131983077041180529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16858976595889240847405141 197566131983077041180529)
                    ·
                      rfl

theorem cell23_1154276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_1154276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154276 prefixEnd_1154276 := by exact prefixLift 1154276
  have htrace : WordTrace (prefixWord ++ tailWord_1154276) baseStart_1154276 baseEnd_1154276 := by
    simpa [prefixWord, tailWord_1154276, baseEnd_1154276] using wordTrace_append hprefix tailTrace_1154276
  have hstable : (prefixWord ++ tailWord_1154276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154276).length < 2 ^ (prefixWord ++ tailWord_1154276).sum := by decide
  have hdescent : baseEnd_1154276 < baseStart_1154276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154353 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 1, 7]
def baseStart_1154353 : Nat := 118140960795 + 1154353 * 2 ^ 59
def prefixEnd_1154353 : Nat := 4983230072969 + 3 ^ 40 * 1154353 * 2
def baseEnd_1154353 : Nat := 197579311319875774092911

theorem tailTrace_1154353 : CollatzResearch.WordTrace tailWord_1154353 prefixEnd_1154353 197579311319875774092911 := by
  unfold tailWord_1154353
  simp only [CollatzResearch.WordTrace]
  refine ⟨42102712786983703641771713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28068475191322469094514475 42102712786983703641771713)
  ·
    refine ⟨31577034590237777731328785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42102712786983703641771713 31577034590237777731328785)
    ·
      refine ⟨23682775942678333298496589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31577034590237777731328785 23682775942678333298496589)
      ·
        refine ⟨8881040978504374986936221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23682775942678333298496589 8881040978504374986936221)
        ·
          refine ⟨3330390366939140620101083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8881040978504374986936221 3330390366939140620101083)
          ·
            refine ⟨4995585550408710930151625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3330390366939140620101083 4995585550408710930151625)
            ·
              refine ⟨3746689162806533197613719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4995585550408710930151625 3746689162806533197613719)
              ·
                refine ⟨5620033744209799796420579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3746689162806533197613719 5620033744209799796420579)
                ·
                  refine ⟨8430050616314699694630869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5620033744209799796420579 8430050616314699694630869)
                  ·
                    refine ⟨197579311319875774092911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8430050616314699694630869 197579311319875774092911)
                    ·
                      rfl

theorem cell23_1154353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_1154353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154353 prefixEnd_1154353 := by exact prefixLift 1154353
  have htrace : WordTrace (prefixWord ++ tailWord_1154353) baseStart_1154353 baseEnd_1154353 := by
    simpa [prefixWord, tailWord_1154353, baseEnd_1154353] using wordTrace_append hprefix tailTrace_1154353
  have hstable : (prefixWord ++ tailWord_1154353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154353).length < 2 ^ (prefixWord ++ tailWord_1154353).sum := by decide
  have hdescent : baseEnd_1154353 < baseStart_1154353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154357 : List Nat := [1, 3, 3, 1, 2, 4, 1, 3, 5]
def baseStart_1154357 : Nat := 118140960795 + 1154357 * 2 ^ 59
def prefixEnd_1154357 : Nat := 4983230072969 + 3 ^ 40 * 1154357 * 2
def baseEnd_1154357 : Nat := 65859998653582811847635

theorem tailTrace_1154357 : CollatzResearch.WordTrace tailWord_1154357 prefixEnd_1154357 65859998653582811847635 := by
  unfold tailWord_1154357
  simp only [CollatzResearch.WordTrace]
  refine ⟨42102858678969212324917325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28068572452646141549944883 42102858678969212324917325)
  ·
    refine ⟨15788572004613454621843997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42102858678969212324917325 15788572004613454621843997)
    ·
      refine ⟨5920714501730045483191499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15788572004613454621843997 5920714501730045483191499)
      ·
        refine ⟨8881071752595068224787249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5920714501730045483191499 8881071752595068224787249)
        ·
          refine ⟨6660803814446301168590437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8881071752595068224787249 6660803814446301168590437)
          ·
            refine ⟨1248900715208681469110707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6660803814446301168590437 1248900715208681469110707)
            ·
              refine ⟨1873351072813022203666061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248900715208681469110707 1873351072813022203666061)
              ·
                refine ⟨702506652304883326374773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1873351072813022203666061 702506652304883326374773)
                ·
                  refine ⟨65859998653582811847635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 702506652304883326374773 65859998653582811847635)
                  ·
                    rfl

theorem cell23_1154357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_1154357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154357 prefixEnd_1154357 := by exact prefixLift 1154357
  have htrace : WordTrace (prefixWord ++ tailWord_1154357) baseStart_1154357 baseEnd_1154357 := by
    simpa [prefixWord, tailWord_1154357, baseEnd_1154357] using wordTrace_append hprefix tailTrace_1154357
  have hstable : (prefixWord ++ tailWord_1154357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154357).length < 2 ^ (prefixWord ++ tailWord_1154357).sum := by decide
  have hdescent : baseEnd_1154357 < baseStart_1154357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154393 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 3, 4, 3]
def baseStart_1154393 : Nat := 118140960795 + 1154393 * 2 ^ 59
def prefixEnd_1154393 : Nat := 4983230072969 + 3 ^ 40 * 1154393 * 2
def baseEnd_1154393 : Nat := 592758473185807165778549

theorem tailTrace_1154393 : CollatzResearch.WordTrace tailWord_1154393 prefixEnd_1154393 592758473185807165778549 := by
  unfold tailWord_1154393
  simp only [CollatzResearch.WordTrace]
  refine ⟨42104171706838790473227833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28069447804559193648818555 42104171706838790473227833)
  ·
    refine ⟨31578128780129092854920875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42104171706838790473227833 31578128780129092854920875)
    ·
      refine ⟨47367193170193639282381313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31578128780129092854920875 47367193170193639282381313)
      ·
        refine ⟨35525394877645229461785985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47367193170193639282381313 35525394877645229461785985)
        ·
          refine ⟨26644046158233922096339489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35525394877645229461785985 26644046158233922096339489)
          ·
            refine ⟨19983034618675441572254617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26644046158233922096339489 19983034618675441572254617)
            ·
              refine ⟨14987275964006581179190963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19983034618675441572254617 14987275964006581179190963)
              ·
                refine ⟨22480913946009871768786445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14987275964006581179190963 22480913946009871768786445)
                ·
                  refine ⟨8430342729753701913294917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22480913946009871768786445 8430342729753701913294917)
                  ·
                    refine ⟨1580689261828819108742797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8430342729753701913294917 1580689261828819108742797)
                    ·
                      refine ⟨592758473185807165778549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1580689261828819108742797 592758473185807165778549)
                      ·
                        rfl

theorem cell23_1154393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_1154393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154393 prefixEnd_1154393 := by exact prefixLift 1154393
  have htrace : WordTrace (prefixWord ++ tailWord_1154393) baseStart_1154393 baseEnd_1154393 := by
    simpa [prefixWord, tailWord_1154393, baseEnd_1154393] using wordTrace_append hprefix tailTrace_1154393
  have hstable : (prefixWord ++ tailWord_1154393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154393).length < 2 ^ (prefixWord ++ tailWord_1154393).sum := by decide
  have hdescent : baseEnd_1154393 < baseStart_1154393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154407 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_1154407 : Nat := 118140960795 + 1154407 * 2 ^ 59
def prefixEnd_1154407 : Nat := 4983230072969 + 3 ^ 40 * 1154407 * 2
def baseEnd_1154407 : Nat := 592765661914970111003485

theorem tailTrace_1154407 : CollatzResearch.WordTrace tailWord_1154407 prefixEnd_1154407 592765661914970111003485 := by
  unfold tailWord_1154407
  simp only [CollatzResearch.WordTrace]
  refine ⟨42104682328788070864237475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28069788219192047242824983 42104682328788070864237475)
  ·
    refine ⟨63157023493182106296356213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42104682328788070864237475 63157023493182106296356213)
    ·
      refine ⟨5920970952485822465283395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63157023493182106296356213 5920970952485822465283395)
      ·
        refine ⟨8881456428728733697925093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5920970952485822465283395 8881456428728733697925093)
        ·
          refine ⟨1665273080386637568360955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8881456428728733697925093 1665273080386637568360955)
          ·
            refine ⟨2497909620579956352541433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665273080386637568360955 2497909620579956352541433)
            ·
              refine ⟨1873432215434967264406075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2497909620579956352541433 1873432215434967264406075)
              ·
                refine ⟨2810148323152450896609113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873432215434967264406075 2810148323152450896609113)
                ·
                  refine ⟨2107611242364338172456835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2810148323152450896609113 2107611242364338172456835)
                  ·
                    refine ⟨3161416863546507258685253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2107611242364338172456835 3161416863546507258685253)
                    ·
                      refine ⟨592765661914970111003485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3161416863546507258685253 592765661914970111003485)
                      ·
                        rfl

theorem cell23_1154407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_1154407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154407 prefixEnd_1154407 := by exact prefixLift 1154407
  have htrace : WordTrace (prefixWord ++ tailWord_1154407) baseStart_1154407 baseEnd_1154407 := by
    simpa [prefixWord, tailWord_1154407, baseEnd_1154407] using wordTrace_append hprefix tailTrace_1154407
  have hstable : (prefixWord ++ tailWord_1154407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154407).length < 2 ^ (prefixWord ++ tailWord_1154407).sum := by decide
  have hdescent : baseEnd_1154407 < baseStart_1154407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154443 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 5, 5]
def baseStart_1154443 : Nat := 118140960795 + 1154443 * 2 ^ 59
def prefixEnd_1154443 : Nat := 4983230072969 + 3 ^ 40 * 1154443 * 2
def baseEnd_1154443 : Nat := 197594715739510656717773

theorem tailTrace_1154443 : CollatzResearch.WordTrace tailWord_1154443 prefixEnd_1154443 197594715739510656717773 := by
  unfold tailWord_1154443
  simp only [CollatzResearch.WordTrace]
  refine ⟨42105995356657649012547983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28070663571105099341698655 42105995356657649012547983)
  ·
    refine ⟨63158993034986473518821975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42105995356657649012547983 63158993034986473518821975)
    ·
      refine ⟨94738489552479710278232963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63158993034986473518821975 94738489552479710278232963)
      ·
        refine ⟨142107734328719565417349445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94738489552479710278232963 142107734328719565417349445)
        ·
          refine ⟨26645200186634918515753021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142107734328719565417349445 26645200186634918515753021)
          ·
            refine ⟨9991950069988094443407383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26645200186634918515753021 9991950069988094443407383)
            ·
              refine ⟨14987925104982141665111075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9991950069988094443407383 14987925104982141665111075)
              ·
                refine ⟨22481887657473212497666613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14987925104982141665111075 22481887657473212497666613)
                ·
                  refine ⟨2107676967888113671656245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22481887657473212497666613 2107676967888113671656245)
                  ·
                    refine ⟨197594715739510656717773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2107676967888113671656245 197594715739510656717773)
                    ·
                      rfl

theorem cell23_1154443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 5].length) (baseStart_1154443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154443 prefixEnd_1154443 := by exact prefixLift 1154443
  have htrace : WordTrace (prefixWord ++ tailWord_1154443) baseStart_1154443 baseEnd_1154443 := by
    simpa [prefixWord, tailWord_1154443, baseEnd_1154443] using wordTrace_append hprefix tailTrace_1154443
  have hstable : (prefixWord ++ tailWord_1154443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154443).length < 2 ^ (prefixWord ++ tailWord_1154443).sum := by decide
  have hdescent : baseEnd_1154443 < baseStart_1154443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154457 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 3, 1, 3]
def baseStart_1154457 : Nat := 118140960795 + 1154457 * 2 ^ 59
def prefixEnd_1154457 : Nat := 4983230072969 + 3 ^ 40 * 1154457 * 2
def baseEnd_1154457 : Nat := 592791335947694915378255

theorem tailTrace_1154457 : CollatzResearch.WordTrace tailWord_1154457 prefixEnd_1154457 592791335947694915378255 := by
  unfold tailWord_1154457
  simp only [CollatzResearch.WordTrace]
  refine ⟨42106505978606929403557625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28071003985737952935705083 42106505978606929403557625)
  ·
    refine ⟨31579879483955197052668219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42106505978606929403557625 31579879483955197052668219)
    ·
      refine ⟨47369819225932795579002329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31579879483955197052668219 47369819225932795579002329)
      ·
        refine ⟨35527364419449596684251747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47369819225932795579002329 35527364419449596684251747)
        ·
          refine ⟨53291046629174395026377621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35527364419449596684251747 53291046629174395026377621)
          ·
            refine ⟨2498017810742549766861451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53291046629174395026377621 2498017810742549766861451)
            ·
              refine ⟨3747026716113824650292177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2498017810742549766861451 3747026716113824650292177)
              ·
                refine ⟨2810270037085368487719133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3747026716113824650292177 2810270037085368487719133)
                ·
                  refine ⟨1053851263907013182894675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2810270037085368487719133 1053851263907013182894675)
                  ·
                    refine ⟨1580776895860519774342013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1053851263907013182894675 1580776895860519774342013)
                    ·
                      refine ⟨592791335947694915378255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1580776895860519774342013 592791335947694915378255)
                      ·
                        rfl

theorem cell23_1154457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_1154457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154457 prefixEnd_1154457 := by exact prefixLift 1154457
  have htrace : WordTrace (prefixWord ++ tailWord_1154457) baseStart_1154457 baseEnd_1154457 := by
    simpa [prefixWord, tailWord_1154457, baseEnd_1154457] using wordTrace_append hprefix tailTrace_1154457
  have hstable : (prefixWord ++ tailWord_1154457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154457).length < 2 ^ (prefixWord ++ tailWord_1154457).sum := by decide
  have hdescent : baseEnd_1154457 < baseStart_1154457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154483 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 5]
def baseStart_1154483 : Nat := 118140960795 + 1154483 * 2 ^ 59
def prefixEnd_1154483 : Nat := 4983230072969 + 3 ^ 40 * 1154483 * 2
def baseEnd_1154483 : Nat := 592804686444711813653135

theorem tailTrace_1154483 : CollatzResearch.WordTrace tailWord_1154483 prefixEnd_1154483 592804686444711813653135 := by
  unfold tailWord_1154483
  simp only [CollatzResearch.WordTrace]
  refine ⟨42107454276512735844004103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28071636184341823896002735 42107454276512735844004103)
  ·
    refine ⟨63161181414769103766006155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42107454276512735844004103 63161181414769103766006155)
    ·
      refine ⟨94741772122153655649009233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63161181414769103766006155 94741772122153655649009233)
      ·
        refine ⟨71056329091615241736756925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94741772122153655649009233 71056329091615241736756925)
        ·
          refine ⟨26646123409355715651283847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71056329091615241736756925 26646123409355715651283847)
          ·
            refine ⟨39969185114033573476925771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26646123409355715651283847 39969185114033573476925771)
            ·
              refine ⟨59953777671050360215388657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39969185114033573476925771 59953777671050360215388657)
              ·
                refine ⟨44965333253287770161541493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59953777671050360215388657 44965333253287770161541493)
                ·
                  refine ⟨4215499992495728452644515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44965333253287770161541493 4215499992495728452644515)
                  ·
                    refine ⟨6323249988743592678966773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4215499992495728452644515 6323249988743592678966773)
                    ·
                      refine ⟨592804686444711813653135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6323249988743592678966773 592804686444711813653135)
                      ·
                        rfl

theorem cell23_1154483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_1154483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154483 prefixEnd_1154483 := by exact prefixLift 1154483
  have htrace : WordTrace (prefixWord ++ tailWord_1154483) baseStart_1154483 baseEnd_1154483 := by
    simpa [prefixWord, tailWord_1154483, baseEnd_1154483] using wordTrace_append hprefix tailTrace_1154483
  have hstable : (prefixWord ++ tailWord_1154483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154483).length < 2 ^ (prefixWord ++ tailWord_1154483).sum := by decide
  have hdescent : baseEnd_1154483 < baseStart_1154483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154503 : List Nat := [1, 1, 4, 1, 1, 3, 2, 10]
def baseStart_1154503 : Nat := 118140960795 + 1154503 * 2 ^ 59
def prefixEnd_1154503 : Nat := 4983230072969 + 3 ^ 40 * 1154503 * 2
def baseEnd_1154503 : Nat := 21956109483622286496409

theorem tailTrace_1154503 : CollatzResearch.WordTrace tailWord_1154503 prefixEnd_1154503 21956109483622286496409 := by
  unfold tailWord_1154503
  simp only [CollatzResearch.WordTrace]
  refine ⟨42108183736440279259732163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28072122490960186173154775 42108183736440279259732163)
  ·
    refine ⟨63162275604660418889598245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42108183736440279259732163 63162275604660418889598245)
    ·
      refine ⟨11842926675873828541799671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63162275604660418889598245 11842926675873828541799671)
      ·
        refine ⟨17764390013810742812699507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11842926675873828541799671 17764390013810742812699507)
        ·
          refine ⟨26646585020716114219049261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17764390013810742812699507 26646585020716114219049261)
          ·
            refine ⟨9992469382768542832143473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26646585020716114219049261 9992469382768542832143473)
            ·
              refine ⟨7494352037076407124107605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9992469382768542832143473 7494352037076407124107605)
              ·
                refine ⟨21956109483622286496409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7494352037076407124107605 21956109483622286496409)
                ·
                  rfl

theorem cell23_1154503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 10].length) (baseStart_1154503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154503 prefixEnd_1154503 := by exact prefixLift 1154503
  have htrace : WordTrace (prefixWord ++ tailWord_1154503) baseStart_1154503 baseEnd_1154503 := by
    simpa [prefixWord, tailWord_1154503, baseEnd_1154503] using wordTrace_append hprefix tailTrace_1154503
  have hstable : (prefixWord ++ tailWord_1154503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154503).length < 2 ^ (prefixWord ++ tailWord_1154503).sum := by decide
  have hdescent : baseEnd_1154503 < baseStart_1154503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154520 : List Nat := [2, 1, 2, 2, 2, 1, 6, 7]
def baseStart_1154520 : Nat := 118140960795 + 1154520 * 2 ^ 59
def prefixEnd_1154520 : Nat := 4983230072969 + 3 ^ 40 * 1154520 * 2
def baseEnd_1154520 : Nat := 21956432786256598847795

theorem tailTrace_1154520 : CollatzResearch.WordTrace tailWord_1154520 prefixEnd_1154520 21956432786256598847795 := by
  unfold tailWord_1154520
  simp only [CollatzResearch.WordTrace]
  refine ⟨21054401888689345581550507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28072535851585794108734009 21054401888689345581550507)
  ·
    refine ⟨31581602833034018372325761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21054401888689345581550507 31581602833034018372325761)
    ·
      refine ⟨23686202124775513779244321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31581602833034018372325761 23686202124775513779244321)
      ·
        refine ⟨17764651593581635334433241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23686202124775513779244321 17764651593581635334433241)
        ·
          refine ⟨13323488695186226500824931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17764651593581635334433241 13323488695186226500824931)
          ·
            refine ⟨19985233042779339751237397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13323488695186226500824931 19985233042779339751237397)
            ·
              refine ⟨936807798880281550839253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19985233042779339751237397 936807798880281550839253)
              ·
                refine ⟨21956432786256598847795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 936807798880281550839253 21956432786256598847795)
                ·
                  rfl

theorem cell23_1154520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 7].length) (baseStart_1154520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154520 prefixEnd_1154520 := by exact prefixLift 1154520
  have htrace : WordTrace (prefixWord ++ tailWord_1154520) baseStart_1154520 baseEnd_1154520 := by
    simpa [prefixWord, tailWord_1154520, baseEnd_1154520] using wordTrace_append hprefix tailTrace_1154520
  have hstable : (prefixWord ++ tailWord_1154520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154520).length < 2 ^ (prefixWord ++ tailWord_1154520).sum := by decide
  have hdescent : baseEnd_1154520 < baseStart_1154520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154610 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 7]
def baseStart_1154610 : Nat := 118140960795 + 1154610 * 2 ^ 59
def prefixEnd_1154610 : Nat := 4983230072969 + 3 ^ 40 * 1154610 * 2
def baseEnd_1154610 : Nat := 65874433165314757418339

theorem tailTrace_1154610 : CollatzResearch.WordTrace tailWord_1154610 prefixEnd_1154610 65874433165314757418339 := by
  unfold tailWord_1154610
  simp only [CollatzResearch.WordTrace]
  refine ⟨10528021586763159133469321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28074724231368424355918189 10528021586763159133469321)
  ·
    refine ⟨7896016190072369350101991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10528021586763159133469321 7896016190072369350101991)
    ·
      refine ⟨11844024285108554025152987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7896016190072369350101991 11844024285108554025152987)
      ·
        refine ⟨17766036427662831037729481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11844024285108554025152987 17766036427662831037729481)
        ·
          refine ⟨13324527320747123278297111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17766036427662831037729481 13324527320747123278297111)
          ·
            refine ⟨19986790981120684917445667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13324527320747123278297111 19986790981120684917445667)
            ·
              refine ⟨29980186471681027376168501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19986790981120684917445667 29980186471681027376168501)
              ·
                refine ⟨2810642481720096316515797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29980186471681027376168501 2810642481720096316515797)
                ·
                  refine ⟨65874433165314757418339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2810642481720096316515797 65874433165314757418339)
                  ·
                    rfl

theorem cell23_1154610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_1154610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154610 prefixEnd_1154610 := by exact prefixLift 1154610
  have htrace : WordTrace (prefixWord ++ tailWord_1154610) baseStart_1154610 baseEnd_1154610 := by
    simpa [prefixWord, tailWord_1154610, baseEnd_1154610] using wordTrace_append hprefix tailTrace_1154610
  have hstable : (prefixWord ++ tailWord_1154610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154610).length < 2 ^ (prefixWord ++ tailWord_1154610).sum := by decide
  have hdescent : baseEnd_1154610 < baseStart_1154610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154614 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1154614 : Nat := 118140960795 + 1154614 * 2 ^ 59
def prefixEnd_1154614 : Nat := 4983230072969 + 3 ^ 40 * 1154614 * 2
def baseEnd_1154614 : Nat := 197623984136816933705011

theorem tailTrace_1154614 : CollatzResearch.WordTrace tailWord_1154614 prefixEnd_1154614 197623984136816933705011 := by
  unfold tailWord_1154614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2632014514939884076063931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28074821492692096811348597 2632014514939884076063931)
  ·
    refine ⟨3948021772409826114095897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2632014514939884076063931 3948021772409826114095897)
    ·
      refine ⟨2961016329307369585571923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3948021772409826114095897 2961016329307369585571923)
      ·
        refine ⟨4441524493961054378357885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2961016329307369585571923 4441524493961054378357885)
        ·
          refine ⟨1665571685235395391884207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4441524493961054378357885 1665571685235395391884207)
          ·
            refine ⟨2498357527853093087826311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665571685235395391884207 2498357527853093087826311)
            ·
              refine ⟨3747536291779639631739467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2498357527853093087826311 3747536291779639631739467)
              ·
                refine ⟨5621304437669459447609201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3747536291779639631739467 5621304437669459447609201)
                ·
                  refine ⟨4215978328252094585706901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5621304437669459447609201 4215978328252094585706901)
                  ·
                    refine ⟨197623984136816933705011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4215978328252094585706901 197623984136816933705011)
                    ·
                      rfl

theorem cell23_1154614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1154614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154614 prefixEnd_1154614 := by exact prefixLift 1154614
  have htrace : WordTrace (prefixWord ++ tailWord_1154614) baseStart_1154614 baseEnd_1154614 := by
    simpa [prefixWord, tailWord_1154614, baseEnd_1154614] using wordTrace_append hprefix tailTrace_1154614
  have hstable : (prefixWord ++ tailWord_1154614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154614).length < 2 ^ (prefixWord ++ tailWord_1154614).sum := by decide
  have hdescent : baseEnd_1154614 < baseStart_1154614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154617 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1154617 : Nat := 118140960795 + 1154617 * 2 ^ 59
def prefixEnd_1154617 : Nat := 4983230072969 + 3 ^ 40 * 1154617 * 2
def baseEnd_1154617 : Nat := 592873492852414289377519

theorem tailTrace_1154617 : CollatzResearch.WordTrace tailWord_1154617 prefixEnd_1154617 592873492852414289377519 := by
  unfold tailWord_1154617
  simp only [CollatzResearch.WordTrace]
  refine ⟨42112341658027276729382105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28074894438684851152921403 42112341658027276729382105)
  ·
    refine ⟨31584256243520457547036579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42112341658027276729382105 31584256243520457547036579)
    ·
      refine ⟨47376384365280686320554869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31584256243520457547036579 47376384365280686320554869)
      ·
        refine ⟨4441536034245064342552019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47376384365280686320554869 4441536034245064342552019)
        ·
          refine ⟨6662304051367596513828029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441536034245064342552019 6662304051367596513828029)
          ·
            refine ⟨2498364019262848692685511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6662304051367596513828029 2498364019262848692685511)
            ·
              refine ⟨3747546028894273039028267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2498364019262848692685511 3747546028894273039028267)
              ·
                refine ⟨5621319043341409558542401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3747546028894273039028267 5621319043341409558542401)
                ·
                  refine ⟨4215989282506057168906801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5621319043341409558542401 4215989282506057168906801)
                  ·
                    refine ⟨3161991961879542876680101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4215989282506057168906801 3161991961879542876680101)
                    ·
                      refine ⟨592873492852414289377519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3161991961879542876680101 592873492852414289377519)
                      ·
                        rfl

theorem cell23_1154617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1154617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154617 prefixEnd_1154617 := by exact prefixLift 1154617
  have htrace : WordTrace (prefixWord ++ tailWord_1154617) baseStart_1154617 baseEnd_1154617 := by
    simpa [prefixWord, tailWord_1154617, baseEnd_1154617] using wordTrace_append hprefix tailTrace_1154617
  have hstable : (prefixWord ++ tailWord_1154617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154617).length < 2 ^ (prefixWord ++ tailWord_1154617).sum := by decide
  have hdescent : baseEnd_1154617 < baseStart_1154617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154621 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 1, 4, 2]
def baseStart_1154621 : Nat := 118140960795 + 1154621 * 2 ^ 59
def prefixEnd_1154621 : Nat := 4983230072969 + 3 ^ 40 * 1154621 * 2
def baseEnd_1154621 : Nat := 592875546775032273727501

theorem tailTrace_1154621 : CollatzResearch.WordTrace tailWord_1154621 prefixEnd_1154621 592875546775032273727501 := by
  unfold tailWord_1154621
  simp only [CollatzResearch.WordTrace]
  refine ⟨42112487550012785412527717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28074991700008523608351811 42112487550012785412527717)
  ·
    refine ⟨7896091415627397264848947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42112487550012785412527717 7896091415627397264848947)
    ·
      refine ⟨11844137123441095897273421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7896091415627397264848947 11844137123441095897273421)
      ·
        refine ⟨4441551421290410961477533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11844137123441095897273421 4441551421290410961477533)
        ·
          refine ⟨1665581782983904110554075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4441551421290410961477533 1665581782983904110554075)
          ·
            refine ⟨2498372674475856165831113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665581782983904110554075 2498372674475856165831113)
            ·
              refine ⟨1873779505856892124373335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2498372674475856165831113 1873779505856892124373335)
              ·
                refine ⟨2810669258785338186560003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873779505856892124373335 2810669258785338186560003)
                ·
                  refine ⟨4216003888178007279840005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810669258785338186560003 4216003888178007279840005)
                  ·
                    refine ⟨790500729033376364970001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4216003888178007279840005 790500729033376364970001)
                    ·
                      refine ⟨592875546775032273727501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 790500729033376364970001 592875546775032273727501)
                      ·
                        rfl

theorem cell23_1154621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_1154621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154621 prefixEnd_1154621 := by exact prefixLift 1154621
  have htrace : WordTrace (prefixWord ++ tailWord_1154621) baseStart_1154621 baseEnd_1154621 := by
    simpa [prefixWord, tailWord_1154621, baseEnd_1154621] using wordTrace_append hprefix tailTrace_1154621
  have hstable : (prefixWord ++ tailWord_1154621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154621).length < 2 ^ (prefixWord ++ tailWord_1154621).sum := by decide
  have hdescent : baseEnd_1154621 < baseStart_1154621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154640 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 1, 7]
def baseStart_1154640 : Nat := 118140960795 + 1154640 * 2 ^ 59
def prefixEnd_1154640 : Nat := 4983230072969 + 3 ^ 40 * 1154640 * 2
def baseEnd_1154640 : Nat := 197628434302489233129971

theorem tailTrace_1154640 : CollatzResearch.WordTrace tailWord_1154640 prefixEnd_1154640 197628434302489233129971 := by
  unfold tailWord_1154640
  simp only [CollatzResearch.WordTrace]
  refine ⟨21056590268471975828734687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28075453691295967771646249 21056590268471975828734687)
  ·
    refine ⟨31584885402707963743102031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21056590268471975828734687 31584885402707963743102031)
    ·
      refine ⟨47377328104061945614653047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31584885402707963743102031 47377328104061945614653047)
      ·
        refine ⟨71065992156092918421979571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47377328104061945614653047 71065992156092918421979571)
        ·
          refine ⟨106598988234139377632969357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71065992156092918421979571 106598988234139377632969357)
          ·
            refine ⟨39974620587802266612363509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106598988234139377632969357 39974620587802266612363509)
            ·
              refine ⟨3747620680106462494909079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39974620587802266612363509 3747620680106462494909079)
              ·
                refine ⟨5621431020159693742363619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3747620680106462494909079 5621431020159693742363619)
                ·
                  refine ⟨8432146530239540613545429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5621431020159693742363619 8432146530239540613545429)
                  ·
                    refine ⟨197628434302489233129971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8432146530239540613545429 197628434302489233129971)
                    ·
                      rfl

theorem cell23_1154640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_1154640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154640 prefixEnd_1154640 := by exact prefixLift 1154640
  have htrace : WordTrace (prefixWord ++ tailWord_1154640) baseStart_1154640 baseEnd_1154640 := by
    simpa [prefixWord, tailWord_1154640, baseEnd_1154640] using wordTrace_append hprefix tailTrace_1154640
  have hstable : (prefixWord ++ tailWord_1154640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154640).length < 2 ^ (prefixWord ++ tailWord_1154640).sum := by decide
  have hdescent : baseEnd_1154640 < baseStart_1154640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154644 : List Nat := [2, 4, 1, 1, 1, 2, 4, 3, 5]
def baseStart_1154644 : Nat := 118140960795 + 1154644 * 2 ^ 59
def prefixEnd_1154644 : Nat := 4983230072969 + 3 ^ 40 * 1154644 * 2
def baseEnd_1154644 : Nat := 65876372981120631526655

theorem tailTrace_1154644 : CollatzResearch.WordTrace tailWord_1154644 prefixEnd_1154644 65876372981120631526655 := by
  unfold tailWord_1154644
  simp only [CollatzResearch.WordTrace]
  refine ⟨21056663214464730170307493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28075550952619640227076657 21056663214464730170307493)
  ·
    refine ⟨3948124352712136906932655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21056663214464730170307493 3948124352712136906932655)
    ·
      refine ⟨5922186529068205360398983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3948124352712136906932655 5922186529068205360398983)
      ·
        refine ⟨8883279793602308040598475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5922186529068205360398983 8883279793602308040598475)
        ·
          refine ⟨13324919690403462060897713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8883279793602308040598475 13324919690403462060897713)
          ·
            refine ⟨9993689767802596545673285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13324919690403462060897713 9993689767802596545673285)
            ·
              refine ⟨1873816831462986852313741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9993689767802596545673285 1873816831462986852313741)
              ·
                refine ⟨702681311798620069617653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1873816831462986852313741 702681311798620069617653)
                ·
                  refine ⟨65876372981120631526655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 702681311798620069617653 65876372981120631526655)
                  ·
                    rfl

theorem cell23_1154644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_1154644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154644 prefixEnd_1154644 := by exact prefixLift 1154644
  have htrace : WordTrace (prefixWord ++ tailWord_1154644) baseStart_1154644 baseEnd_1154644 := by
    simpa [prefixWord, tailWord_1154644, baseEnd_1154644] using wordTrace_append hprefix tailTrace_1154644
  have hstable : (prefixWord ++ tailWord_1154644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154644).length < 2 ^ (prefixWord ++ tailWord_1154644).sum := by decide
  have hdescent : baseEnd_1154644 < baseStart_1154644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154650 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_1154650 : Nat := 118140960795 + 1154650 * 2 ^ 59
def prefixEnd_1154650 : Nat := 4983230072969 + 3 ^ 40 * 1154650 * 2
def baseEnd_1154650 : Nat := 592890437714012660264867

theorem tailTrace_1154650 : CollatzResearch.WordTrace tailWord_1154650 prefixEnd_1154650 592890437714012660264867 := by
  unfold tailWord_1154650
  simp only [CollatzResearch.WordTrace]
  refine ⟨10528386316726930841333351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28075696844605148910222269 10528386316726930841333351)
  ·
    refine ⟨15792579475090396262000027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10528386316726930841333351 15792579475090396262000027)
    ·
      refine ⟨23688869212635594393000041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15792579475090396262000027 23688869212635594393000041)
      ·
        refine ⟨17766651909476695794750031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23688869212635594393000041 17766651909476695794750031)
        ·
          refine ⟨26649977864215043692125047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17766651909476695794750031 26649977864215043692125047)
          ·
            refine ⟨39974966796322565538187571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26649977864215043692125047 39974966796322565538187571)
            ·
              refine ⟨59962450194483848307281357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39974966796322565538187571 59962450194483848307281357)
              ·
                refine ⟨22485918822931443115230509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59962450194483848307281357 22485918822931443115230509)
                ·
                  refine ⟨8432219558599291168211441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22485918822931443115230509 8432219558599291168211441)
                  ·
                    refine ⟨6324164668949468376158581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8432219558599291168211441 6324164668949468376158581)
                    ·
                      refine ⟨592890437714012660264867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6324164668949468376158581 592890437714012660264867)
                      ·
                        rfl

theorem cell23_1154650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_1154650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154650 prefixEnd_1154650 := by exact prefixLift 1154650
  have htrace : WordTrace (prefixWord ++ tailWord_1154650) baseStart_1154650 baseEnd_1154650 := by
    simpa [prefixWord, tailWord_1154650, baseEnd_1154650] using wordTrace_append hprefix tailTrace_1154650
  have hstable : (prefixWord ++ tailWord_1154650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154650).length < 2 ^ (prefixWord ++ tailWord_1154650).sum := by decide
  have hdescent : baseEnd_1154650 < baseStart_1154650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154697 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 1, 4, 3]
def baseStart_1154697 : Nat := 118140960795 + 1154697 * 2 ^ 59
def prefixEnd_1154697 : Nat := 4983230072969 + 3 ^ 40 * 1154697 * 2
def baseEnd_1154697 : Nat := 592914571304773976377151

theorem tailTrace_1154697 : CollatzResearch.WordTrace tailWord_1154697 prefixEnd_1154697 592914571304773976377151 := by
  unfold tailWord_1154697
  simp only [CollatzResearch.WordTrace]
  refine ⟨42115259497737450392294345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28076839665158300261529563 42115259497737450392294345)
  ·
    refine ⟨31586444623303087794220759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42115259497737450392294345 31586444623303087794220759)
    ·
      refine ⟨47379666934954631691331139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31586444623303087794220759 47379666934954631691331139)
      ·
        refine ⟨71069500402431947536996709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47379666934954631691331139 71069500402431947536996709)
        ·
          refine ⟨13325531325455990163186883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71069500402431947536996709 13325531325455990163186883)
          ·
            refine ⟨19988296988183985244780325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13325531325455990163186883 19988296988183985244780325)
            ·
              refine ⟨3747805685284497233396311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19988296988183985244780325 3747805685284497233396311)
              ·
                refine ⟨5621708527926745850094467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3747805685284497233396311 5621708527926745850094467)
                ·
                  refine ⟨8432562791890118775141701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5621708527926745850094467 8432562791890118775141701)
                  ·
                    refine ⟨1581105523479397270339069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8432562791890118775141701 1581105523479397270339069)
                    ·
                      refine ⟨592914571304773976377151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1581105523479397270339069 592914571304773976377151)
                      ·
                        rfl

theorem cell23_1154697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4, 3].length) (baseStart_1154697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154697 prefixEnd_1154697 := by exact prefixLift 1154697
  have htrace : WordTrace (prefixWord ++ tailWord_1154697) baseStart_1154697 baseEnd_1154697 := by
    simpa [prefixWord, tailWord_1154697, baseEnd_1154697] using wordTrace_append hprefix tailTrace_1154697
  have hstable : (prefixWord ++ tailWord_1154697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154697).length < 2 ^ (prefixWord ++ tailWord_1154697).sum := by decide
  have hdescent : baseEnd_1154697 < baseStart_1154697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154700 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 10]
def baseStart_1154700 : Nat := 118140960795 + 1154700 * 2 ^ 59
def prefixEnd_1154700 : Nat := 4983230072969 + 3 ^ 40 * 1154700 * 2
def baseEnd_1154700 : Nat := 65879567971859718293293

theorem tailTrace_1154700 : CollatzResearch.WordTrace tailWord_1154700 prefixEnd_1154700 65879567971859718293293 := by
  unfold tailWord_1154700
  simp only [CollatzResearch.WordTrace]
  refine ⟨21057684458363290952326777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28076912611151054603102369 21057684458363290952326777)
  ·
    refine ⟨15793263343772468214245083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21057684458363290952326777 15793263343772468214245083)
    ·
      refine ⟨23689895015658702321367625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15793263343772468214245083 23689895015658702321367625)
      ·
        refine ⟨17767421261744026741025719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23689895015658702321367625 17767421261744026741025719)
        ·
          refine ⟨26651131892616040111538579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17767421261744026741025719 26651131892616040111538579)
          ·
            refine ⟨39976697838924060167307869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26651131892616040111538579 39976697838924060167307869)
            ·
              refine ⟨14991261689596522562740451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39976697838924060167307869 14991261689596522562740451)
              ·
                refine ⟨22486892534394783844110677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14991261689596522562740451 22486892534394783844110677)
                ·
                  refine ⟨65879567971859718293293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 22486892534394783844110677 65879567971859718293293)
                  ·
                    rfl

theorem cell23_1154700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_1154700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154700 prefixEnd_1154700 := by exact prefixLift 1154700
  have htrace : WordTrace (prefixWord ++ tailWord_1154700) baseStart_1154700 baseEnd_1154700 := by
    simpa [prefixWord, tailWord_1154700, baseEnd_1154700] using wordTrace_append hprefix tailTrace_1154700
  have hstable : (prefixWord ++ tailWord_1154700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154700).length < 2 ^ (prefixWord ++ tailWord_1154700).sum := by decide
  have hdescent : baseEnd_1154700 < baseStart_1154700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154717 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 6]
def baseStart_1154717 : Nat := 118140960795 + 1154717 * 2 ^ 59
def prefixEnd_1154717 : Nat := 4983230072969 + 3 ^ 40 * 1154717 * 2
def baseEnd_1154717 : Nat := 65880537879762655347451

theorem tailTrace_1154717 : CollatzResearch.WordTrace tailWord_1154717 prefixEnd_1154717 65880537879762655347451 := by
  unfold tailWord_1154717
  simp only [CollatzResearch.WordTrace]
  refine ⟨42115988957664993808022405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28077325971776662538681603 42115988957664993808022405)
  ·
    refine ⟨7896747929562186339004201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42115988957664993808022405 7896747929562186339004201)
    ·
      refine ⟨5922560947171639754253151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7896747929562186339004201 5922560947171639754253151)
      ·
        refine ⟨8883841420757459631379727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5922560947171639754253151 8883841420757459631379727)
        ·
          refine ⟨13325762131136189447069591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8883841420757459631379727 13325762131136189447069591)
          ·
            refine ⟨19988643196704284170604387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13325762131136189447069591 19988643196704284170604387)
            ·
              refine ⟨29982964795056426255906581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19988643196704284170604387 29982964795056426255906581)
              ·
                refine ⟨1405451474768269980745621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29982964795056426255906581 1405451474768269980745621)
                ·
                  refine ⟨65880537879762655347451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1405451474768269980745621 65880537879762655347451)
                  ·
                    rfl

theorem cell23_1154717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_1154717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154717 prefixEnd_1154717 := by exact prefixLift 1154717
  have htrace : WordTrace (prefixWord ++ tailWord_1154717) baseStart_1154717 baseEnd_1154717 := by
    simpa [prefixWord, tailWord_1154717, baseEnd_1154717] using wordTrace_append hprefix tailTrace_1154717
  have hstable : (prefixWord ++ tailWord_1154717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154717).length < 2 ^ (prefixWord ++ tailWord_1154717).sum := by decide
  have hdescent : baseEnd_1154717 < baseStart_1154717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154721 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 3, 4]
def baseStart_1154721 : Nat := 118140960795 + 1154721 * 2 ^ 59
def prefixEnd_1154721 : Nat := 4983230072969 + 3 ^ 40 * 1154721 * 2
def baseEnd_1154721 : Nat := 197642298280160627492347

theorem tailTrace_1154721 : CollatzResearch.WordTrace tailWord_1154721 prefixEnd_1154721 197642298280160627492347 := by
  unfold tailWord_1154721
  simp only [CollatzResearch.WordTrace]
  refine ⟨42116134849650502491168017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28077423233100334994112011 42116134849650502491168017)
  ·
    refine ⟨31587101137237876868376013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42116134849650502491168017 31587101137237876868376013)
    ·
      refine ⟨11845162926464203825641005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31587101137237876868376013 11845162926464203825641005)
      ·
        refine ⟨4441936097424076434615377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11845162926464203825641005 4441936097424076434615377)
        ·
          refine ⟨3331452073068057325961533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4441936097424076434615377 3331452073068057325961533)
          ·
            refine ⟨1249294527400521497235575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3331452073068057325961533 1249294527400521497235575)
            ·
              refine ⟨1873941791100782245853363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249294527400521497235575 1873941791100782245853363)
              ·
                refine ⟨2810912686651173368780045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873941791100782245853363 2810912686651173368780045)
                ·
                  refine ⟨1054092257494190013292517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2810912686651173368780045 1054092257494190013292517)
                  ·
                    refine ⟨197642298280160627492347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1054092257494190013292517 197642298280160627492347)
                    ·
                      rfl

theorem cell23_1154721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_1154721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154721 prefixEnd_1154721 := by exact prefixLift 1154721
  have htrace : WordTrace (prefixWord ++ tailWord_1154721) baseStart_1154721 baseEnd_1154721 := by
    simpa [prefixWord, tailWord_1154721, baseEnd_1154721] using wordTrace_append hprefix tailTrace_1154721
  have hstable : (prefixWord ++ tailWord_1154721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154721).length < 2 ^ (prefixWord ++ tailWord_1154721).sum := by decide
  have hdescent : baseEnd_1154721 < baseStart_1154721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154744 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 3, 1, 3]
def baseStart_1154744 : Nat := 118140960795 + 1154744 * 2 ^ 59
def prefixEnd_1154744 : Nat := 4983230072969 + 3 ^ 40 * 1154744 * 2
def baseEnd_1154744 : Nat := 592938704895535292489435

theorem tailTrace_1154744 : CollatzResearch.WordTrace tailWord_1154744 prefixEnd_1154744 592938704895535292489435 := by
  unfold tailWord_1154744
  simp only [CollatzResearch.WordTrace]
  refine ⟨21058486864283588709627643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28077982485711451612836857 21058486864283588709627643)
  ·
    refine ⟨31587730296425383064441465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21058486864283588709627643 31587730296425383064441465)
    ·
      refine ⟨23690797722319037298331099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31587730296425383064441465 23690797722319037298331099)
      ·
        refine ⟨35536196583478555947496649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23690797722319037298331099 35536196583478555947496649)
        ·
          refine ⟨26652147437608916960622487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35536196583478555947496649 26652147437608916960622487)
          ·
            refine ⟨39978221156413375440933731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26652147437608916960622487 39978221156413375440933731)
            ·
              refine ⟨59967331734620063161400597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39978221156413375440933731 59967331734620063161400597)
              ·
                refine ⟨2810968675060315460690653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59967331734620063161400597 2810968675060315460690653)
                ·
                  refine ⟨1054113253147618297758995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2810968675060315460690653 1054113253147618297758995)
                  ·
                    refine ⟨1581169879721427446638493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1054113253147618297758995 1581169879721427446638493)
                    ·
                      refine ⟨592938704895535292489435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1581169879721427446638493 592938704895535292489435)
                      ·
                        rfl

theorem cell23_1154744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_1154744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154744 prefixEnd_1154744 := by exact prefixLift 1154744
  have htrace : WordTrace (prefixWord ++ tailWord_1154744) baseStart_1154744 baseEnd_1154744 := by
    simpa [prefixWord, tailWord_1154744, baseEnd_1154744] using wordTrace_append hprefix tailTrace_1154744
  have hstable : (prefixWord ++ tailWord_1154744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154744).length < 2 ^ (prefixWord ++ tailWord_1154744).sum := by decide
  have hdescent : baseEnd_1154744 < baseStart_1154744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154778 : List Nat := [3, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3]
def baseStart_1154778 : Nat := 118140960795 + 1154778 * 2 ^ 59
def prefixEnd_1154778 : Nat := 4983230072969 + 3 ^ 40 * 1154778 * 2
def baseEnd_1154778 : Nat := 592956163237788159464279

theorem tailTrace_1154778 : CollatzResearch.WordTrace tailWord_1154778 prefixEnd_1154778 592956163237788159464279 := by
  unfold tailWord_1154778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10529553452611000306498247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28078809206962667483995325 10529553452611000306498247)
  ·
    refine ⟨15794330178916500459747371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10529553452611000306498247 15794330178916500459747371)
    ·
      refine ⟨23691495268374750689621057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15794330178916500459747371 23691495268374750689621057)
      ·
        refine ⟨17768621451281063017215793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23691495268374750689621057 17768621451281063017215793)
        ·
          refine ⟨13326466088460797262911845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17768621451281063017215793 13326466088460797262911845)
          ·
            refine ⟨2498712391586399486795971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13326466088460797262911845 2498712391586399486795971)
            ·
              refine ⟨3748068587379599230193957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2498712391586399486795971 3748068587379599230193957)
              ·
                refine ⟨702762860133674855661367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3748068587379599230193957 702762860133674855661367)
                ·
                  refine ⟨1054144290200512283492051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702762860133674855661367 1054144290200512283492051)
                  ·
                    refine ⟨1581216435300768425238077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1054144290200512283492051 1581216435300768425238077)
                    ·
                      refine ⟨592956163237788159464279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1581216435300768425238077 592956163237788159464279)
                      ·
                        rfl

theorem cell23_1154778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_1154778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154778 prefixEnd_1154778 := by exact prefixLift 1154778
  have htrace : WordTrace (prefixWord ++ tailWord_1154778) baseStart_1154778 baseEnd_1154778 := by
    simpa [prefixWord, tailWord_1154778, baseEnd_1154778] using wordTrace_append hprefix tailTrace_1154778
  have hstable : (prefixWord ++ tailWord_1154778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154778).length < 2 ^ (prefixWord ++ tailWord_1154778).sum := by decide
  have hdescent : baseEnd_1154778 < baseStart_1154778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154801 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 5, 2, 2]
def baseStart_1154801 : Nat := 118140960795 + 1154801 * 2 ^ 59
def prefixEnd_1154801 : Nat := 4983230072969 + 3 ^ 40 * 1154801 * 2
def baseEnd_1154801 : Nat := 592967973292841569476673

theorem tailTrace_1154801 : CollatzResearch.WordTrace tailWord_1154801 prefixEnd_1154801 592967973292841569476673 := by
  unfold tailWord_1154801
  simp only [CollatzResearch.WordTrace]
  refine ⟨42119052689360676154080257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28079368459573784102720171 42119052689360676154080257)
  ·
    refine ⟨31589289517020507115560193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42119052689360676154080257 31589289517020507115560193)
    ·
      refine ⟨23691967137765380336670145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31589289517020507115560193 23691967137765380336670145)
      ·
        refine ⟨17768975353324035252502609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23691967137765380336670145 17768975353324035252502609)
        ·
          refine ⟨13326731514993026439376957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17768975353324035252502609 13326731514993026439376957)
          ·
            refine ⟨4997524318122384914766359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13326731514993026439376957 4997524318122384914766359)
            ·
              refine ⟨7496286477183577372149539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4997524318122384914766359 7496286477183577372149539)
              ·
                refine ⟨11244429715775366058224309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7496286477183577372149539 11244429715775366058224309)
                ·
                  refine ⟨1054165285853940567958529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11244429715775366058224309 1054165285853940567958529)
                  ·
                    refine ⟨790623964390455425968897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1054165285853940567958529 790623964390455425968897)
                    ·
                      refine ⟨592967973292841569476673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 790623964390455425968897 592967973292841569476673)
                      ·
                        rfl

theorem cell23_1154801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_1154801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154801 prefixEnd_1154801 := by exact prefixLift 1154801
  have htrace : WordTrace (prefixWord ++ tailWord_1154801) baseStart_1154801 baseEnd_1154801 := by
    simpa [prefixWord, tailWord_1154801, baseEnd_1154801] using wordTrace_append hprefix tailTrace_1154801
  have hstable : (prefixWord ++ tailWord_1154801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154801).length < 2 ^ (prefixWord ++ tailWord_1154801).sum := by decide
  have hdescent : baseEnd_1154801 < baseStart_1154801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154818 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_1154818 : Nat := 118140960795 + 1154818 * 2 ^ 59
def prefixEnd_1154818 : Nat := 4983230072969 + 3 ^ 40 * 1154818 * 2
def baseEnd_1154818 : Nat := 592976702463968002964095

theorem tailTrace_1154818 : CollatzResearch.WordTrace tailWord_1154818 prefixEnd_1154818 592976702463968002964095 := by
  unfold tailWord_1154818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10529918182574772014362277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28079781820199392038299405 10529918182574772014362277)
  ·
    refine ⟨1974359659232769752692927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10529918182574772014362277 1974359659232769752692927)
    ·
      refine ⟨2961539488849154629039391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1974359659232769752692927 2961539488849154629039391)
      ·
        refine ⟨4442309233273731943559087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2961539488849154629039391 4442309233273731943559087)
        ·
          refine ⟨6663463849910597915338631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4442309233273731943559087 6663463849910597915338631)
          ·
            refine ⟨9995195774865896873007947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6663463849910597915338631 9995195774865896873007947)
            ·
              refine ⟨14992793662298845309511921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9995195774865896873007947 14992793662298845309511921)
              ·
                refine ⟨11244595246724133982133941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14992793662298845309511921 11244595246724133982133941)
                ·
                  refine ⟨1054180804380387560825057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11244595246724133982133941 1054180804380387560825057)
                  ·
                    refine ⟨790635603285290670618793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1054180804380387560825057 790635603285290670618793)
                    ·
                      refine ⟨592976702463968002964095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 790635603285290670618793 592976702463968002964095)
                      ·
                        rfl

theorem cell23_1154818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_1154818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154818 prefixEnd_1154818 := by exact prefixLift 1154818
  have htrace : WordTrace (prefixWord ++ tailWord_1154818) baseStart_1154818 baseEnd_1154818 := by
    simpa [prefixWord, tailWord_1154818, baseEnd_1154818] using wordTrace_append hprefix tailTrace_1154818
  have hstable : (prefixWord ++ tailWord_1154818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154818).length < 2 ^ (prefixWord ++ tailWord_1154818).sum := by decide
  have hdescent : baseEnd_1154818 < baseStart_1154818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154829 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1154829 : Nat := 118140960795 + 1154829 * 2 ^ 59
def prefixEnd_1154829 : Nat := 4983230072969 + 3 ^ 40 * 1154829 * 2
def baseEnd_1154829 : Nat := 592982350751167459926545

theorem tailTrace_1154829 : CollatzResearch.WordTrace tailWord_1154829 prefixEnd_1154829 592982350751167459926545 := by
  unfold tailWord_1154829
  simp only [CollatzResearch.WordTrace]
  refine ⟨42120073933259236936099541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28080049288839491290733027 42120073933259236936099541)
  ·
    refine ⟨987189232810763365689833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 42120073933259236936099541 987189232810763365689833)
    ·
      refine ⟨740391924608072524267375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 987189232810763365689833 740391924608072524267375)
      ·
        refine ⟨1110587886912108786401063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740391924608072524267375 1110587886912108786401063)
        ·
          refine ⟨1665881830368163179601595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110587886912108786401063 1665881830368163179601595)
          ·
            refine ⟨2498822745552244769402393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665881830368163179601595 2498822745552244769402393)
            ·
              refine ⟨1874117059164183577051795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2498822745552244769402393 1874117059164183577051795)
              ·
                refine ⟨2811175588746275365577693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874117059164183577051795 2811175588746275365577693)
                ·
                  refine ⟨1054190845779853262091635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2811175588746275365577693 1054190845779853262091635)
                  ·
                    refine ⟨1581286268669779893137453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1054190845779853262091635 1581286268669779893137453)
                    ·
                      refine ⟨592982350751167459926545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1581286268669779893137453 592982350751167459926545)
                      ·
                        rfl

theorem cell23_1154829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1154829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1154829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1154829 prefixEnd_1154829 := by exact prefixLift 1154829
  have htrace : WordTrace (prefixWord ++ tailWord_1154829) baseStart_1154829 baseEnd_1154829 := by
    simpa [prefixWord, tailWord_1154829, baseEnd_1154829] using wordTrace_append hprefix tailTrace_1154829
  have hstable : (prefixWord ++ tailWord_1154829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154829).length < 2 ^ (prefixWord ++ tailWord_1154829).sum := by decide
  have hdescent : baseEnd_1154829 < baseStart_1154829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
