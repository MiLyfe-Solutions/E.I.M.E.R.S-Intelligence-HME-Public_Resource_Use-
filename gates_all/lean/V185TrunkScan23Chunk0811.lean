import V185TrunkScan23Chunk0810

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4797179 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 4]
def baseStart_4797179 : Nat := 118140960795 + 4797179 * 2 ^ 59
def prefixEnd_4797179 : Nat := 4983230072969 + 3 ^ 40 * 4797179 * 2
def baseEnd_4797179 : Nat := 2463258612654991748800681

theorem tailTrace_4797179 : CollatzResearch.WordTrace tailWord_4797179 prefixEnd_4797179 2463258612654991748800681 := by
  unfold tailWord_4797179
  simp only [CollatzResearch.WordTrace]
  refine ⟨174967492287647250791066591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116644994858431500527377727 174967492287647250791066591)
  ·
    refine ⟨262451238431470876186599887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174967492287647250791066591 262451238431470876186599887)
    ·
      refine ⟨393676857647206314279899831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262451238431470876186599887 393676857647206314279899831)
      ·
        refine ⟨590515286470809471419849747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393676857647206314279899831 590515286470809471419849747)
        ·
          refine ⟨885772929706214207129774621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590515286470809471419849747 885772929706214207129774621)
          ·
            refine ⟨332164848639830327673665483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 885772929706214207129774621 332164848639830327673665483)
            ·
              refine ⟨498247272959745491510498225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332164848639830327673665483 498247272959745491510498225)
              ·
                refine ⟨373685454719809118632873669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498247272959745491510498225 373685454719809118632873669)
                ·
                  refine ⟨70066022759964209743663813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373685454719809118632873669 70066022759964209743663813)
                  ·
                    refine ⟨13137379267493289326936965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70066022759964209743663813 13137379267493289326936965)
                    ·
                      refine ⟨2463258612654991748800681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13137379267493289326936965 2463258612654991748800681)
                      ·
                        rfl

theorem cell23_4797179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 4].length) (baseStart_4797179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797179 prefixEnd_4797179 := by exact prefixLift 4797179
  have htrace : WordTrace (prefixWord ++ tailWord_4797179) baseStart_4797179 baseEnd_4797179 := by
    simpa [prefixWord, tailWord_4797179, baseEnd_4797179] using wordTrace_append hprefix tailTrace_4797179
  have hstable : (prefixWord ++ tailWord_4797179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797179).length < 2 ^ (prefixWord ++ tailWord_4797179).sum := by decide
  have hdescent : baseEnd_4797179 < baseStart_4797179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797189 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 8]
def baseStart_4797189 : Nat := 118140960795 + 4797189 * 2 ^ 59
def prefixEnd_4797189 : Nat := 4983230072969 + 3 ^ 40 * 4797189 * 2
def baseEnd_4797189 : Nat := 273695971940170745519515

theorem tailTrace_4797189 : CollatzResearch.WordTrace tailWord_4797189 prefixEnd_4797189 273695971940170745519515 := by
  unfold tailWord_4797189
  simp only [CollatzResearch.WordTrace]
  refine ⟨174967857017611022498930621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116645238011740681665953747 174967857017611022498930621)
  ·
    refine ⟨65612946381604133437098983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174967857017611022498930621 65612946381604133437098983)
    ·
      refine ⟨98419419572406200155648475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65612946381604133437098983 98419419572406200155648475)
      ·
        refine ⟨147629129358609300233472713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98419419572406200155648475 147629129358609300233472713)
        ·
          refine ⟨110721847018956975175104535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147629129358609300233472713 110721847018956975175104535)
          ·
            refine ⟨166082770528435462762656803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110721847018956975175104535 166082770528435462762656803)
            ·
              refine ⟨249124155792653194143985205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166082770528435462762656803 249124155792653194143985205)
              ·
                refine ⟨23355389605561236950998613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249124155792653194143985205 23355389605561236950998613)
                ·
                  refine ⟨273695971940170745519515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23355389605561236950998613 273695971940170745519515)
                  ·
                    rfl

theorem cell23_4797189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_4797189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797189 prefixEnd_4797189 := by exact prefixLift 4797189
  have htrace : WordTrace (prefixWord ++ tailWord_4797189) baseStart_4797189 baseEnd_4797189 := by
    simpa [prefixWord, tailWord_4797189, baseEnd_4797189] using wordTrace_append hprefix tailTrace_4797189
  have hstable : (prefixWord ++ tailWord_4797189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797189).length < 2 ^ (prefixWord ++ tailWord_4797189).sum := by decide
  have hdescent : baseEnd_4797189 < baseStart_4797189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797209 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_4797209 : Nat := 118140960795 + 4797209 * 2 ^ 59
def prefixEnd_4797209 : Nat := 4983230072969 + 3 ^ 40 * 4797209 * 2
def baseEnd_4797209 : Nat := 2463274017074626631425543

theorem tailTrace_4797209 : CollatzResearch.WordTrace tailWord_4797209 prefixEnd_4797209 2463274017074626631425543 := by
  unfold tailWord_4797209
  simp only [CollatzResearch.WordTrace]
  refine ⟨174968586477538565914658681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116645724318359043943105787 174968586477538565914658681)
  ·
    refine ⟨131226439858153924435994011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174968586477538565914658681 131226439858153924435994011)
    ·
      refine ⟨196839659787230886653991017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131226439858153924435994011 196839659787230886653991017)
      ·
        refine ⟨147629744840423164990493263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196839659787230886653991017 147629744840423164990493263)
        ·
          refine ⟨221444617260634747485739895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147629744840423164990493263 221444617260634747485739895)
          ·
            refine ⟨332166925890952121228609843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221444617260634747485739895 332166925890952121228609843)
            ·
              refine ⟨498250388836428181842914765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332166925890952121228609843 498250388836428181842914765)
              ·
                refine ⟨186843895813660568191093037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 498250388836428181842914765 186843895813660568191093037)
                ·
                  refine ⟨70066460930122713071659889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186843895813660568191093037 70066460930122713071659889)
                  ·
                    refine ⟨52549845697592034803744917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70066460930122713071659889 52549845697592034803744917)
                    ·
                      refine ⟨2463274017074626631425543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52549845697592034803744917 2463274017074626631425543)
                      ·
                        rfl

theorem cell23_4797209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_4797209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797209 prefixEnd_4797209 := by exact prefixLift 4797209
  have htrace : WordTrace (prefixWord ++ tailWord_4797209) baseStart_4797209 baseEnd_4797209 := by
    simpa [prefixWord, tailWord_4797209, baseEnd_4797209] using wordTrace_append hprefix tailTrace_4797209
  have hstable : (prefixWord ++ tailWord_4797209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797209).length < 2 ^ (prefixWord ++ tailWord_4797209).sum := by decide
  have hdescent : baseEnd_4797209 < baseStart_4797209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797233 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 5, 1, 3]
def baseStart_4797233 : Nat := 118140960795 + 4797233 * 2 ^ 59
def prefixEnd_4797233 : Nat := 4983230072969 + 3 ^ 40 * 4797233 * 2
def baseEnd_4797233 : Nat := 2463286340610334537525433

theorem tailTrace_4797233 : CollatzResearch.WordTrace tailWord_4797233 prefixEnd_4797233 2463286340610334537525433 := by
  unfold tailWord_4797233
  simp only [CollatzResearch.WordTrace]
  refine ⟨174969461829451618013532353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116646307886301078675688235 174969461829451618013532353)
  ·
    refine ⟨131227096372088713510149265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174969461829451618013532353 131227096372088713510149265)
    ·
      refine ⟨98420322279066535132611949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131227096372088713510149265 98420322279066535132611949)
      ·
        refine ⟨36907620854649950674729481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98420322279066535132611949 36907620854649950674729481)
        ·
          refine ⟨27680715640987463006047111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36907620854649950674729481 27680715640987463006047111)
          ·
            refine ⟨41521073461481194509070667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27680715640987463006047111 41521073461481194509070667)
            ·
              refine ⟨62281610192221791763606001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41521073461481194509070667 62281610192221791763606001)
              ·
                refine ⟨46711207644166343822704501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62281610192221791763606001 46711207644166343822704501)
                ·
                  refine ⟨4379175716640594733378547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46711207644166343822704501 4379175716640594733378547)
                  ·
                    refine ⟨6568763574960892100067821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4379175716640594733378547 6568763574960892100067821)
                    ·
                      refine ⟨2463286340610334537525433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6568763574960892100067821 2463286340610334537525433)
                      ·
                        rfl

theorem cell23_4797233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_4797233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797233 prefixEnd_4797233 := by exact prefixLift 4797233
  have htrace : WordTrace (prefixWord ++ tailWord_4797233) baseStart_4797233 baseEnd_4797233 := by
    simpa [prefixWord, tailWord_4797233, baseEnd_4797233] using wordTrace_append hprefix tailTrace_4797233
  have hstable : (prefixWord ++ tailWord_4797233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797233).length < 2 ^ (prefixWord ++ tailWord_4797233).sum := by decide
  have hdescent : baseEnd_4797233 < baseStart_4797233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797273 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 4]
def baseStart_4797273 : Nat := 118140960795 + 4797273 * 2 ^ 59
def prefixEnd_4797273 : Nat := 4983230072969 + 3 ^ 40 * 4797273 * 2
def baseEnd_4797273 : Nat := 2463306879836514381025249

theorem tailTrace_4797273 : CollatzResearch.WordTrace tailWord_4797273 prefixEnd_4797273 2463306879836514381025249 := by
  unfold tailWord_4797273
  simp only [CollatzResearch.WordTrace]
  refine ⟨174970920749306704844988473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116647280499537803229992315 174970920749306704844988473)
  ·
    refine ⟨131228190561980028633741355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174970920749306704844988473 131228190561980028633741355)
    ·
      refine ⟨196842285842970042950612033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131228190561980028633741355 196842285842970042950612033)
      ·
        refine ⟨147631714382227532212959025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196842285842970042950612033 147631714382227532212959025)
        ·
          refine ⟨110723785786670649159719269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147631714382227532212959025 110723785786670649159719269)
          ·
            refine ⟨20760709835000746717447363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110723785786670649159719269 20760709835000746717447363)
            ·
              refine ⟨31141064752501120076171045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20760709835000746717447363 31141064752501120076171045)
              ·
                refine ⟨5838949641093960014282071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31141064752501120076171045 5838949641093960014282071)
                ·
                  refine ⟨8758424461640940021423107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5838949641093960014282071 8758424461640940021423107)
                  ·
                    refine ⟨13137636692461410032134661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8758424461640940021423107 13137636692461410032134661)
                    ·
                      refine ⟨2463306879836514381025249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13137636692461410032134661 2463306879836514381025249)
                      ·
                        rfl

theorem cell23_4797273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_4797273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797273 prefixEnd_4797273 := by exact prefixLift 4797273
  have htrace : WordTrace (prefixWord ++ tailWord_4797273) baseStart_4797273 baseEnd_4797273 := by
    simpa [prefixWord, tailWord_4797273, baseEnd_4797273] using wordTrace_append hprefix tailTrace_4797273
  have hstable : (prefixWord ++ tailWord_4797273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797273).length < 2 ^ (prefixWord ++ tailWord_4797273).sum := by decide
  have hdescent : baseEnd_4797273 < baseStart_4797273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797283 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 4, 4]
def baseStart_4797283 : Nat := 118140960795 + 4797283 * 2 ^ 59
def prefixEnd_4797283 : Nat := 4983230072969 + 3 ^ 40 * 4797283 * 2
def baseEnd_4797283 : Nat := 821104004881019780633401

theorem tailTrace_4797283 : CollatzResearch.WordTrace tailWord_4797283 prefixEnd_4797283 821104004881019780633401 := by
  unfold tailWord_4797283
  simp only [CollatzResearch.WordTrace]
  refine ⟨174971285479270476552852503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116647523652846984368568335 174971285479270476552852503)
  ·
    refine ⟨262456928218905714829278755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174971285479270476552852503 262456928218905714829278755)
    ·
      refine ⟨393685392328358572243918133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262456928218905714829278755 393685392328358572243918133)
      ·
        refine ⟨36908005530783616147867325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 393685392328358572243918133 36908005530783616147867325)
        ·
          refine ⟨13840502074043856055450247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36908005530783616147867325 13840502074043856055450247)
          ·
            refine ⟨20760753111065784083175371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13840502074043856055450247 20760753111065784083175371)
            ·
              refine ⟨31141129666598676124763057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20760753111065784083175371 31141129666598676124763057)
              ·
                refine ⟨23355847249949007093572293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31141129666598676124763057 23355847249949007093572293)
                ·
                  refine ⟨4379221359365438830044805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23355847249949007093572293 4379221359365438830044805)
                  ·
                    refine ⟨821104004881019780633401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4379221359365438830044805 821104004881019780633401)
                    ·
                      rfl

theorem cell23_4797283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 4].length) (baseStart_4797283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797283 prefixEnd_4797283 := by exact prefixLift 4797283
  have htrace : WordTrace (prefixWord ++ tailWord_4797283) baseStart_4797283 baseEnd_4797283 := by
    simpa [prefixWord, tailWord_4797283, baseEnd_4797283] using wordTrace_append hprefix tailTrace_4797283
  have hstable : (prefixWord ++ tailWord_4797283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797283).length < 2 ^ (prefixWord ++ tailWord_4797283).sum := by decide
  have hdescent : baseEnd_4797283 < baseStart_4797283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797284 : List Nat := [2, 3, 1, 1, 4, 3, 1, 3, 1, 1, 3]
def baseStart_4797284 : Nat := 118140960795 + 4797284 * 2 ^ 59
def prefixEnd_4797284 : Nat := 4983230072969 + 3 ^ 40 * 4797284 * 2
def baseEnd_4797284 : Nat := 2463312528123713837987699

theorem tailTrace_4797284 : CollatzResearch.WordTrace tailWord_4797284 prefixEnd_4797284 2463312528123713837987699 := by
  unfold tailWord_4797284
  simp only [CollatzResearch.WordTrace]
  refine ⟨87485660976133426861819453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116647547968177902482425937 87485660976133426861819453)
  ·
    refine ⟨32807122866050035073182295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87485660976133426861819453 32807122866050035073182295)
    ·
      refine ⟨49210684299075052609773443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32807122866050035073182295 49210684299075052609773443)
      ·
        refine ⟨73816026448612578914660165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49210684299075052609773443 73816026448612578914660165)
        ·
          refine ⟨13840504959114858546498781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73816026448612578914660165 13840504959114858546498781)
          ·
            refine ⟨5190189359668071954937043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13840504959114858546498781 5190189359668071954937043)
            ·
              refine ⟨7785284039502107932405565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5190189359668071954937043 7785284039502107932405565)
              ·
                refine ⟨2919481514813290474652087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7785284039502107932405565 2919481514813290474652087)
                ·
                  refine ⟨4379222272219935711978131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919481514813290474652087 4379222272219935711978131)
                  ·
                    refine ⟨6568833408329903567967197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4379222272219935711978131 6568833408329903567967197)
                    ·
                      refine ⟨2463312528123713837987699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6568833408329903567967197 2463312528123713837987699)
                      ·
                        rfl

theorem cell23_4797284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_4797284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797284 prefixEnd_4797284 := by exact prefixLift 4797284
  have htrace : WordTrace (prefixWord ++ tailWord_4797284) baseStart_4797284 baseEnd_4797284 := by
    simpa [prefixWord, tailWord_4797284, baseEnd_4797284] using wordTrace_append hprefix tailTrace_4797284
  have hstable : (prefixWord ++ tailWord_4797284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797284).length < 2 ^ (prefixWord ++ tailWord_4797284).sum := by decide
  have hdescent : baseEnd_4797284 < baseStart_4797284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797293 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_4797293 : Nat := 118140960795 + 4797293 * 2 ^ 59
def prefixEnd_4797293 : Nat := 4983230072969 + 3 ^ 40 * 4797293 * 2
def baseEnd_4797293 : Nat := 2463317149449604302775157

theorem tailTrace_4797293 : CollatzResearch.WordTrace tailWord_4797293 prefixEnd_4797293 2463317149449604302775157 := by
  unfold tailWord_4797293
  simp only [CollatzResearch.WordTrace]
  refine ⟨174971650209234248260716533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116647766806156165507144355 174971650209234248260716533)
  ·
    refine ⟨16403592207115710774442175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174971650209234248260716533 16403592207115710774442175)
    ·
      refine ⟨24605388310673566161663263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16403592207115710774442175 24605388310673566161663263)
      ·
        refine ⟨36908082466010349242494895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24605388310673566161663263 36908082466010349242494895)
        ·
          refine ⟨55362123699015523863742343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36908082466010349242494895 55362123699015523863742343)
          ·
            refine ⟨83043185548523285795613515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55362123699015523863742343 83043185548523285795613515)
            ·
              refine ⟨124564778322784928693420273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83043185548523285795613515 124564778322784928693420273)
              ·
                refine ⟨93423583742088696520065205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124564778322784928693420273 93423583742088696520065205)
                ·
                  refine ⟨8758460975820815298756113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93423583742088696520065205 8758460975820815298756113)
                  ·
                    refine ⟨6568845731865611474067085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8758460975820815298756113 6568845731865611474067085)
                    ·
                      refine ⟨2463317149449604302775157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6568845731865611474067085 2463317149449604302775157)
                      ·
                        rfl

theorem cell23_4797293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_4797293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797293 prefixEnd_4797293 := by exact prefixLift 4797293
  have htrace : WordTrace (prefixWord ++ tailWord_4797293) baseStart_4797293 baseEnd_4797293 := by
    simpa [prefixWord, tailWord_4797293, baseEnd_4797293] using wordTrace_append hprefix tailTrace_4797293
  have hstable : (prefixWord ++ tailWord_4797293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797293).length < 2 ^ (prefixWord ++ tailWord_4797293).sum := by decide
  have hdescent : baseEnd_4797293 < baseStart_4797293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797307 : List Nat := [1, 1, 1, 1, 1, 5, 2, 6, 1, 2, 2]
def baseStart_4797307 : Nat := 118140960795 + 4797307 * 2 ^ 59
def prefixEnd_4797307 : Nat := 4983230072969 + 3 ^ 40 * 4797307 * 2
def baseEnd_4797307 : Nat := 2463324338178767248000093

theorem tailTrace_4797307 : CollatzResearch.WordTrace tailWord_4797307 prefixEnd_4797307 2463324338178767248000093 := by
  unfold tailWord_4797307
  simp only [CollatzResearch.WordTrace]
  refine ⟨174972160831183528651726175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116648107220789019101150783 174972160831183528651726175)
  ·
    refine ⟨262458241246775292977589263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174972160831183528651726175 262458241246775292977589263)
    ·
      refine ⟨393687361870162939466383895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262458241246775292977589263 393687361870162939466383895)
      ·
        refine ⟨590531042805244409199575843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393687361870162939466383895 590531042805244409199575843)
        ·
          refine ⟨885796564207866613799363765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590531042805244409199575843 885796564207866613799363765)
          ·
            refine ⟨83043427894487495043690353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 885796564207866613799363765 83043427894487495043690353)
            ·
              refine ⟨62282570920865621282767765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83043427894487495043690353 62282570920865621282767765)
              ·
                refine ⟨2919495511915575997629739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62282570920865621282767765 2919495511915575997629739)
                ·
                  refine ⟨4379243267873363996444609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919495511915575997629739 4379243267873363996444609)
                  ·
                    refine ⟨3284432450905022997333457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4379243267873363996444609 3284432450905022997333457)
                    ·
                      refine ⟨2463324338178767248000093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284432450905022997333457 2463324338178767248000093)
                      ·
                        rfl

theorem cell23_4797307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 1, 2, 2].length) (baseStart_4797307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797307 prefixEnd_4797307 := by exact prefixLift 4797307
  have htrace : WordTrace (prefixWord ++ tailWord_4797307) baseStart_4797307 baseEnd_4797307 := by
    simpa [prefixWord, tailWord_4797307, baseEnd_4797307] using wordTrace_append hprefix tailTrace_4797307
  have hstable : (prefixWord ++ tailWord_4797307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797307).length < 2 ^ (prefixWord ++ tailWord_4797307).sum := by decide
  have hdescent : baseEnd_4797307 < baseStart_4797307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797316 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_4797316 : Nat := 118140960795 + 4797316 * 2 ^ 59
def prefixEnd_4797316 : Nat := 4983230072969 + 3 ^ 40 * 4797316 * 2
def baseEnd_4797316 : Nat := 2463328959504657712787551

theorem tailTrace_4797316 : CollatzResearch.WordTrace tailWord_4797316 prefixEnd_4797316 2463328959504657712787551 := by
  unfold tailWord_4797316
  simp only [CollatzResearch.WordTrace]
  refine ⟨87486244544075461594401901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116648326058767282125869201 87486244544075461594401901)
  ·
    refine ⟨32807341704028298097900713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87486244544075461594401901 32807341704028298097900713)
    ·
      refine ⟨24605506278021223573425535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32807341704028298097900713 24605506278021223573425535)
      ·
        refine ⟨36908259417031835360138303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24605506278021223573425535 36908259417031835360138303)
        ·
          refine ⟨55362389125547753040207455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36908259417031835360138303 55362389125547753040207455)
          ·
            refine ⟨83043583688321629560311183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55362389125547753040207455 83043583688321629560311183)
            ·
              refine ⟨124565375532482444340466775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83043583688321629560311183 124565375532482444340466775)
              ·
                refine ⟨186848063298723666510700163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124565375532482444340466775 186848063298723666510700163)
                ·
                  refine ⟨280272094948085499766050245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186848063298723666510700163 280272094948085499766050245)
                  ·
                    refine ⟨52551017802766031206134421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 280272094948085499766050245 52551017802766031206134421)
                    ·
                      refine ⟨2463328959504657712787551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52551017802766031206134421 2463328959504657712787551)
                      ·
                        rfl

theorem cell23_4797316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_4797316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797316 prefixEnd_4797316 := by exact prefixLift 4797316
  have htrace : WordTrace (prefixWord ++ tailWord_4797316) baseStart_4797316 baseEnd_4797316 := by
    simpa [prefixWord, tailWord_4797316, baseEnd_4797316] using wordTrace_append hprefix tailTrace_4797316
  have hstable : (prefixWord ++ tailWord_4797316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797316).length < 2 ^ (prefixWord ++ tailWord_4797316).sum := by decide
  have hdescent : baseEnd_4797316 < baseStart_4797316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797317 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 2, 4]
def baseStart_4797317 : Nat := 118140960795 + 4797317 * 2 ^ 59
def prefixEnd_4797317 : Nat := 4983230072969 + 3 ^ 40 * 4797317 * 2
def baseEnd_4797317 : Nat := 821109824328437402958349

theorem tailTrace_4797317 : CollatzResearch.WordTrace tailWord_4797317 prefixEnd_4797317 821109824328437402958349 := by
  unfold tailWord_4797317
  simp only [CollatzResearch.WordTrace]
  refine ⟨174972525561147300359590205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116648350374098200239726803 174972525561147300359590205)
  ·
    refine ⟨65614697085430237634846327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174972525561147300359590205 65614697085430237634846327)
    ·
      refine ⟨98422045628145356452269491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65614697085430237634846327 98422045628145356452269491)
      ·
        refine ⟨147633068442218034678404237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98422045628145356452269491 147633068442218034678404237)
        ·
          refine ⟨55362400665831763004401589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147633068442218034678404237 55362400665831763004401589)
          ·
            refine ⟨5190225062421727781662649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55362400665831763004401589 5190225062421727781662649)
            ·
              refine ⟨3892668796816295836246987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5190225062421727781662649 3892668796816295836246987)
              ·
                refine ⟨5839003195224443754370481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3892668796816295836246987 5839003195224443754370481)
                ·
                  refine ⟨4379252396418332815777861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5839003195224443754370481 4379252396418332815777861)
                  ·
                    refine ⟨821109824328437402958349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4379252396418332815777861 821109824328437402958349)
                    ·
                      rfl

theorem cell23_4797317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_4797317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797317 prefixEnd_4797317 := by exact prefixLift 4797317
  have htrace : WordTrace (prefixWord ++ tailWord_4797317) baseStart_4797317 baseEnd_4797317 := by
    simpa [prefixWord, tailWord_4797317, baseEnd_4797317] using wordTrace_append hprefix tailTrace_4797317
  have hstable : (prefixWord ++ tailWord_4797317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797317).length < 2 ^ (prefixWord ++ tailWord_4797317).sum := by decide
  have hdescent : baseEnd_4797317 < baseStart_4797317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797356 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_4797356 : Nat := 118140960795 + 4797356 * 2 ^ 59
def prefixEnd_4797356 : Nat := 4983230072969 + 3 ^ 40 * 4797356 * 2
def baseEnd_4797356 : Nat := 821116499576945852095789

theorem tailTrace_4797356 : CollatzResearch.WordTrace tailWord_4797356 prefixEnd_4797356 821116499576945852095789 := by
  unfold tailWord_4797356
  simp only [CollatzResearch.WordTrace]
  refine ⟨87486974004003005010129961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116649298672004006680173281 87486974004003005010129961)
  ·
    refine ⟨65615230503002253757597471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87486974004003005010129961 65615230503002253757597471)
    ·
      refine ⟨98422845754503380636396207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65615230503002253757597471 98422845754503380636396207)
      ·
        refine ⟨147634268631755070954594311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98422845754503380636396207 147634268631755070954594311)
        ·
          refine ⟨221451402947632606431891467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147634268631755070954594311 221451402947632606431891467)
          ·
            refine ⟨332177104421448909647837201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221451402947632606431891467 332177104421448909647837201)
            ·
              refine ⟨249132828316086682235877901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332177104421448909647837201 249132828316086682235877901)
              ·
                refine ⟨93424810618532505838454213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249132828316086682235877901 93424810618532505838454213)
                ·
                  refine ⟨17517151990974844844710165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93424810618532505838454213 17517151990974844844710165)
                  ·
                    refine ⟨821116499576945852095789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17517151990974844844710165 821116499576945852095789)
                    ·
                      rfl

theorem cell23_4797356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_4797356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797356 prefixEnd_4797356 := by exact prefixLift 4797356
  have htrace : WordTrace (prefixWord ++ tailWord_4797356) baseStart_4797356 baseEnd_4797356 := by
    simpa [prefixWord, tailWord_4797356, baseEnd_4797356] using wordTrace_append hprefix tailTrace_4797356
  have hstable : (prefixWord ++ tailWord_4797356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797356).length < 2 ^ (prefixWord ++ tailWord_4797356).sum := by decide
  have hdescent : baseEnd_4797356 < baseStart_4797356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797490 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_4797490 : Nat := 118140960795 + 4797490 * 2 ^ 59
def prefixEnd_4797490 : Nat := 4983230072969 + 3 ^ 40 * 4797490 * 2
def baseEnd_4797490 : Nat := 2463418305138540032011751

theorem tailTrace_4797490 : CollatzResearch.WordTrace tailWord_4797490 prefixEnd_4797490 2463418305138540032011751 := by
  unfold tailWord_4797490
  simp only [CollatzResearch.WordTrace]
  refine ⟨43744708847380137726409481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116652556926347033937091949 43744708847380137726409481)
  ·
    refine ⟨32808531635535103294807111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43744708847380137726409481 32808531635535103294807111)
    ·
      refine ⟨49212797453302654942210667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32808531635535103294807111 49212797453302654942210667)
      ·
        refine ⟨73819196179953982413316001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49212797453302654942210667 73819196179953982413316001)
        ·
          refine ⟨55364397134965486809987001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73819196179953982413316001 55364397134965486809987001)
          ·
            refine ⟨41523297851224115107490251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55364397134965486809987001 41523297851224115107490251)
            ·
              refine ⟨62284946776836172661235377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41523297851224115107490251 62284946776836172661235377)
              ·
                refine ⟨46713710082627129495926533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62284946776836172661235377 46713710082627129495926533)
                ·
                  refine ⟨8758820640492586780486225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46713710082627129495926533 8758820640492586780486225)
                  ·
                    refine ⟨6569115480369440085364669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8758820640492586780486225 6569115480369440085364669)
                    ·
                      refine ⟨2463418305138540032011751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6569115480369440085364669 2463418305138540032011751)
                      ·
                        rfl

theorem cell23_4797490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_4797490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797490 prefixEnd_4797490 := by exact prefixLift 4797490
  have htrace : WordTrace (prefixWord ++ tailWord_4797490) baseStart_4797490 baseEnd_4797490 := by
    simpa [prefixWord, tailWord_4797490, baseEnd_4797490] using wordTrace_append hprefix tailTrace_4797490
  have hstable : (prefixWord ++ tailWord_4797490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797490).length < 2 ^ (prefixWord ++ tailWord_4797490).sum := by decide
  have hdescent : baseEnd_4797490 < baseStart_4797490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797523 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 5, 5]
def baseStart_4797523 : Nat := 118140960795 + 4797523 * 2 ^ 59
def prefixEnd_4797523 : Nat := 4983230072969 + 3 ^ 40 * 4797523 * 2
def baseEnd_4797523 : Nat := 821145083333379467633033

theorem tailTrace_4797523 : CollatzResearch.WordTrace tailWord_4797523 prefixEnd_4797523 821145083333379467633033 := by
  unfold tailWord_4797523
  simp only [CollatzResearch.WordTrace]
  refine ⟨174980038998400997541589223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116653359332267331694392815 174980038998400997541589223)
  ·
    refine ⟨262470058497601496312383835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174980038998400997541589223 262470058497601496312383835)
    ·
      refine ⟨393705087746402244468575753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262470058497601496312383835 393705087746402244468575753)
      ·
        refine ⟨295278815809801683351431815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393705087746402244468575753 295278815809801683351431815)
        ·
          refine ⟨442918223714702525027147723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295278815809801683351431815 442918223714702525027147723)
          ·
            refine ⟨664377335572053787540721585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442918223714702525027147723 664377335572053787540721585)
            ·
              refine ⟨498283001679040340655541189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664377335572053787540721585 498283001679040340655541189)
              ·
                refine ⟨93428062814820063872913973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498283001679040340655541189 93428062814820063872913973)
                ·
                  refine ⟨8758880888889380988085685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93428062814820063872913973 8758880888889380988085685)
                  ·
                    refine ⟨821145083333379467633033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8758880888889380988085685 821145083333379467633033)
                    ·
                      rfl

theorem cell23_4797523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 5].length) (baseStart_4797523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797523 prefixEnd_4797523 := by exact prefixLift 4797523
  have htrace : WordTrace (prefixWord ++ tailWord_4797523) baseStart_4797523 baseEnd_4797523 := by
    simpa [prefixWord, tailWord_4797523, baseEnd_4797523] using wordTrace_append hprefix tailTrace_4797523
  have hstable : (prefixWord ++ tailWord_4797523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797523).length < 2 ^ (prefixWord ++ tailWord_4797523).sum := by decide
  have hdescent : baseEnd_4797523 < baseStart_4797523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797560 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_4797560 : Nat := 118140960795 + 4797560 * 2 ^ 59
def prefixEnd_4797560 : Nat := 4983230072969 + 3 ^ 40 * 4797560 * 2
def baseEnd_4797560 : Nat := 2463454248784354758136429

theorem tailTrace_4797560 : CollatzResearch.WordTrace tailWord_4797560 prefixEnd_4797560 2463454248784354758136429 := by
  unfold tailWord_4797560
  simp only [CollatzResearch.WordTrace]
  refine ⟨87490694249633476430343067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116654258999511301907124089 87490694249633476430343067)
  ·
    refine ⟨131236041374450214645514601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87490694249633476430343067 131236041374450214645514601)
    ·
      refine ⟨98427031030837660984135951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131236041374450214645514601 98427031030837660984135951)
      ·
        refine ⟨147640546546256491476203927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98427031030837660984135951 147640546546256491476203927)
        ·
          refine ⟨221460819819384737214305891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147640546546256491476203927 221460819819384737214305891)
          ·
            refine ⟨332191229729077105821458837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221460819819384737214305891 332191229729077105821458837)
            ·
              refine ⟨15571463893550489335380883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 332191229729077105821458837 15571463893550489335380883)
              ·
                refine ⟨23357195840325734003071325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15571463893550489335380883 23357195840325734003071325)
                ·
                  refine ⟨8758948440122150251151747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23357195840325734003071325 8758948440122150251151747)
                  ·
                    refine ⟨13138422660183225376727621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8758948440122150251151747 13138422660183225376727621)
                    ·
                      refine ⟨2463454248784354758136429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13138422660183225376727621 2463454248784354758136429)
                      ·
                        rfl

theorem cell23_4797560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_4797560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797560 prefixEnd_4797560 := by exact prefixLift 4797560
  have htrace : WordTrace (prefixWord ++ tailWord_4797560) baseStart_4797560 baseEnd_4797560 := by
    simpa [prefixWord, tailWord_4797560, baseEnd_4797560] using wordTrace_append hprefix tailTrace_4797560
  have hstable : (prefixWord ++ tailWord_4797560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797560).length < 2 ^ (prefixWord ++ tailWord_4797560).sum := by decide
  have hdescent : baseEnd_4797560 < baseStart_4797560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797577 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 4]
def baseStart_4797577 : Nat := 118140960795 + 4797577 * 2 ^ 59
def prefixEnd_4797577 : Nat := 4983230072969 + 3 ^ 40 * 4797577 * 2
def baseEnd_4797577 : Nat := 2463462977955481191623851

theorem tailTrace_4797577 : CollatzResearch.WordTrace tailWord_4797577 prefixEnd_4797577 2463462977955481191623851 := by
  unfold tailWord_4797577
  simp only [CollatzResearch.WordTrace]
  refine ⟨174982008540205364764054985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116654672360136909842703323 174982008540205364764054985)
  ·
    refine ⟨131236506405154023573041239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174982008540205364764054985 131236506405154023573041239)
    ·
      refine ⟨196854759607731035359561859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131236506405154023573041239 196854759607731035359561859)
      ·
        refine ⟨295282139411596553039342789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196854759607731035359561859 295282139411596553039342789)
        ·
          refine ⟨55365401139674353694876773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 295282139411596553039342789 55365401139674353694876773)
          ·
            refine ⟨10381012713688941317789395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55365401139674353694876773 10381012713688941317789395)
            ·
              refine ⟨15571519070533411976684093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10381012713688941317789395 15571519070533411976684093)
              ·
                refine ⟨5839319651450029491256535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15571519070533411976684093 5839319651450029491256535)
                ·
                  refine ⟨8758979477175044236884803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5839319651450029491256535 8758979477175044236884803)
                  ·
                    refine ⟨13138469215762566355327205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8758979477175044236884803 13138469215762566355327205)
                    ·
                      refine ⟨2463462977955481191623851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13138469215762566355327205 2463462977955481191623851)
                      ·
                        rfl

theorem cell23_4797577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 4].length) (baseStart_4797577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797577 prefixEnd_4797577 := by exact prefixLift 4797577
  have htrace : WordTrace (prefixWord ++ tailWord_4797577) baseStart_4797577 baseEnd_4797577 := by
    simpa [prefixWord, tailWord_4797577, baseEnd_4797577] using wordTrace_append hprefix tailTrace_4797577
  have hstable : (prefixWord ++ tailWord_4797577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797577).length < 2 ^ (prefixWord ++ tailWord_4797577).sum := by decide
  have hdescent : baseEnd_4797577 < baseStart_4797577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797587 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 2, 4]
def baseStart_4797587 : Nat := 118140960795 + 4797587 * 2 ^ 59
def prefixEnd_4797587 : Nat := 4983230072969 + 3 ^ 40 * 4797587 * 2
def baseEnd_4797587 : Nat := 821156037587342050832935

theorem tailTrace_4797587 : CollatzResearch.WordTrace tailWord_4797587 prefixEnd_4797587 821156037587342050832935 := by
  unfold tailWord_4797587
  simp only [CollatzResearch.WordTrace]
  refine ⟨174982373270169136471919015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116654915513446090981279343 174982373270169136471919015)
  ·
    refine ⟨262473559905253704707878523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174982373270169136471919015 262473559905253704707878523)
    ·
      refine ⟨393710339857880557061817785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262473559905253704707878523 393710339857880557061817785)
      ·
        refine ⟨295282754893410417796363339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393710339857880557061817785 295282754893410417796363339)
        ·
          refine ⟨442924132340115626694545009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295282754893410417796363339 442924132340115626694545009)
          ·
            refine ⟨332193099255086720020908757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442924132340115626694545009 332193099255086720020908757)
            ·
              refine ⟨7785775763791095000490049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 332193099255086720020908757 7785775763791095000490049)
              ·
                refine ⟨5839331822843321250367537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7785775763791095000490049 5839331822843321250367537)
                ·
                  refine ⟨4379498867132490937775653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5839331822843321250367537 4379498867132490937775653)
                  ·
                    refine ⟨821156037587342050832935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4379498867132490937775653 821156037587342050832935)
                    ·
                      rfl

theorem cell23_4797587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 4].length) (baseStart_4797587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797587 prefixEnd_4797587 := by exact prefixLift 4797587
  have htrace : WordTrace (prefixWord ++ tailWord_4797587) baseStart_4797587 baseEnd_4797587 := by
    simpa [prefixWord, tailWord_4797587, baseEnd_4797587] using wordTrace_append hprefix tailTrace_4797587
  have hstable : (prefixWord ++ tailWord_4797587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797587).length < 2 ^ (prefixWord ++ tailWord_4797587).sum := by decide
  have hdescent : baseEnd_4797587 < baseStart_4797587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797593 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_4797593 : Nat := 118140960795 + 4797593 * 2 ^ 59
def prefixEnd_4797593 : Nat := 4983230072969 + 3 ^ 40 * 4797593 * 2
def baseEnd_4797593 : Nat := 2463471193645953129023777

theorem tailTrace_4797593 : CollatzResearch.WordTrace tailWord_4797593 prefixEnd_4797593 2463471193645953129023777 := by
  unfold tailWord_4797593
  simp only [CollatzResearch.WordTrace]
  refine ⟨174982592108147399496637433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116655061405431599664424955 174982592108147399496637433)
  ·
    refine ⟨131236944081110549622478075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174982592108147399496637433 131236944081110549622478075)
    ·
      refine ⟨196855416121665824433717113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131236944081110549622478075 196855416121665824433717113)
      ·
        refine ⟨147641562091249368325287835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196855416121665824433717113 147641562091249368325287835)
        ·
          refine ⟨221462343136874052487931753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147641562091249368325287835 221462343136874052487931753)
          ·
            refine ⟨166096757352655539365948815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221462343136874052487931753 166096757352655539365948815)
            ·
              refine ⟨249145136028983309048923223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166096757352655539365948815 249145136028983309048923223)
              ·
                refine ⟨373717704043474963573384835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249145136028983309048923223 373717704043474963573384835)
                ·
                  refine ⟨560576556065212445360077253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373717704043474963573384835 560576556065212445360077253)
                  ·
                    refine ⟨105108104262227333505014485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 560576556065212445360077253 105108104262227333505014485)
                    ·
                      refine ⟨2463471193645953129023777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105108104262227333505014485 2463471193645953129023777)
                      ·
                        rfl

theorem cell23_4797593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_4797593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797593 prefixEnd_4797593 := by exact prefixLift 4797593
  have htrace : WordTrace (prefixWord ++ tailWord_4797593) baseStart_4797593 baseEnd_4797593 := by
    simpa [prefixWord, tailWord_4797593, baseEnd_4797593] using wordTrace_append hprefix tailTrace_4797593
  have hstable : (prefixWord ++ tailWord_4797593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797593).length < 2 ^ (prefixWord ++ tailWord_4797593).sum := by decide
  have hdescent : baseEnd_4797593 < baseStart_4797593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797607 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4797607 : Nat := 118140960795 + 4797607 * 2 ^ 59
def prefixEnd_4797607 : Nat := 4983230072969 + 3 ^ 40 * 4797607 * 2
def baseEnd_4797607 : Nat := 2463478382375116074248713

theorem tailTrace_4797607 : CollatzResearch.WordTrace tailWord_4797607 prefixEnd_4797607 2463478382375116074248713 := by
  unfold tailWord_4797607
  simp only [CollatzResearch.WordTrace]
  refine ⟨174983102730096679887647075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116655401820064453258431383 174983102730096679887647075)
  ·
    refine ⟨262474654095145019831470613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174983102730096679887647075 262474654095145019831470613)
    ·
      refine ⟨12303499410709922804600185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 262474654095145019831470613 12303499410709922804600185)
      ·
        refine ⟨9227624558032442103450139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12303499410709922804600185 9227624558032442103450139)
        ·
          refine ⟨13841436837048663155175209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9227624558032442103450139 13841436837048663155175209)
          ·
            refine ⟨10381077627786497366381407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13841436837048663155175209 10381077627786497366381407)
            ·
              refine ⟨15571616441679746049572111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10381077627786497366381407 15571616441679746049572111)
              ·
                refine ⟨23357424662519619074358167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15571616441679746049572111 23357424662519619074358167)
                ·
                  refine ⟨35036136993779428611537251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23357424662519619074358167 35036136993779428611537251)
                  ·
                    refine ⟨52554205490669142917305877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35036136993779428611537251 52554205490669142917305877)
                    ·
                      refine ⟨2463478382375116074248713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52554205490669142917305877 2463478382375116074248713)
                      ·
                        rfl

theorem cell23_4797607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4797607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797607 prefixEnd_4797607 := by exact prefixLift 4797607
  have htrace : WordTrace (prefixWord ++ tailWord_4797607) baseStart_4797607 baseEnd_4797607 := by
    simpa [prefixWord, tailWord_4797607, baseEnd_4797607] using wordTrace_append hprefix tailTrace_4797607
  have hstable : (prefixWord ++ tailWord_4797607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797607).length < 2 ^ (prefixWord ++ tailWord_4797607).sum := by decide
  have hdescent : baseEnd_4797607 < baseStart_4797607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797617 : List Nat := [1, 2, 2, 5, 1, 1, 4, 7]
def baseStart_4797617 : Nat := 118140960795 + 4797617 * 2 ^ 59
def prefixEnd_4797617 : Nat := 4983230072969 + 3 ^ 40 * 4797617 * 2
def baseEnd_4797617 : Nat := 91240130265987445745321

theorem tailTrace_4797617 : CollatzResearch.WordTrace tailWord_4797617 prefixEnd_4797617 91240130265987445745321 := by
  unfold tailWord_4797617
  simp only [CollatzResearch.WordTrace]
  refine ⟨174983467460060451595511105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116655644973373634397007403 174983467460060451595511105)
  ·
    refine ⟨131237600595045338696633329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174983467460060451595511105 131237600595045338696633329)
    ·
      refine ⟨98428200446284004022474997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131237600595045338696633329 98428200446284004022474997)
      ·
        refine ⟨9227643791839125377107031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98428200446284004022474997 9227643791839125377107031)
        ·
          refine ⟨13841465687758688065660547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9227643791839125377107031 13841465687758688065660547)
          ·
            refine ⟨20762198531638032098490821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13841465687758688065660547 20762198531638032098490821)
            ·
              refine ⟨3892912224682131018467029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20762198531638032098490821 3892912224682131018467029)
              ·
                refine ⟨91240130265987445745321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3892912224682131018467029 91240130265987445745321)
                ·
                  rfl

theorem cell23_4797617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 7].length) (baseStart_4797617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797617 prefixEnd_4797617 := by exact prefixLift 4797617
  have htrace : WordTrace (prefixWord ++ tailWord_4797617) baseStart_4797617 baseEnd_4797617 := by
    simpa [prefixWord, tailWord_4797617, baseEnd_4797617] using wordTrace_append hprefix tailTrace_4797617
  have hstable : (prefixWord ++ tailWord_4797617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797617).length < 2 ^ (prefixWord ++ tailWord_4797617).sum := by decide
  have hdescent : baseEnd_4797617 < baseStart_4797617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797622 : List Nat := [5, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_4797622 : Nat := 118140960795 + 4797622 * 2 ^ 59
def prefixEnd_4797622 : Nat := 4983230072969 + 3 ^ 40 * 4797622 * 2
def baseEnd_4797622 : Nat := 2463486084584933515561145

theorem tailTrace_4797622 : CollatzResearch.WordTrace tailWord_4797622 prefixEnd_4797622 2463486084584933515561145 := by
  unfold tailWord_4797622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10936478114065146090590195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116655766550028224966295413 10936478114065146090590195)
  ·
    refine ⟨16404717171097719135885293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10936478114065146090590195 16404717171097719135885293)
    ·
      refine ⟨6151768939161644675956985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16404717171097719135885293 6151768939161644675956985)
      ·
        refine ⟨4613826704371233506967739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6151768939161644675956985 4613826704371233506967739)
        ·
          refine ⟨6920740056556850260451609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4613826704371233506967739 6920740056556850260451609)
          ·
            refine ⟨5190555042417637695338707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6920740056556850260451609 5190555042417637695338707)
            ·
              refine ⟨7785832563626456543008061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5190555042417637695338707 7785832563626456543008061)
              ·
                refine ⟨2919687211359921203628023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7785832563626456543008061 2919687211359921203628023)
                ·
                  refine ⟨4379530817039881805442035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919687211359921203628023 4379530817039881805442035)
                  ·
                    refine ⟨6569296225559822708163053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4379530817039881805442035 6569296225559822708163053)
                    ·
                      refine ⟨2463486084584933515561145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6569296225559822708163053 2463486084584933515561145)
                      ·
                        rfl

theorem cell23_4797622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_4797622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797622 prefixEnd_4797622 := by exact prefixLift 4797622
  have htrace : WordTrace (prefixWord ++ tailWord_4797622) baseStart_4797622 baseEnd_4797622 := by
    simpa [prefixWord, tailWord_4797622, baseEnd_4797622] using wordTrace_append hprefix tailTrace_4797622
  have hstable : (prefixWord ++ tailWord_4797622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797622).length < 2 ^ (prefixWord ++ tailWord_4797622).sum := by decide
  have hdescent : baseEnd_4797622 < baseStart_4797622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797628 : List Nat := [2, 2, 2, 3, 2, 1, 3, 3, 1, 2, 2]
def baseStart_4797628 : Nat := 118140960795 + 4797628 * 2 ^ 59
def prefixEnd_4797628 : Nat := 4983230072969 + 3 ^ 40 * 4797628 * 2
def baseEnd_4797628 : Nat := 2463489165468860492086117

theorem tailTrace_4797628 : CollatzResearch.WordTrace tailWord_4797628 prefixEnd_4797628 2463489165468860492086117 := by
  unfold tailWord_4797628
  simp only [CollatzResearch.WordTrace]
  refine ⟨87491934331510300237080769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116655912442013733649441025 87491934331510300237080769)
  ·
    refine ⟨65618950748632725177810577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87491934331510300237080769 65618950748632725177810577)
    ·
      refine ⟨49214213061474543883357933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65618950748632725177810577 49214213061474543883357933)
      ·
        refine ⟨18455329898052953956259225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49214213061474543883357933 18455329898052953956259225)
        ·
          refine ⟨13841497423539715467194419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18455329898052953956259225 13841497423539715467194419)
          ·
            refine ⟨20762246135309573200791629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13841497423539715467194419 20762246135309573200791629)
            ·
              refine ⟨7785842300741089950296861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20762246135309573200791629 7785842300741089950296861)
              ·
                refine ⟨2919690862777908731361323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7785842300741089950296861 2919690862777908731361323)
                ·
                  refine ⟨4379536294166863097041985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919690862777908731361323 4379536294166863097041985)
                  ·
                    refine ⟨3284652220625147322781489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4379536294166863097041985 3284652220625147322781489)
                    ·
                      refine ⟨2463489165468860492086117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284652220625147322781489 2463489165468860492086117)
                      ·
                        rfl

theorem cell23_4797628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_4797628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797628 prefixEnd_4797628 := by exact prefixLift 4797628
  have htrace : WordTrace (prefixWord ++ tailWord_4797628) baseStart_4797628 baseEnd_4797628 := by
    simpa [prefixWord, tailWord_4797628, baseEnd_4797628] using wordTrace_append hprefix tailTrace_4797628
  have hstable : (prefixWord ++ tailWord_4797628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797628).length < 2 ^ (prefixWord ++ tailWord_4797628).sum := by decide
  have hdescent : baseEnd_4797628 < baseStart_4797628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797637 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 5, 3, 2]
def baseStart_4797637 : Nat := 118140960795 + 4797637 * 2 ^ 59
def prefixEnd_4797637 : Nat := 4983230072969 + 3 ^ 40 * 4797637 * 2
def baseEnd_4797637 : Nat := 2463493786794750956873575

theorem tailTrace_4797637 : CollatzResearch.WordTrace tailWord_4797637 prefixEnd_4797637 2463493786794750956873575 := by
  unfold tailWord_4797637
  simp only [CollatzResearch.WordTrace]
  refine ⟨174984196919987995011239165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116656131279991996674159443 174984196919987995011239165)
  ·
    refine ⟨65619073844995498129214687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174984196919987995011239165 65619073844995498129214687)
    ·
      refine ⟨98428610767493247193822031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65619073844995498129214687 98428610767493247193822031)
      ·
        refine ⟨147642916151239870790733047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98428610767493247193822031 147642916151239870790733047)
        ·
          refine ⟨221464374226859806186099571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147642916151239870790733047 221464374226859806186099571)
          ·
            refine ⟨332196561340289709279149357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221464374226859806186099571 332196561340289709279149357)
            ·
              refine ⟨124573710502608640979681009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332196561340289709279149357 124573710502608640979681009)
              ·
                refine ⟨93430282876956480734760757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124573710502608640979681009 93430282876956480734760757)
                ·
                  refine ⟨8759089019714670068883821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93430282876956480734760757 8759089019714670068883821)
                  ·
                    refine ⟨3284658382393001275831433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8759089019714670068883821 3284658382393001275831433)
                    ·
                      refine ⟨2463493786794750956873575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284658382393001275831433 2463493786794750956873575)
                      ·
                        rfl

theorem cell23_4797637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 3, 2].length) (baseStart_4797637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797637 prefixEnd_4797637 := by exact prefixLift 4797637
  have htrace : WordTrace (prefixWord ++ tailWord_4797637) baseStart_4797637 baseEnd_4797637 := by
    simpa [prefixWord, tailWord_4797637, baseEnd_4797637] using wordTrace_append hprefix tailTrace_4797637
  have hstable : (prefixWord ++ tailWord_4797637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797637).length < 2 ^ (prefixWord ++ tailWord_4797637).sum := by decide
  have hdescent : baseEnd_4797637 < baseStart_4797637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797671 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4797671 : Nat := 118140960795 + 4797671 * 2 ^ 59
def prefixEnd_4797671 : Nat := 4983230072969 + 3 ^ 40 * 4797671 * 2
def baseEnd_4797671 : Nat := 2463511245137003823848419

theorem tailTrace_4797671 : CollatzResearch.WordTrace tailWord_4797671 prefixEnd_4797671 2463511245137003823848419 := by
  unfold tailWord_4797671
  simp only [CollatzResearch.WordTrace]
  refine ⟨174985437001864818817976867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116656958001243212545317911 174985437001864818817976867)
  ·
    refine ⟨262478155502797228226965301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174985437001864818817976867 262478155502797228226965301)
    ·
      refine ⟨24607327078387240146277997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 262478155502797228226965301 24607327078387240146277997)
      ·
        refine ⟨9227747654395215054854249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24607327078387240146277997 9227747654395215054854249)
        ·
          refine ⟨6920810740796411291140687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9227747654395215054854249 6920810740796411291140687)
          ·
            refine ⟨10381216111194616936711031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6920810740796411291140687 10381216111194616936711031)
            ·
              refine ⟨15571824166791925405066547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10381216111194616936711031 15571824166791925405066547)
              ·
                refine ⟨23357736250187888107599821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15571824166791925405066547 23357736250187888107599821)
                ·
                  refine ⟨8759151093820458040349933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23357736250187888107599821 8759151093820458040349933)
                  ·
                    refine ⟨3284681660182671765131225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8759151093820458040349933 3284681660182671765131225)
                    ·
                      refine ⟨2463511245137003823848419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284681660182671765131225 2463511245137003823848419)
                      ·
                        rfl

theorem cell23_4797671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4797671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797671 prefixEnd_4797671 := by exact prefixLift 4797671
  have htrace : WordTrace (prefixWord ++ tailWord_4797671) baseStart_4797671 baseEnd_4797671 := by
    simpa [prefixWord, tailWord_4797671, baseEnd_4797671] using wordTrace_append hprefix tailTrace_4797671
  have hstable : (prefixWord ++ tailWord_4797671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797671).length < 2 ^ (prefixWord ++ tailWord_4797671).sum := by decide
  have hdescent : baseEnd_4797671 < baseStart_4797671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797680 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 4]
def baseStart_4797680 : Nat := 118140960795 + 4797680 * 2 ^ 59
def prefixEnd_4797680 : Nat := 4983230072969 + 3 ^ 40 * 4797680 * 2
def baseEnd_4797680 : Nat := 2463515866462894288635877

theorem tailTrace_4797680 : CollatzResearch.WordTrace tailWord_4797680 prefixEnd_4797680 2463515866462894288635877 := by
  unfold tailWord_4797680
  simp only [CollatzResearch.WordTrace]
  refine ⟨87492882629416106677527247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116657176839221475570036329 87492882629416106677527247)
  ·
    refine ⟨131239323944124160016290871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87492882629416106677527247 131239323944124160016290871)
    ·
      refine ⟨196858985916186240024436307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131239323944124160016290871 196858985916186240024436307)
      ·
        refine ⟨295288478874279360036654461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196858985916186240024436307 295288478874279360036654461)
        ·
          refine ⟨110733179577854760013745423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295288478874279360036654461 110733179577854760013745423)
          ·
            refine ⟨166099769366782140020618135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110733179577854760013745423 166099769366782140020618135)
            ·
              refine ⟨249149654050173210030927203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166099769366782140020618135 249149654050173210030927203)
              ·
                refine ⟨373724481075259815046390805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249149654050173210030927203 373724481075259815046390805)
                ·
                  refine ⟨17518335050402803830299569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 373724481075259815046390805 17518335050402803830299569)
                  ·
                    refine ⟨13138751287802102872724677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17518335050402803830299569 13138751287802102872724677)
                    ·
                      refine ⟨2463515866462894288635877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13138751287802102872724677 2463515866462894288635877)
                      ·
                        rfl

theorem cell23_4797680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_4797680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797680 prefixEnd_4797680 := by exact prefixLift 4797680
  have htrace : WordTrace (prefixWord ++ tailWord_4797680) baseStart_4797680 baseEnd_4797680 := by
    simpa [prefixWord, tailWord_4797680, baseEnd_4797680] using wordTrace_append hprefix tailTrace_4797680
  have hstable : (prefixWord ++ tailWord_4797680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797680).length < 2 ^ (prefixWord ++ tailWord_4797680).sum := by decide
  have hdescent : baseEnd_4797680 < baseStart_4797680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797701 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 2, 2, 2]
def baseStart_4797701 : Nat := 118140960795 + 4797701 * 2 ^ 59
def prefixEnd_4797701 : Nat := 4983230072969 + 3 ^ 40 * 4797701 * 2
def baseEnd_4797701 : Nat := 2463526649556638706473281

theorem tailTrace_4797701 : CollatzResearch.WordTrace tailWord_4797701 prefixEnd_4797701 2463526649556638706473281 := by
  unfold tailWord_4797701
  simp only [CollatzResearch.WordTrace]
  refine ⟨174986531191756133941568957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116657687461170755961045971 174986531191756133941568957)
  ·
    refine ⟨65619949196908550228088359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174986531191756133941568957 65619949196908550228088359)
    ·
      refine ⟨98429923795362825342132539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65619949196908550228088359 98429923795362825342132539)
      ·
        refine ⟨147644885693044238013198809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98429923795362825342132539 147644885693044238013198809)
        ·
          refine ⟨110733664269783178509899107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147644885693044238013198809 110733664269783178509899107)
          ·
            refine ⟨166100496404674767764848661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110733664269783178509899107 166100496404674767764848661)
            ·
              refine ⟨7785960768969129738977281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166100496404674767764848661 7785960768969129738977281)
              ·
                refine ⟨5839470576726847304232961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7785960768969129738977281 5839470576726847304232961)
                ·
                  refine ⟨4379602932545135478174721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5839470576726847304232961 4379602932545135478174721)
                  ·
                    refine ⟨3284702199408851608631041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4379602932545135478174721 3284702199408851608631041)
                    ·
                      refine ⟨2463526649556638706473281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284702199408851608631041 2463526649556638706473281)
                      ·
                        rfl

theorem cell23_4797701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 2, 2].length) (baseStart_4797701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797701 prefixEnd_4797701 := by exact prefixLift 4797701
  have htrace : WordTrace (prefixWord ++ tailWord_4797701) baseStart_4797701 baseEnd_4797701 := by
    simpa [prefixWord, tailWord_4797701, baseEnd_4797701] using wordTrace_append hprefix tailTrace_4797701
  have hstable : (prefixWord ++ tailWord_4797701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797701).length < 2 ^ (prefixWord ++ tailWord_4797701).sum := by decide
  have hdescent : baseEnd_4797701 < baseStart_4797701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797741 : List Nat := [1, 5, 3, 1, 1, 1, 1, 5, 5]
def baseStart_4797741 : Nat := 118140960795 + 4797741 * 2 ^ 59
def prefixEnd_4797741 : Nat := 4983230072969 + 3 ^ 40 * 4797741 * 2
def baseEnd_4797741 : Nat := 273727465420313172219233

theorem tailTrace_4797741 : CollatzResearch.WordTrace tailWord_4797741 prefixEnd_4797741 273727465420313172219233 := by
  unfold tailWord_4797741
  simp only [CollatzResearch.WordTrace]
  refine ⟨174987990111611220773025077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116658660074407480515350051 174987990111611220773025077)
  ·
    refine ⟨16405124072963551947471101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174987990111611220773025077 16405124072963551947471101)
    ·
      refine ⟨6151921527361331980301663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16405124072963551947471101 6151921527361331980301663)
      ·
        refine ⟨9227882291041997970452495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6151921527361331980301663 9227882291041997970452495)
        ·
          refine ⟨13841823436562996955678743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9227882291041997970452495 13841823436562996955678743)
          ·
            refine ⟨20762735154844495433518115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13841823436562996955678743 20762735154844495433518115)
            ·
              refine ⟨31144102732266743150277173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20762735154844495433518115 31144102732266743150277173)
              ·
                refine ⟨2919759631150007170338485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31144102732266743150277173 2919759631150007170338485)
                ·
                  refine ⟨273727465420313172219233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2919759631150007170338485 273727465420313172219233)
                  ·
                    rfl

theorem cell23_4797741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_4797741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797741 prefixEnd_4797741 := by exact prefixLift 4797741
  have htrace : WordTrace (prefixWord ++ tailWord_4797741) baseStart_4797741 baseEnd_4797741 := by
    simpa [prefixWord, tailWord_4797741, baseEnd_4797741] using wordTrace_append hprefix tailTrace_4797741
  have hstable : (prefixWord ++ tailWord_4797741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797741).length < 2 ^ (prefixWord ++ tailWord_4797741).sum := by decide
  have hdescent : baseEnd_4797741 < baseStart_4797741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797774 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2]
def baseStart_4797774 : Nat := 118140960795 + 4797774 * 2 ^ 59
def prefixEnd_4797774 : Nat := 4983230072969 + 3 ^ 40 * 4797774 * 2
def baseEnd_4797774 : Nat := 2463564133644416920860445

theorem tailTrace_4797774 : CollatzResearch.WordTrace tailWord_4797774 prefixEnd_4797774 2463564133644416920860445 := by
  unfold tailWord_4797774
  simp only [CollatzResearch.WordTrace]
  refine ⟨21873649215061458426122047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116659462480327778272650917 21873649215061458426122047)
  ·
    refine ⟨32810473822592187639183071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21873649215061458426122047 32810473822592187639183071)
    ·
      refine ⟨49215710733888281458774607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32810473822592187639183071 49215710733888281458774607)
      ·
        refine ⟨73823566100832422188161911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49215710733888281458774607 73823566100832422188161911)
        ·
          refine ⟨110735349151248633282242867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73823566100832422188161911 110735349151248633282242867)
          ·
            refine ⟨166103023726872949923364301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110735349151248633282242867 166103023726872949923364301)
            ·
              refine ⟨62288633897577356221261613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166103023726872949923364301 62288633897577356221261613)
              ·
                refine ⟨23358237711591508582973105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62288633897577356221261613 23358237711591508582973105)
                ·
                  refine ⟨17518678283693631437229829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23358237711591508582973105 17518678283693631437229829)
                  ·
                    refine ⟨3284752178192555894480593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17518678283693631437229829 3284752178192555894480593)
                    ·
                      refine ⟨2463564133644416920860445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284752178192555894480593 2463564133644416920860445)
                      ·
                        rfl

theorem cell23_4797774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_4797774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797774 prefixEnd_4797774 := by exact prefixLift 4797774
  have htrace : WordTrace (prefixWord ++ tailWord_4797774) baseStart_4797774 baseEnd_4797774 := by
    simpa [prefixWord, tailWord_4797774, baseEnd_4797774] using wordTrace_append hprefix tailTrace_4797774
  have hstable : (prefixWord ++ tailWord_4797774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797774).length < 2 ^ (prefixWord ++ tailWord_4797774).sum := by decide
  have hdescent : baseEnd_4797774 < baseStart_4797774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797777 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 3, 4, 3]
def baseStart_4797777 : Nat := 118140960795 + 4797777 * 2 ^ 59
def prefixEnd_4797777 : Nat := 4983230072969 + 3 ^ 40 * 4797777 * 2
def baseEnd_4797777 : Nat := 2463565674086380409122931

theorem tailTrace_4797777 : CollatzResearch.WordTrace tailWord_4797777 prefixEnd_4797777 2463565674086380409122931 := by
  unfold tailWord_4797777
  simp only [CollatzResearch.WordTrace]
  refine ⟨174989303139480798921335585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116659535426320532614223723 174989303139480798921335585)
  ·
    refine ⟨131241977354610599191001689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174989303139480798921335585 131241977354610599191001689)
    ·
      refine ⟨98431483015957949393251267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131241977354610599191001689 98431483015957949393251267)
      ·
        refine ⟨147647224523936924089876901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98431483015957949393251267 147647224523936924089876901)
        ·
          refine ⟨27683854598238173266851919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147647224523936924089876901 27683854598238173266851919)
          ·
            refine ⟨41525781897357259900277879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27683854598238173266851919 41525781897357259900277879)
            ·
              refine ⟨62288672846035889850416819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41525781897357259900277879 62288672846035889850416819)
              ·
                refine ⟨93433009269053834775625229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62288672846035889850416819 93433009269053834775625229)
                ·
                  refine ⟨35037378475895188040859461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93433009269053834775625229 35037378475895188040859461)
                  ·
                    refine ⟨6569508464230347757661149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35037378475895188040859461 6569508464230347757661149)
                    ·
                      refine ⟨2463565674086380409122931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6569508464230347757661149 2463565674086380409122931)
                      ·
                        rfl

theorem cell23_4797777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_4797777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797777 prefixEnd_4797777 := by exact prefixLift 4797777
  have htrace : WordTrace (prefixWord ++ tailWord_4797777) baseStart_4797777 baseEnd_4797777 := by
    simpa [prefixWord, tailWord_4797777, baseEnd_4797777] using wordTrace_append hprefix tailTrace_4797777
  have hstable : (prefixWord ++ tailWord_4797777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797777).length < 2 ^ (prefixWord ++ tailWord_4797777).sum := by decide
  have hdescent : baseEnd_4797777 < baseStart_4797777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797794 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_4797794 : Nat := 118140960795 + 4797794 * 2 ^ 59
def prefixEnd_4797794 : Nat := 4983230072969 + 3 ^ 40 * 4797794 * 2
def baseEnd_4797794 : Nat := 2463574403257506842610353

theorem tailTrace_4797794 : CollatzResearch.WordTrace tailWord_4797794 prefixEnd_4797794 2463574403257506842610353 := by
  unfold tailWord_4797794
  simp only [CollatzResearch.WordTrace]
  refine ⟨43747480795104802706176109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116659948786946140549802957 43747480795104802706176109)
  ·
    refine ⟨16405305298164301014816041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43747480795104802706176109 16405305298164301014816041)
    ·
      refine ⟨12303978973623225761112031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16405305298164301014816041 12303978973623225761112031)
      ·
        refine ⟨18455968460434838641668047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12303978973623225761112031 18455968460434838641668047)
        ·
          refine ⟨27683952690652257962502071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18455968460434838641668047 27683952690652257962502071)
          ·
            refine ⟨41525929035978386943753107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27683952690652257962502071 41525929035978386943753107)
            ·
              refine ⟨62288893553967580415629661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41525929035978386943753107 62288893553967580415629661)
              ·
                refine ⟨23358335082737842655861123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62288893553967580415629661 23358335082737842655861123)
                ·
                  refine ⟨35037502624106763983791685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23358335082737842655861123 35037502624106763983791685)
                  ·
                    refine ⟨6569531742020018246960941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35037502624106763983791685 6569531742020018246960941)
                    ·
                      refine ⟨2463574403257506842610353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6569531742020018246960941 2463574403257506842610353)
                      ·
                        rfl

theorem cell23_4797794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_4797794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797794 prefixEnd_4797794 := by exact prefixLift 4797794
  have htrace : WordTrace (prefixWord ++ tailWord_4797794) baseStart_4797794 baseEnd_4797794 := by
    simpa [prefixWord, tailWord_4797794, baseEnd_4797794] using wordTrace_append hprefix tailTrace_4797794
  have hstable : (prefixWord ++ tailWord_4797794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797794).length < 2 ^ (prefixWord ++ tailWord_4797794).sum := by decide
  have hdescent : baseEnd_4797794 < baseStart_4797794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797831 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 6]
def baseStart_4797831 : Nat := 118140960795 + 4797831 * 2 ^ 59
def prefixEnd_4797831 : Nat := 4983230072969 + 3 ^ 40 * 4797831 * 2
def baseEnd_4797831 : Nat := 273732600226858133094187

theorem tailTrace_4797831 : CollatzResearch.WordTrace tailWord_4797831 prefixEnd_4797831 273732600226858133094187 := by
  unfold tailWord_4797831
  simp only [CollatzResearch.WordTrace]
  refine ⟨174991272681285166143801347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116660848454190110762534231 174991272681285166143801347)
  ·
    refine ⟨262486909021927749215702021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174991272681285166143801347 262486909021927749215702021)
    ·
      refine ⟨49216295441611452977944129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262486909021927749215702021 49216295441611452977944129)
      ·
        refine ⟨36912221581208589733458097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49216295441611452977944129 36912221581208589733458097)
        ·
          refine ⟨27684166185906442300093573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36912221581208589733458097 27684166185906442300093573)
          ·
            refine ⟨5190781159857457931267545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27684166185906442300093573 5190781159857457931267545)
            ·
              refine ⟨3893085869893093448450659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5190781159857457931267545 3893085869893093448450659)
              ·
                refine ⟨5839628804839640172675989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3893085869893093448450659 5839628804839640172675989)
                ·
                  refine ⟨273732600226858133094187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5839628804839640172675989 273732600226858133094187)
                  ·
                    rfl

theorem cell23_4797831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 6].length) (baseStart_4797831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797831 prefixEnd_4797831 := by exact prefixLift 4797831
  have htrace : WordTrace (prefixWord ++ tailWord_4797831) baseStart_4797831 baseEnd_4797831 := by
    simpa [prefixWord, tailWord_4797831, baseEnd_4797831] using wordTrace_append hprefix tailTrace_4797831
  have hstable : (prefixWord ++ tailWord_4797831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797831).length < 2 ^ (prefixWord ++ tailWord_4797831).sum := by decide
  have hdescent : baseEnd_4797831 < baseStart_4797831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797867 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 3]
def baseStart_4797867 : Nat := 118140960795 + 4797867 * 2 ^ 59
def prefixEnd_4797867 : Nat := 4983230072969 + 3 ^ 40 * 4797867 * 2
def baseEnd_4797867 : Nat := 2463611887345285056997517

theorem tailTrace_4797867 : CollatzResearch.WordTrace tailWord_4797867 prefixEnd_4797867 2463611887345285056997517 := by
  unfold tailWord_4797867
  simp only [CollatzResearch.WordTrace]
  refine ⟨174992585709154744292111855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116661723806103162861407903 174992585709154744292111855)
  ·
    refine ⟨262488878563732116438167783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174992585709154744292111855 262488878563732116438167783)
    ·
      refine ⟨393733317845598174657251675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262488878563732116438167783 393733317845598174657251675)
      ·
        refine ⟨590599976768397261985877513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393733317845598174657251675 590599976768397261985877513)
        ·
          refine ⟨442949982576297946489408135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 590599976768397261985877513 442949982576297946489408135)
          ·
            refine ⟨664424973864446919734112203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442949982576297946489408135 664424973864446919734112203)
            ·
              refine ⟨996637460796670379601168305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664424973864446919734112203 996637460796670379601168305)
              ·
                refine ⟨747478095597502784700876229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 996637460796670379601168305 747478095597502784700876229)
                ·
                  refine ⟨140152142924531772131414293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 747478095597502784700876229 140152142924531772131414293)
                  ·
                    refine ⟨6569631699587426818660045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 140152142924531772131414293 6569631699587426818660045)
                    ·
                      refine ⟨2463611887345285056997517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6569631699587426818660045 2463611887345285056997517)
                      ·
                        rfl

theorem cell23_4797867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 3].length) (baseStart_4797867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797867 prefixEnd_4797867 := by exact prefixLift 4797867
  have htrace : WordTrace (prefixWord ++ tailWord_4797867) baseStart_4797867 baseEnd_4797867 := by
    simpa [prefixWord, tailWord_4797867, baseEnd_4797867] using wordTrace_append hprefix tailTrace_4797867
  have hstable : (prefixWord ++ tailWord_4797867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797867).length < 2 ^ (prefixWord ++ tailWord_4797867).sum := by decide
  have hdescent : baseEnd_4797867 < baseStart_4797867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797898 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2]
def baseStart_4797898 : Nat := 118140960795 + 4797898 * 2 ^ 59
def prefixEnd_4797898 : Nat := 4983230072969 + 3 ^ 40 * 4797898 * 2
def baseEnd_4797898 : Nat := 2463627805245574435709875

theorem tailTrace_4797898 : CollatzResearch.WordTrace tailWord_4797898 prefixEnd_4797898 2463627805245574435709875 := by
  unfold tailWord_4797898
  simp only [CollatzResearch.WordTrace]
  refine ⟨43748429093010609146622587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116662477581361624390993565 43748429093010609146622587)
  ·
    refine ⟨65622643639515913719933881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43748429093010609146622587 65622643639515913719933881)
    ·
      refine ⟨49216982729636935289950411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65622643639515913719933881 49216982729636935289950411)
      ·
        refine ⟨73825474094455402934925617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49216982729636935289950411 73825474094455402934925617)
        ·
          refine ⟨55369105570841552201194213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73825474094455402934925617 55369105570841552201194213)
          ·
            refine ⟨10381707294532791037723915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55369105570841552201194213 10381707294532791037723915)
            ·
              refine ⟨15572560941799186556585873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10381707294532791037723915 15572560941799186556585873)
              ·
                refine ⟨11679420706349389917439405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15572560941799186556585873 11679420706349389917439405)
                ·
                  refine ⟨4379782764881021219039777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11679420706349389917439405 4379782764881021219039777)
                  ·
                    refine ⟨3284837073660765914279833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4379782764881021219039777 3284837073660765914279833)
                    ·
                      refine ⟨2463627805245574435709875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284837073660765914279833 2463627805245574435709875)
                      ·
                        rfl

theorem cell23_4797898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_4797898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797898 prefixEnd_4797898 := by exact prefixLift 4797898
  have htrace : WordTrace (prefixWord ++ tailWord_4797898) baseStart_4797898 baseEnd_4797898 := by
    simpa [prefixWord, tailWord_4797898, baseEnd_4797898] using wordTrace_append hprefix tailTrace_4797898
  have hstable : (prefixWord ++ tailWord_4797898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797898).length < 2 ^ (prefixWord ++ tailWord_4797898).sum := by decide
  have hdescent : baseEnd_4797898 < baseStart_4797898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797931 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 2, 1, 3]
def baseStart_4797931 : Nat := 118140960795 + 4797931 * 2 ^ 59
def prefixEnd_4797931 : Nat := 4983230072969 + 3 ^ 40 * 4797931 * 2
def baseEnd_4797931 : Nat := 2463644750107172806597223

theorem tailTrace_4797931 : CollatzResearch.WordTrace tailWord_4797931 prefixEnd_4797931 2463644750107172806597223 := by
  unfold tailWord_4797931
  simp only [CollatzResearch.WordTrace]
  refine ⟨174994919980922883222441647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116663279987281922148294431 174994919980922883222441647)
  ·
    refine ⟨262492379971384324833662471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174994919980922883222441647 262492379971384324833662471)
    ·
      refine ⟨393738569957076487250493707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262492379971384324833662471 393738569957076487250493707)
      ·
        refine ⟨590607854935614730875740561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393738569957076487250493707 590607854935614730875740561)
        ·
          refine ⟨442955891201711048156805421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 590607854935614730875740561 442955891201711048156805421)
          ·
            refine ⟨166108459200641643058802033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 442955891201711048156805421 166108459200641643058802033)
            ·
              refine ⟨124581344400481232294101525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166108459200641643058802033 124581344400481232294101525)
              ·
                refine ⟨5839750518772557763786009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124581344400481232294101525 5839750518772557763786009)
                ·
                  refine ⟨4379812889079418322839507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5839750518772557763786009 4379812889079418322839507)
                  ·
                    refine ⟨6569719333619127484259261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4379812889079418322839507 6569719333619127484259261)
                    ·
                      refine ⟨2463644750107172806597223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6569719333619127484259261 2463644750107172806597223)
                      ·
                        rfl

theorem cell23_4797931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 1, 3].length) (baseStart_4797931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797931 prefixEnd_4797931 := by exact prefixLift 4797931
  have htrace : WordTrace (prefixWord ++ tailWord_4797931) baseStart_4797931 baseEnd_4797931 := by
    simpa [prefixWord, tailWord_4797931, baseEnd_4797931] using wordTrace_append hprefix tailTrace_4797931
  have hstable : (prefixWord ++ tailWord_4797931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797931).length < 2 ^ (prefixWord ++ tailWord_4797931).sum := by decide
  have hdescent : baseEnd_4797931 < baseStart_4797931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797967 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_4797967 : Nat := 118140960795 + 4797967 * 2 ^ 59
def prefixEnd_4797967 : Nat := 4983230072969 + 3 ^ 40 * 4797967 * 2
def baseEnd_4797967 : Nat := 2463663235410734665747057

theorem tailTrace_4797967 : CollatzResearch.WordTrace tailWord_4797967 prefixEnd_4797967 2463663235410734665747057 := by
  unfold tailWord_4797967
  simp only [CollatzResearch.WordTrace]
  refine ⟨174996233008792461370752155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116664155339194974247168103 174996233008792461370752155)
  ·
    refine ⟨262494349513188692056128233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174996233008792461370752155 262494349513188692056128233)
    ·
      refine ⟨196870762134891519042096175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262494349513188692056128233 196870762134891519042096175)
      ·
        refine ⟨295306143202337278563144263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196870762134891519042096175 295306143202337278563144263)
        ·
          refine ⟨442959214803505917844716395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295306143202337278563144263 442959214803505917844716395)
          ·
            refine ⟨664438822205258876767074593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442959214803505917844716395 664438822205258876767074593)
            ·
              refine ⟨498329116653944157575305945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664438822205258876767074593 498329116653944157575305945)
              ·
                refine ⟨373746837490458118181479459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498329116653944157575305945 373746837490458118181479459)
                ·
                  refine ⟨560620256235687177272219189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373746837490458118181479459 560620256235687177272219189)
                  ·
                    refine ⟨52558149022095672869270549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 560620256235687177272219189 52558149022095672869270549)
                    ·
                      refine ⟨2463663235410734665747057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52558149022095672869270549 2463663235410734665747057)
                      ·
                        rfl

theorem cell23_4797967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_4797967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797967 prefixEnd_4797967 := by exact prefixLift 4797967
  have htrace : WordTrace (prefixWord ++ tailWord_4797967) baseStart_4797967 baseEnd_4797967 := by
    simpa [prefixWord, tailWord_4797967, baseEnd_4797967] using wordTrace_append hprefix tailTrace_4797967
  have hstable : (prefixWord ++ tailWord_4797967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797967).length < 2 ^ (prefixWord ++ tailWord_4797967).sum := by decide
  have hdescent : baseEnd_4797967 < baseStart_4797967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798005 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_4798005 : Nat := 118140960795 + 4798005 * 2 ^ 59
def prefixEnd_4798005 : Nat := 4983230072969 + 3 ^ 40 * 4798005 * 2
def baseEnd_4798005 : Nat := 2463682747675605517071883

theorem tailTrace_4798005 : CollatzResearch.WordTrace tailWord_4798005 prefixEnd_4798005 2463682747675605517071883 := by
  unfold tailWord_4798005
  simp only [CollatzResearch.WordTrace]
  refine ⟨174997618982654793860635469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116665079321769862573756979 174997618982654793860635469)
  ·
    refine ⟨65624107118495547697738301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174997618982654793860635469 65624107118495547697738301)
    ·
      refine ⟨24609040169435830386651863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65624107118495547697738301 24609040169435830386651863)
      ·
        refine ⟨36913560254153745579977795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24609040169435830386651863 36913560254153745579977795)
        ·
          refine ⟨55370340381230618369966693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36913560254153745579977795 55370340381230618369966693)
          ·
            refine ⟨10381938821480740944368755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55370340381230618369966693 10381938821480740944368755)
            ·
              refine ⟨15572908232221111416553133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10381938821480740944368755 15572908232221111416553133)
              ·
                refine ⟨5839840587082916781207425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15572908232221111416553133 5839840587082916781207425)
                ·
                  refine ⟨4379880440312187585905569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5839840587082916781207425 4379880440312187585905569)
                  ·
                    refine ⟨3284910330234140689429177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4379880440312187585905569 3284910330234140689429177)
                    ·
                      refine ⟨2463682747675605517071883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284910330234140689429177 2463682747675605517071883)
                      ·
                        rfl

theorem cell23_4798005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_4798005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798005 prefixEnd_4798005 := by exact prefixLift 4798005
  have htrace : WordTrace (prefixWord ++ tailWord_4798005) baseStart_4798005 baseEnd_4798005 := by
    simpa [prefixWord, tailWord_4798005, baseEnd_4798005] using wordTrace_append hprefix tailTrace_4798005
  have hstable : (prefixWord ++ tailWord_4798005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798005).length < 2 ^ (prefixWord ++ tailWord_4798005).sum := by decide
  have hdescent : baseEnd_4798005 < baseStart_4798005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798022 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_4798022 : Nat := 118140960795 + 4798022 * 2 ^ 59
def prefixEnd_4798022 : Nat := 4983230072969 + 3 ^ 40 * 4798022 * 2
def baseEnd_4798022 : Nat := 2463691476846731950559305

theorem tailTrace_4798022 : CollatzResearch.WordTrace tailWord_4798022 prefixEnd_4798022 2463691476846731950559305 := by
  unfold tailWord_4798022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468694969487287680125135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116665492682395470509336213 5468694969487287680125135)
  ·
    refine ⟨8203042454230931520187703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5468694969487287680125135 8203042454230931520187703)
    ·
      refine ⟨12304563681346397280281555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8203042454230931520187703 12304563681346397280281555)
      ·
        refine ⟨18456845522019595920422333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12304563681346397280281555 18456845522019595920422333)
        ·
          refine ⟨6921317070757348470158375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18456845522019595920422333 6921317070757348470158375)
          ·
            refine ⟨10381975606136022705237563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6921317070757348470158375 10381975606136022705237563)
            ·
              refine ⟨15572963409204034057856345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10381975606136022705237563 15572963409204034057856345)
              ·
                refine ⟨11679722556903025543392259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15572963409204034057856345 11679722556903025543392259)
                ·
                  refine ⟨17519583835354538315088389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11679722556903025543392259 17519583835354538315088389)
                  ·
                    refine ⟨3284921969128975934079073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17519583835354538315088389 3284921969128975934079073)
                    ·
                      refine ⟨2463691476846731950559305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284921969128975934079073 2463691476846731950559305)
                      ·
                        rfl

theorem cell23_4798022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_4798022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798022 prefixEnd_4798022 := by exact prefixLift 4798022
  have htrace : WordTrace (prefixWord ++ tailWord_4798022) baseStart_4798022 baseEnd_4798022 := by
    simpa [prefixWord, tailWord_4798022, baseEnd_4798022] using wordTrace_append hprefix tailTrace_4798022
  have hstable : (prefixWord ++ tailWord_4798022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798022).length < 2 ^ (prefixWord ++ tailWord_4798022).sum := by decide
  have hdescent : baseEnd_4798022 < baseStart_4798022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798074 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_4798074 : Nat := 118140960795 + 4798074 * 2 ^ 59
def prefixEnd_4798074 : Nat := 4983230072969 + 3 ^ 40 * 4798074 * 2
def baseEnd_4798074 : Nat := 2463718177840765747109065

theorem tailTrace_4798074 : CollatzResearch.WordTrace tailWord_4798074 prefixEnd_4798074 2463718177840765747109065 := by
  unfold tailWord_4798074
  simp only [CollatzResearch.WordTrace]
  refine ⟨43750033904851204661224319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116666757079603212429931517 43750033904851204661224319)
  ·
    refine ⟨65625050857276806991836479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43750033904851204661224319 65625050857276806991836479)
    ·
      refine ⟨98437576285915210487754719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65625050857276806991836479 98437576285915210487754719)
      ·
        refine ⟨147656364428872815731632079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98437576285915210487754719 147656364428872815731632079)
        ·
          refine ⟨221484546643309223597448119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147656364428872815731632079 221484546643309223597448119)
          ·
            refine ⟨332226819964963835396172179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221484546643309223597448119 332226819964963835396172179)
            ·
              refine ⟨498340229947445753094258269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332226819964963835396172179 498340229947445753094258269)
              ·
                refine ⟨186877586230292157410346851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 498340229947445753094258269 186877586230292157410346851)
                ·
                  refine ⟨280316379345438236115520277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186877586230292157410346851 280316379345438236115520277)
                  ·
                    refine ⟨13139830281817417317915013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 280316379345438236115520277 13139830281817417317915013)
                    ·
                      refine ⟨2463718177840765747109065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13139830281817417317915013 2463718177840765747109065)
                      ·
                        rfl

theorem cell23_4798074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_4798074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798074 prefixEnd_4798074 := by exact prefixLift 4798074
  have htrace : WordTrace (prefixWord ++ tailWord_4798074) baseStart_4798074 baseEnd_4798074 := by
    simpa [prefixWord, tailWord_4798074, baseEnd_4798074] using wordTrace_append hprefix tailTrace_4798074
  have hstable : (prefixWord ++ tailWord_4798074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798074).length < 2 ^ (prefixWord ++ tailWord_4798074).sum := by decide
  have hdescent : baseEnd_4798074 < baseStart_4798074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798128 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 3, 1, 3]
def baseStart_4798128 : Nat := 118140960795 + 4798128 * 2 ^ 59
def prefixEnd_4798128 : Nat := 4983230072969 + 3 ^ 40 * 4798128 * 2
def baseEnd_4798128 : Nat := 2463745905796108535833817

theorem tailTrace_4798128 : CollatzResearch.WordTrace tailWord_4798128 prefixEnd_4798128 2463745905796108535833817 := by
  unfold tailWord_4798128
  simp only [CollatzResearch.WordTrace]
  refine ⟨87501052580604592933681519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116668070107472790578242025 87501052580604592933681519)
  ·
    refine ⟨131251578870906889400522279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87501052580604592933681519 131251578870906889400522279)
    ·
      refine ⟨196877368306360334100783419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131251578870906889400522279 196877368306360334100783419)
      ·
        refine ⟨295316052459540501151175129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196877368306360334100783419 295316052459540501151175129)
        ·
          refine ⟨221487039344655375863381347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295316052459540501151175129 221487039344655375863381347)
          ·
            refine ⟨332230559016983063795072021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221487039344655375863381347 332230559016983063795072021)
            ·
              refine ⟨15573307453921081115394001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 332230559016983063795072021 15573307453921081115394001)
              ·
                refine ⟨11679980590440810836545501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15573307453921081115394001 11679980590440810836545501)
                ·
                  refine ⟨4379992721415304063704563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11679980590440810836545501 4379992721415304063704563)
                  ·
                    refine ⟨6569989082122956095556845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4379992721415304063704563 6569989082122956095556845)
                    ·
                      refine ⟨2463745905796108535833817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6569989082122956095556845 2463745905796108535833817)
                      ·
                        rfl

theorem cell23_4798128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3, 1, 3].length) (baseStart_4798128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798128 prefixEnd_4798128 := by exact prefixLift 4798128
  have htrace : WordTrace (prefixWord ++ tailWord_4798128) baseStart_4798128 baseEnd_4798128 := by
    simpa [prefixWord, tailWord_4798128, baseEnd_4798128] using wordTrace_append hprefix tailTrace_4798128
  have hstable : (prefixWord ++ tailWord_4798128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798128).length < 2 ^ (prefixWord ++ tailWord_4798128).sum := by decide
  have hdescent : baseEnd_4798128 < baseStart_4798128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798138 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2]
def baseStart_4798138 : Nat := 118140960795 + 4798138 * 2 ^ 59
def prefixEnd_4798138 : Nat := 4983230072969 + 3 ^ 40 * 4798138 * 2
def baseEnd_4798138 : Nat := 2463751040602653496708771

theorem tailTrace_4798138 : CollatzResearch.WordTrace tailWord_4798138 prefixEnd_4798138 2463751040602653496708771 := by
  unfold tailWord_4798138
  simp only [CollatzResearch.WordTrace]
  refine ⟨43750617472793239393806767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116668313260781971716818045 43750617472793239393806767)
  ·
    refine ⟨65625926209189859090710151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43750617472793239393806767 65625926209189859090710151)
    ·
      refine ⟨98438889313784788636065227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65625926209189859090710151 98438889313784788636065227)
      ·
        refine ⟨147658333970677182954097841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98438889313784788636065227 147658333970677182954097841)
        ·
          refine ⟨110743750478007887215573381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147658333970677182954097841 110743750478007887215573381)
          ·
            refine ⟨20764453214626478852920009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110743750478007887215573381 20764453214626478852920009)
            ·
              refine ⟨15573339910969859139690007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20764453214626478852920009 15573339910969859139690007)
              ·
                refine ⟨23360009866454788709535011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15573339910969859139690007 23360009866454788709535011)
                ·
                  refine ⟨35040014799682183064302517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23360009866454788709535011 35040014799682183064302517)
                  ·
                    refine ⟨3285001387470204662278361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35040014799682183064302517 3285001387470204662278361)
                    ·
                      refine ⟨2463751040602653496708771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285001387470204662278361 2463751040602653496708771)
                      ·
                        rfl

theorem cell23_4798138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2].length) (baseStart_4798138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798138 prefixEnd_4798138 := by exact prefixLift 4798138
  have htrace : WordTrace (prefixWord ++ tailWord_4798138) baseStart_4798138 baseEnd_4798138 := by
    simpa [prefixWord, tailWord_4798138, baseEnd_4798138] using wordTrace_append hprefix tailTrace_4798138
  have hstable : (prefixWord ++ tailWord_4798138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798138).length < 2 ^ (prefixWord ++ tailWord_4798138).sum := by decide
  have hdescent : baseEnd_4798138 < baseStart_4798138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798148 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_4798148 : Nat := 118140960795 + 4798148 * 2 ^ 59
def prefixEnd_4798148 : Nat := 4983230072969 + 3 ^ 40 * 4798148 * 2
def baseEnd_4798148 : Nat := 821252058469732819194575

theorem tailTrace_4798148 : CollatzResearch.WordTrace tailWord_4798148 prefixEnd_4798148 821252058469732819194575 := by
  unfold tailWord_4798148
  simp only [CollatzResearch.WordTrace]
  refine ⟨87501417310568364641545549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116668556414091152855394065 87501417310568364641545549)
  ·
    refine ⟨32813031491463136740579581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87501417310568364641545549 32813031491463136740579581)
    ·
      refine ⟨12304886809298676277717343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32813031491463136740579581 12304886809298676277717343)
      ·
        refine ⟨18457330213948014416576015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12304886809298676277717343 18457330213948014416576015)
        ·
          refine ⟨27685995320922021624864023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18457330213948014416576015 27685995320922021624864023)
          ·
            refine ⟨41528992981383032437296035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27685995320922021624864023 41528992981383032437296035)
            ·
              refine ⟨62293489472074548655944053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41528992981383032437296035 62293489472074548655944053)
              ·
                refine ⟨5840014638006988936494755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62293489472074548655944053 5840014638006988936494755)
                ·
                  refine ⟨8760021957010483404742133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5840014638006988936494755 8760021957010483404742133)
                  ·
                    refine ⟨821252058469732819194575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8760021957010483404742133 821252058469732819194575)
                    ·
                      rfl

theorem cell23_4798148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_4798148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798148 prefixEnd_4798148 := by exact prefixLift 4798148
  have htrace : WordTrace (prefixWord ++ tailWord_4798148) baseStart_4798148 baseEnd_4798148 := by
    simpa [prefixWord, tailWord_4798148, baseEnd_4798148] using wordTrace_append hprefix tailTrace_4798148
  have hstable : (prefixWord ++ tailWord_4798148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798148).length < 2 ^ (prefixWord ++ tailWord_4798148).sum := by decide
  have hdescent : baseEnd_4798148 < baseStart_4798148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798162 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_4798162 : Nat := 118140960795 + 4798162 * 2 ^ 59
def prefixEnd_4798162 : Nat := 4983230072969 + 3 ^ 40 * 4798162 * 2
def baseEnd_4798162 : Nat := 2463763364138361402808661

theorem tailTrace_4798162 : CollatzResearch.WordTrace tailWord_4798162 prefixEnd_4798162 2463763364138361402808661 := by
  unfold tailWord_4798162
  simp only [CollatzResearch.WordTrace]
  refine ⟨43750836310771502418525185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116668896828724006449400493 43750836310771502418525185)
  ·
    refine ⟨32813127233078626813893889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43750836310771502418525185 32813127233078626813893889)
    ·
      refine ⟨24609845424808970110420417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32813127233078626813893889 24609845424808970110420417)
      ·
        refine ⟨18457384068606727582815313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24609845424808970110420417 18457384068606727582815313)
        ·
          refine ⟨13843038051455045687111485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18457384068606727582815313 13843038051455045687111485)
          ·
            refine ⟨5191139269295642132666807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13843038051455045687111485 5191139269295642132666807)
            ·
              refine ⟨7786708903943463199000211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191139269295642132666807 7786708903943463199000211)
              ·
                refine ⟨11680063355915194798500317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7786708903943463199000211 11680063355915194798500317)
                ·
                  refine ⟨4380023758468198049437619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11680063355915194798500317 4380023758468198049437619)
                  ·
                    refine ⟨6570035637702297074156429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4380023758468198049437619 6570035637702297074156429)
                    ·
                      refine ⟨2463763364138361402808661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6570035637702297074156429 2463763364138361402808661)
                      ·
                        rfl

theorem cell23_4798162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_4798162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798162 prefixEnd_4798162 := by exact prefixLift 4798162
  have htrace : WordTrace (prefixWord ++ tailWord_4798162) baseStart_4798162 baseEnd_4798162 := by
    simpa [prefixWord, tailWord_4798162, baseEnd_4798162] using wordTrace_append hprefix tailTrace_4798162
  have hstable : (prefixWord ++ tailWord_4798162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798162).length < 2 ^ (prefixWord ++ tailWord_4798162).sum := by decide
  have hdescent : baseEnd_4798162 < baseStart_4798162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798181 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_4798181 : Nat := 118140960795 + 4798181 * 2 ^ 59
def prefixEnd_4798181 : Nat := 4983230072969 + 3 ^ 40 * 4798181 * 2
def baseEnd_4798181 : Nat := 2463773120270796828471073

theorem tailTrace_4798181 : CollatzResearch.WordTrace tailWord_4798181 prefixEnd_4798181 2463773120270796828471073 := by
  unfold tailWord_4798181
  simp only [CollatzResearch.WordTrace]
  refine ⟨175004038230017175919042397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116669358820011450612694931 175004038230017175919042397)
  ·
    refine ⟨65626514336256440969640899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175004038230017175919042397 65626514336256440969640899)
    ·
      refine ⟨98439771504384661454461349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65626514336256440969640899 98439771504384661454461349)
      ·
        refine ⟨18457457157072124022711503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98439771504384661454461349 18457457157072124022711503)
        ·
          refine ⟨27686185735608186034067255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18457457157072124022711503 27686185735608186034067255)
          ·
            refine ⟨41529278603412279051100883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27686185735608186034067255 41529278603412279051100883)
            ·
              refine ⟨62293917905118418576651325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41529278603412279051100883 62293917905118418576651325)
              ·
                refine ⟨23360219214419406966244247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62293917905118418576651325 23360219214419406966244247)
                ·
                  refine ⟨35040328821629110449366371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23360219214419406966244247 35040328821629110449366371)
                  ·
                    refine ⟨52560493232443665674049557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35040328821629110449366371 52560493232443665674049557)
                    ·
                      refine ⟨2463773120270796828471073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52560493232443665674049557 2463773120270796828471073)
                      ·
                        rfl

theorem cell23_4798181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_4798181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798181 prefixEnd_4798181 := by exact prefixLift 4798181
  have htrace : WordTrace (prefixWord ++ tailWord_4798181) baseStart_4798181 baseEnd_4798181 := by
    simpa [prefixWord, tailWord_4798181, baseEnd_4798181] using wordTrace_append hprefix tailTrace_4798181
  have hstable : (prefixWord ++ tailWord_4798181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798181).length < 2 ^ (prefixWord ++ tailWord_4798181).sum := by decide
  have hdescent : baseEnd_4798181 < baseStart_4798181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798198 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_4798198 : Nat := 118140960795 + 4798198 * 2 ^ 59
def prefixEnd_4798198 : Nat := 4983230072969 + 3 ^ 40 * 4798198 * 2
def baseEnd_4798198 : Nat := 2463781849441923261958495

theorem tailTrace_4798198 : CollatzResearch.WordTrace tailWord_4798198 prefixEnd_4798198 2463781849441923261958495 := by
  unfold tailWord_4798198
  simp only [CollatzResearch.WordTrace]
  refine ⟨10937791141934724238900703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116669772180637058548274165 10937791141934724238900703)
  ·
    refine ⟨16406686712902086358351055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10937791141934724238900703 16406686712902086358351055)
    ·
      refine ⟨24610030069353129537526583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16406686712902086358351055 24610030069353129537526583)
      ·
        refine ⟨36915045104029694306289875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24610030069353129537526583 36915045104029694306289875)
        ·
          refine ⟨55372567656044541459434813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36915045104029694306289875 55372567656044541459434813)
          ·
            refine ⟨20764712871016703047288055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55372567656044541459434813 20764712871016703047288055)
            ·
              refine ⟨31147069306525054570932083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20764712871016703047288055 31147069306525054570932083)
              ·
                refine ⟨46720603959787581856398125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31147069306525054570932083 46720603959787581856398125)
                ·
                  refine ⟨17520226484920343196149297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46720603959787581856398125 17520226484920343196149297)
                  ·
                    refine ⟨13140169863690257397111973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17520226484920343196149297 13140169863690257397111973)
                    ·
                      refine ⟨2463781849441923261958495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13140169863690257397111973 2463781849441923261958495)
                      ·
                        rfl

theorem cell23_4798198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_4798198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798198 prefixEnd_4798198 := by exact prefixLift 4798198
  have htrace : WordTrace (prefixWord ++ tailWord_4798198) baseStart_4798198 baseEnd_4798198 := by
    simpa [prefixWord, tailWord_4798198, baseEnd_4798198] using wordTrace_append hprefix tailTrace_4798198
  have hstable : (prefixWord ++ tailWord_4798198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798198).length < 2 ^ (prefixWord ++ tailWord_4798198).sum := by decide
  have hdescent : baseEnd_4798198 < baseStart_4798198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798202 : List Nat := [3, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2]
def baseStart_4798202 : Nat := 118140960795 + 4798202 * 2 ^ 59
def prefixEnd_4798202 : Nat := 4983230072969 + 3 ^ 40 * 4798202 * 2
def baseEnd_4798202 : Nat := 2463783903364541246308477

theorem tailTrace_4798202 : CollatzResearch.WordTrace tailWord_4798202 prefixEnd_4798202 2463783903364541246308477 := by
  unfold tailWord_4798202
  simp only [CollatzResearch.WordTrace]
  refine ⟨43751201040735274126389215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116669869441960731003704573 43751201040735274126389215)
  ·
    refine ⟨65626801561102911189583823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43751201040735274126389215 65626801561102911189583823)
    ·
      refine ⟨98440202341654366784375735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65626801561102911189583823 98440202341654366784375735)
      ·
        refine ⟨147660303512481550176563603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98440202341654366784375735 147660303512481550176563603)
        ·
          refine ⟨221490455268722325264845405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147660303512481550176563603 221490455268722325264845405)
          ·
            refine ⟨83058920725770871974317027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221490455268722325264845405 83058920725770871974317027)
            ·
              refine ⟨124588381088656307961475541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83058920725770871974317027 124588381088656307961475541)
              ·
                refine ⟨2920040181765382217847083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 124588381088656307961475541 2920040181765382217847083)
                ·
                  refine ⟨4380060272648073326770625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920040181765382217847083 4380060272648073326770625)
                  ·
                    refine ⟨3285045204486054995077969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4380060272648073326770625 3285045204486054995077969)
                    ·
                      refine ⟨2463783903364541246308477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285045204486054995077969 2463783903364541246308477)
                      ·
                        rfl

theorem cell23_4798202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2].length) (baseStart_4798202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798202 prefixEnd_4798202 := by exact prefixLift 4798202
  have htrace : WordTrace (prefixWord ++ tailWord_4798202) baseStart_4798202 baseEnd_4798202 := by
    simpa [prefixWord, tailWord_4798202, baseEnd_4798202] using wordTrace_append hprefix tailTrace_4798202
  have hstable : (prefixWord ++ tailWord_4798202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798202).length < 2 ^ (prefixWord ++ tailWord_4798202).sum := by decide
  have hdescent : baseEnd_4798202 < baseStart_4798202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798219 : List Nat := [1, 1, 1, 1, 5, 1, 6, 2, 1, 2, 2]
def baseStart_4798219 : Nat := 118140960795 + 4798219 * 2 ^ 59
def prefixEnd_4798219 : Nat := 4983230072969 + 3 ^ 40 * 4798219 * 2
def baseEnd_4798219 : Nat := 2463792632535667679795899

theorem tailTrace_4798219 : CollatzResearch.WordTrace tailWord_4798219 prefixEnd_4798219 2463792632535667679795899 := by
  unfold tailWord_4798219
  simp only [CollatzResearch.WordTrace]
  refine ⟨175005424203879508408925711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116670282802586338939283807 175005424203879508408925711)
  ·
    refine ⟨262508136305819262613388567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175005424203879508408925711 262508136305819262613388567)
    ·
      refine ⟨393762204458728893920082851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262508136305819262613388567 393762204458728893920082851)
      ·
        refine ⟨590643306688093340880124277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393762204458728893920082851 590643306688093340880124277)
        ·
          refine ⟨55372810002008750707511651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 590643306688093340880124277 55372810002008750707511651)
          ·
            refine ⟨83059215003013126061267477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55372810002008750707511651 83059215003013126061267477)
            ·
              refine ⟨3893400703266240284121913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83059215003013126061267477 3893400703266240284121913)
              ·
                refine ⟨2920050527449680213091435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3893400703266240284121913 2920050527449680213091435)
                ·
                  refine ⟨4380075791174520319637153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920050527449680213091435 4380075791174520319637153)
                  ·
                    refine ⟨3285056843380890239727865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4380075791174520319637153 3285056843380890239727865)
                    ·
                      refine ⟨2463792632535667679795899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285056843380890239727865 2463792632535667679795899)
                      ·
                        rfl

theorem cell23_4798219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 1, 2, 2].length) (baseStart_4798219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798219 prefixEnd_4798219 := by exact prefixLift 4798219
  have htrace : WordTrace (prefixWord ++ tailWord_4798219) baseStart_4798219 baseEnd_4798219 := by
    simpa [prefixWord, tailWord_4798219, baseEnd_4798219] using wordTrace_append hprefix tailTrace_4798219
  have hstable : (prefixWord ++ tailWord_4798219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798219).length < 2 ^ (prefixWord ++ tailWord_4798219).sum := by decide
  have hdescent : baseEnd_4798219 < baseStart_4798219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798245 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 3, 3, 2]
def baseStart_4798245 : Nat := 118140960795 + 4798245 * 2 ^ 59
def prefixEnd_4798245 : Nat := 4983230072969 + 3 ^ 40 * 4798245 * 2
def baseEnd_4798245 : Nat := 2463805983032684578070779

theorem tailTrace_4798245 : CollatzResearch.WordTrace tailWord_4798245 prefixEnd_4798245 2463805983032684578070779 := by
  unfold tailWord_4798245
  simp only [CollatzResearch.WordTrace]
  refine ⟨175006372501785314849372189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116670915001190209899581459 175006372501785314849372189)
  ·
    refine ⟨65627389688169493068514571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175006372501785314849372189 65627389688169493068514571)
    ·
      refine ⟨98441084532254239602771857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65627389688169493068514571 98441084532254239602771857)
      ·
        refine ⟨73830813399190679702078893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98441084532254239602771857 73830813399190679702078893)
        ·
          refine ⟨27686555024696504888279585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73830813399190679702078893 27686555024696504888279585)
          ·
            refine ⟨20764916268522378666209689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27686555024696504888279585 20764916268522378666209689)
            ·
              refine ⟨15573687201391783999657267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20764916268522378666209689 15573687201391783999657267)
              ·
                refine ⟨23360530802087675999485901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15573687201391783999657267 23360530802087675999485901)
                ·
                  refine ⟨8760199050782878499807213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23360530802087675999485901 8760199050782878499807213)
                  ·
                    refine ⟨3285074644043579437427705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8760199050782878499807213 3285074644043579437427705)
                    ·
                      refine ⟨2463805983032684578070779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285074644043579437427705 2463805983032684578070779)
                      ·
                        rfl

theorem cell23_4798245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_4798245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798245 prefixEnd_4798245 := by exact prefixLift 4798245
  have htrace : WordTrace (prefixWord ++ tailWord_4798245) baseStart_4798245 baseEnd_4798245 := by
    simpa [prefixWord, tailWord_4798245, baseEnd_4798245] using wordTrace_append hprefix tailTrace_4798245
  have hstable : (prefixWord ++ tailWord_4798245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798245).length < 2 ^ (prefixWord ++ tailWord_4798245).sum := by decide
  have hdescent : baseEnd_4798245 < baseStart_4798245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798269 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4798269 : Nat := 118140960795 + 4798269 * 2 ^ 59
def prefixEnd_4798269 : Nat := 4983230072969 + 3 ^ 40 * 4798269 * 2
def baseEnd_4798269 : Nat := 2463818306568392484170669

theorem tailTrace_4798269 : CollatzResearch.WordTrace tailWord_4798269 prefixEnd_4798269 2463818306568392484170669 := by
  unfold tailWord_4798269
  simp only [CollatzResearch.WordTrace]
  refine ⟨175007247853698366948245861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116671498569132244632163907 175007247853698366948245861)
  ·
    refine ⟨32813858972568443802796099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175007247853698366948245861 32813858972568443802796099)
    ·
      refine ⟨49220788458852665704194149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32813858972568443802796099 49220788458852665704194149)
      ·
        refine ⟨9228897836034874819536403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49220788458852665704194149 9228897836034874819536403)
        ·
          refine ⟨13843346754052312229304605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9228897836034874819536403 13843346754052312229304605)
          ·
            refine ⟨5191255032769617085989227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13843346754052312229304605 5191255032769617085989227)
            ·
              refine ⟨7786882549154425628983841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191255032769617085989227 7786882549154425628983841)
              ·
                refine ⟨5840161911865819221737881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7786882549154425628983841 5840161911865819221737881)
                ·
                  refine ⟨4380121433899364416303411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5840161911865819221737881 4380121433899364416303411)
                  ·
                    refine ⟨6570182150849046624455117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4380121433899364416303411 6570182150849046624455117)
                    ·
                      refine ⟨2463818306568392484170669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6570182150849046624455117 2463818306568392484170669)
                      ·
                        rfl

theorem cell23_4798269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4798269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798269 prefixEnd_4798269 := by exact prefixLift 4798269
  have htrace : WordTrace (prefixWord ++ tailWord_4798269) baseStart_4798269 baseEnd_4798269 := by
    simpa [prefixWord, tailWord_4798269, baseEnd_4798269] using wordTrace_append hprefix tailTrace_4798269
  have hstable : (prefixWord ++ tailWord_4798269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798269).length < 2 ^ (prefixWord ++ tailWord_4798269).sum := by decide
  have hdescent : baseEnd_4798269 < baseStart_4798269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798285 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_4798285 : Nat := 118140960795 + 4798285 * 2 ^ 59
def prefixEnd_4798285 : Nat := 4983230072969 + 3 ^ 40 * 4798285 * 2
def baseEnd_4798285 : Nat := 821275507419621473856865

theorem tailTrace_4798285 : CollatzResearch.WordTrace tailWord_4798285 prefixEnd_4798285 821275507419621473856865 := by
  unfold tailWord_4798285
  simp only [CollatzResearch.WordTrace]
  refine ⟨175007831421640401680828309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116671887614426934453885539 175007831421640401680828309)
  ·
    refine ⟨8203492097889393828788827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 175007831421640401680828309 8203492097889393828788827)
    ·
      refine ⟨12305238146834090743183241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8203492097889393828788827 12305238146834090743183241)
      ·
        refine ⟨9228928610125568057387431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12305238146834090743183241 9228928610125568057387431)
        ·
          refine ⟨13843392915188352086081147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9228928610125568057387431 13843392915188352086081147)
          ·
            refine ⟨20765089372782528129121721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13843392915188352086081147 20765089372782528129121721)
            ·
              refine ⟨15573817029586896096841291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20765089372782528129121721 15573817029586896096841291)
              ·
                refine ⟨23360725544380344145261937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15573817029586896096841291 23360725544380344145261937)
                ·
                  refine ⟨17520544158285258108946453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23360725544380344145261937 17520544158285258108946453)
                  ·
                    refine ⟨821275507419621473856865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17520544158285258108946453 821275507419621473856865)
                    ·
                      rfl

theorem cell23_4798285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_4798285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798285 prefixEnd_4798285 := by exact prefixLift 4798285
  have htrace : WordTrace (prefixWord ++ tailWord_4798285) baseStart_4798285 baseEnd_4798285 := by
    simpa [prefixWord, tailWord_4798285, baseEnd_4798285] using wordTrace_append hprefix tailTrace_4798285
  have hstable : (prefixWord ++ tailWord_4798285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798285).length < 2 ^ (prefixWord ++ tailWord_4798285).sum := by decide
  have hdescent : baseEnd_4798285 < baseStart_4798285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798292 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_4798292 : Nat := 118140960795 + 4798292 * 2 ^ 59
def prefixEnd_4798292 : Nat := 4983230072969 + 3 ^ 40 * 4798292 * 2
def baseEnd_4798292 : Nat := 2463830116623445894183063

theorem tailTrace_4798292 : CollatzResearch.WordTrace tailWord_4798292 prefixEnd_4798292 2463830116623445894183063 := by
  unfold tailWord_4798292
  simp only [CollatzResearch.WordTrace]
  refine ⟨87504043366307520938166565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116672057821743361250888753 87504043366307520938166565)
  ·
    refine ⟨16407008131182660175906231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87504043366307520938166565 16407008131182660175906231)
    ·
      refine ⟨24610512196773990263859347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16407008131182660175906231 24610512196773990263859347)
      ·
        refine ⟨36915768295160985395789021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24610512196773990263859347 36915768295160985395789021)
        ·
          refine ⟨13843413110685369523420883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36915768295160985395789021 13843413110685369523420883)
          ·
            refine ⟨20765119666028054285131325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13843413110685369523420883 20765119666028054285131325)
            ·
              refine ⟨7786919874760520356924247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20765119666028054285131325 7786919874760520356924247)
              ·
                refine ⟨11680379812140780535386371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7786919874760520356924247 11680379812140780535386371)
                ·
                  refine ⟨17520569718211170803079557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11680379812140780535386371 17520569718211170803079557)
                  ·
                    refine ⟨3285106822164594525577417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17520569718211170803079557 3285106822164594525577417)
                    ·
                      refine ⟨2463830116623445894183063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285106822164594525577417 2463830116623445894183063)
                      ·
                        rfl

theorem cell23_4798292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_4798292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798292 prefixEnd_4798292 := by exact prefixLift 4798292
  have htrace : WordTrace (prefixWord ++ tailWord_4798292) baseStart_4798292 baseEnd_4798292 := by
    simpa [prefixWord, tailWord_4798292, baseEnd_4798292] using wordTrace_append hprefix tailTrace_4798292
  have hstable : (prefixWord ++ tailWord_4798292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798292).length < 2 ^ (prefixWord ++ tailWord_4798292).sum := by decide
  have hdescent : baseEnd_4798292 < baseStart_4798292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798343 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 2, 2, 2]
def baseStart_4798343 : Nat := 118140960795 + 4798343 * 2 ^ 59
def prefixEnd_4798343 : Nat := 4983230072969 + 3 ^ 40 * 4798343 * 2
def baseEnd_4798343 : Nat := 2463856304136825194645329

theorem tailTrace_4798343 : CollatzResearch.WordTrace tailWord_4798343 prefixEnd_4798343 2463856304136825194645329 := by
  unfold tailWord_4798343
  simp only [CollatzResearch.WordTrace]
  refine ⟨175009946855430277586439683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116673297903620185057626455 175009946855430277586439683)
  ·
    refine ⟨262514920283145416379659525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175009946855430277586439683 262514920283145416379659525)
    ·
      refine ⟨49221547553089765571186161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262514920283145416379659525 49221547553089765571186161)
      ·
        refine ⟨36916160664817324178389621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49221547553089765571186161 36916160664817324178389621)
        ·
          refine ⟨3460890062326624141724027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36916160664817324178389621 3460890062326624141724027)
          ·
            refine ⟨5191335093489936212586041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3460890062326624141724027 5191335093489936212586041)
            ·
              refine ⟨3893501320117452159439531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5191335093489936212586041 3893501320117452159439531)
              ·
                refine ⟨5840251980176178239159297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3893501320117452159439531 5840251980176178239159297)
                ·
                  refine ⟨4380188985132133679369473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5840251980176178239159297 4380188985132133679369473)
                  ·
                    refine ⟨3285141738849100259527105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4380188985132133679369473 3285141738849100259527105)
                    ·
                      refine ⟨2463856304136825194645329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285141738849100259527105 2463856304136825194645329)
                      ·
                        rfl

theorem cell23_4798343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_4798343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798343 prefixEnd_4798343 := by exact prefixLift 4798343
  have htrace : WordTrace (prefixWord ++ tailWord_4798343) baseStart_4798343 baseEnd_4798343 := by
    simpa [prefixWord, tailWord_4798343, baseEnd_4798343] using wordTrace_append hprefix tailTrace_4798343
  have hstable : (prefixWord ++ tailWord_4798343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798343).length < 2 ^ (prefixWord ++ tailWord_4798343).sum := by decide
  have hdescent : baseEnd_4798343 < baseStart_4798343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798348 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_4798348 : Nat := 118140960795 + 4798348 * 2 ^ 59
def prefixEnd_4798348 : Nat := 4983230072969 + 3 ^ 40 * 4798348 * 2
def baseEnd_4798348 : Nat := 2463858871540097675082805

theorem tailTrace_4798348 : CollatzResearch.WordTrace tailWord_4798348 prefixEnd_4798348 2463858871540097675082805 := by
  unfold tailWord_4798348
  simp only [CollatzResearch.WordTrace]
  refine ⟨87505064610206081720185849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116673419480274775626914465 87505064610206081720185849)
  ·
    refine ⟨65628798457654561290139387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87505064610206081720185849 65628798457654561290139387)
    ·
      refine ⟨98443197686481841935209081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65628798457654561290139387 98443197686481841935209081)
      ·
        refine ⟨73832398264861381451406811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98443197686481841935209081 73832398264861381451406811)
        ·
          refine ⟨110748597397292072177110217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73832398264861381451406811 110748597397292072177110217)
          ·
            refine ⟨83061448047969054132832663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110748597397292072177110217 83061448047969054132832663)
            ·
              refine ⟨124592172071953581199248995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83061448047969054132832663 124592172071953581199248995)
              ·
                refine ⟨186888258107930371798873493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124592172071953581199248995 186888258107930371798873493)
                ·
                  refine ⟨8760387098809236178072195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 186888258107930371798873493 8760387098809236178072195)
                  ·
                    refine ⟨13140580648213854267108293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8760387098809236178072195 13140580648213854267108293)
                    ·
                      refine ⟨2463858871540097675082805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13140580648213854267108293 2463858871540097675082805)
                      ·
                        rfl

theorem cell23_4798348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_4798348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798348 prefixEnd_4798348 := by exact prefixLift 4798348
  have htrace : WordTrace (prefixWord ++ tailWord_4798348) baseStart_4798348 baseEnd_4798348 := by
    simpa [prefixWord, tailWord_4798348, baseEnd_4798348] using wordTrace_append hprefix tailTrace_4798348
  have hstable : (prefixWord ++ tailWord_4798348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798348).length < 2 ^ (prefixWord ++ tailWord_4798348).sum := by decide
  have hdescent : baseEnd_4798348 < baseStart_4798348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798351 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_4798351 : Nat := 118140960795 + 4798351 * 2 ^ 59
def prefixEnd_4798351 : Nat := 4983230072969 + 3 ^ 40 * 4798351 * 2
def baseEnd_4798351 : Nat := 2463860411982061163345291

theorem tailTrace_4798351 : CollatzResearch.WordTrace tailWord_4798351 prefixEnd_4798351 2463860411982061163345291 := by
  unfold tailWord_4798351
  simp only [CollatzResearch.WordTrace]
  refine ⟨175010238639401294952730907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116673492426267529968487271 175010238639401294952730907)
  ·
    refine ⟨262515357959101942429096361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175010238639401294952730907 262515357959101942429096361)
    ·
      refine ⟨196886518469326456821822271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262515357959101942429096361 196886518469326456821822271)
      ·
        refine ⟨295329777703989685232733407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196886518469326456821822271 295329777703989685232733407)
        ·
          refine ⟨442994666555984527849100111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295329777703989685232733407 442994666555984527849100111)
          ·
            refine ⟨664491999833976791773650167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442994666555984527849100111 664491999833976791773650167)
            ·
              refine ⟨996737999750965187660475251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664491999833976791773650167 996737999750965187660475251)
              ·
                refine ⟨1495106999626447781490712877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996737999750965187660475251 1495106999626447781490712877)
                ·
                  refine ⟨560665124859917918059017329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1495106999626447781490712877 560665124859917918059017329)
                  ·
                    refine ⟨420498843644938438544262997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 560665124859917918059017329 420498843644938438544262997)
                    ·
                      refine ⟨2463860411982061163345291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 420498843644938438544262997 2463860411982061163345291)
                      ·
                        rfl

theorem cell23_4798351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_4798351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798351 prefixEnd_4798351 := by exact prefixLift 4798351
  have htrace : WordTrace (prefixWord ++ tailWord_4798351) baseStart_4798351 baseEnd_4798351 := by
    simpa [prefixWord, tailWord_4798351, baseEnd_4798351] using wordTrace_append hprefix tailTrace_4798351
  have hstable : (prefixWord ++ tailWord_4798351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798351).length < 2 ^ (prefixWord ++ tailWord_4798351).sum := by decide
  have hdescent : baseEnd_4798351 < baseStart_4798351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798365 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_4798365 : Nat := 118140960795 + 4798365 * 2 ^ 59
def prefixEnd_4798365 : Nat := 4983230072969 + 3 ^ 40 * 4798365 * 2
def baseEnd_4798365 : Nat := 2463867600711224108570227

theorem tailTrace_4798365 : CollatzResearch.WordTrace tailWord_4798365 prefixEnd_4798365 2463867600711224108570227 := by
  unfold tailWord_4798365
  simp only [CollatzResearch.WordTrace]
  refine ⟨175010749261350575343740549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116673832840900383562493699 175010749261350575343740549)
  ·
    refine ⟨32814515486503232876951353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175010749261350575343740549 32814515486503232876951353)
    ·
      refine ⟨24610886614877424657713515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32814515486503232876951353 24610886614877424657713515)
      ·
        refine ⟨36916329922316136986570273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24610886614877424657713515 36916329922316136986570273)
        ·
          refine ⟨27687247441737102739927705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36916329922316136986570273 27687247441737102739927705)
          ·
            refine ⟨20765435581302827054945779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27687247441737102739927705 20765435581302827054945779)
            ·
              refine ⟨31148153371954240582418669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20765435581302827054945779 31148153371954240582418669)
              ·
                refine ⟨11680557514482840218407001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31148153371954240582418669 11680557514482840218407001)
                ·
                  refine ⟨8760418135862130163805251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11680557514482840218407001 8760418135862130163805251)
                  ·
                    refine ⟨13140627203793195245707877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8760418135862130163805251 13140627203793195245707877)
                    ·
                      refine ⟨2463867600711224108570227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13140627203793195245707877 2463867600711224108570227)
                      ·
                        rfl

theorem cell23_4798365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_4798365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798365 prefixEnd_4798365 := by exact prefixLift 4798365
  have htrace : WordTrace (prefixWord ++ tailWord_4798365) baseStart_4798365 baseEnd_4798365 := by
    simpa [prefixWord, tailWord_4798365, baseEnd_4798365] using wordTrace_append hprefix tailTrace_4798365
  have hstable : (prefixWord ++ tailWord_4798365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798365).length < 2 ^ (prefixWord ++ tailWord_4798365).sum := by decide
  have hdescent : baseEnd_4798365 < baseStart_4798365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798392 : List Nat := [2, 1, 2, 1, 2, 3, 3, 4, 1, 4]
def baseStart_4798392 : Nat := 118140960795 + 4798392 * 2 ^ 59
def prefixEnd_4798392 : Nat := 4983230072969 + 3 ^ 40 * 4798392 * 2
def baseEnd_4798392 : Nat := 821293821562965167644201

theorem tailTrace_4798392 : CollatzResearch.WordTrace tailWord_4798392 prefixEnd_4798392 821293821562965167644201 := by
  unfold tailWord_4798392
  simp only [CollatzResearch.WordTrace]
  refine ⟨87505867016126379477486715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116674489354835172636648953 87505867016126379477486715)
  ·
    refine ⟨131258800524189569216230073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87505867016126379477486715 131258800524189569216230073)
    ·
      refine ⟨98444100393142176912172555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131258800524189569216230073 98444100393142176912172555)
      ·
        refine ⟨147666150589713265368258833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98444100393142176912172555 147666150589713265368258833)
        ·
          refine ⟨110749612942284949026194125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147666150589713265368258833 110749612942284949026194125)
          ·
            refine ⟨41531104853356855884822797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110749612942284949026194125 41531104853356855884822797)
            ·
              refine ⟨15574164320008820956808549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41531104853356855884822797 15574164320008820956808549)
              ·
                refine ⟨2920155810001653929401603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15574164320008820956808549 2920155810001653929401603)
                ·
                  refine ⟨4380233715002480894102405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920155810001653929401603 4380233715002480894102405)
                  ·
                    refine ⟨821293821562965167644201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4380233715002480894102405 821293821562965167644201)
                    ·
                      rfl

theorem cell23_4798392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_4798392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798392 prefixEnd_4798392 := by exact prefixLift 4798392
  have htrace : WordTrace (prefixWord ++ tailWord_4798392) baseStart_4798392 baseEnd_4798392 := by
    simpa [prefixWord, tailWord_4798392, baseEnd_4798392] using wordTrace_append hprefix tailTrace_4798392
  have hstable : (prefixWord ++ tailWord_4798392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798392).length < 2 ^ (prefixWord ++ tailWord_4798392).sum := by decide
  have hdescent : baseEnd_4798392 < baseStart_4798392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798439 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 6]
def baseStart_4798439 : Nat := 118140960795 + 4798439 * 2 ^ 59
def prefixEnd_4798439 : Nat := 4983230072969 + 3 ^ 40 * 4798439 * 2
def baseEnd_4798439 : Nat := 273767288697739646560543

theorem tailTrace_4798439 : CollatzResearch.WordTrace tailWord_4798439 prefixEnd_4798439 273767288697739646560543 := by
  unfold tailWord_4798439
  simp only [CollatzResearch.WordTrace]
  refine ⟨175013448263082485981934371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116675632175388323987956247 175013448263082485981934371)
  ·
    refine ⟨262520172394623728972901557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175013448263082485981934371 262520172394623728972901557)
    ·
      refine ⟨24611266161995974591209521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 262520172394623728972901557 24611266161995974591209521)
      ·
        refine ⟨18458449621496980943407141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24611266161995974591209521 18458449621496980943407141)
        ·
          refine ⟨3460959304030683926888839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18458449621496980943407141 3460959304030683926888839)
          ·
            refine ⟨5191438956046025890333259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3460959304030683926888839 5191438956046025890333259)
            ·
              refine ⟨7787158434069038835499889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191438956046025890333259 7787158434069038835499889)
              ·
                refine ⟨5840368825551779126624917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7787158434069038835499889 5840368825551779126624917)
                ·
                  refine ⟨273767288697739646560543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5840368825551779126624917 273767288697739646560543)
                  ·
                    rfl

theorem cell23_4798439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 6].length) (baseStart_4798439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798439 prefixEnd_4798439 := by exact prefixLift 4798439
  have htrace : WordTrace (prefixWord ++ tailWord_4798439) baseStart_4798439 baseEnd_4798439 := by
    simpa [prefixWord, tailWord_4798439, baseEnd_4798439] using wordTrace_append hprefix tailTrace_4798439
  have hstable : (prefixWord ++ tailWord_4798439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798439).length < 2 ^ (prefixWord ++ tailWord_4798439).sum := by decide
  have hdescent : baseEnd_4798439 < baseStart_4798439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798442 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_4798442 : Nat := 118140960795 + 4798442 * 2 ^ 59
def prefixEnd_4798442 : Nat := 4983230072969 + 3 ^ 40 * 4798442 * 2
def baseEnd_4798442 : Nat := 2463907138721620307307373

theorem tailTrace_4798442 : CollatzResearch.WordTrace tailWord_4798442 prefixEnd_4798442 2463907138721620307307373 := by
  unfold tailWord_4798442
  simp only [CollatzResearch.WordTrace]
  refine ⟨43753389420517904373573395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116675705121381078329529053 43753389420517904373573395)
  ·
    refine ⟨65630084130776856560360093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43753389420517904373573395 65630084130776856560360093)
    ·
      refine ⟨24611281549041321210135035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65630084130776856560360093 24611281549041321210135035)
      ·
        refine ⟨36916922323561981815202553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24611281549041321210135035 36916922323561981815202553)
        ·
          refine ⟨27687691742671486361401915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36916922323561981815202553 27687691742671486361401915)
          ·
            refine ⟨41531537614007229542102873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27687691742671486361401915 41531537614007229542102873)
            ·
              refine ⟨31148653210505422156577155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41531537614007229542102873 31148653210505422156577155)
              ·
                refine ⟨46722979815758133234865733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31148653210505422156577155 46722979815758133234865733)
                ·
                  refine ⟨8760558715454649981537325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46722979815758133234865733 8760558715454649981537325)
                  ·
                    refine ⟨3285209518295493743076497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8760558715454649981537325 3285209518295493743076497)
                    ·
                      refine ⟨2463907138721620307307373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285209518295493743076497 2463907138721620307307373)
                      ·
                        rfl

theorem cell23_4798442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_4798442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798442 prefixEnd_4798442 := by exact prefixLift 4798442
  have htrace : WordTrace (prefixWord ++ tailWord_4798442) baseStart_4798442 baseEnd_4798442 := by
    simpa [prefixWord, tailWord_4798442, baseEnd_4798442] using wordTrace_append hprefix tailTrace_4798442
  have hstable : (prefixWord ++ tailWord_4798442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798442).length < 2 ^ (prefixWord ++ tailWord_4798442).sum := by decide
  have hdescent : baseEnd_4798442 < baseStart_4798442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798448 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 3, 6]
def baseStart_4798448 : Nat := 118140960795 + 4798448 * 2 ^ 59
def prefixEnd_4798448 : Nat := 4983230072969 + 3 ^ 40 * 4798448 * 2
def baseEnd_4798448 : Nat := 821303406535182427944115

theorem tailTrace_4798448 : CollatzResearch.WordTrace tailWord_4798448 prefixEnd_4798448 821303406535182427944115 := by
  unfold tailWord_4798448
  simp only [CollatzResearch.WordTrace]
  refine ⟨87506888260024940259505999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116675851013366587012674665 87506888260024940259505999)
  ·
    refine ⟨131260332390037410389258999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87506888260024940259505999 131260332390037410389258999)
    ·
      refine ⟨196890498585056115583888499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131260332390037410389258999 196890498585056115583888499)
      ·
        refine ⟨295335747877584173375832749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196890498585056115583888499 295335747877584173375832749)
        ·
          refine ⟨110750905454094065015937281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295335747877584173375832749 110750905454094065015937281)
          ·
            refine ⟨83063179090570548761952961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110750905454094065015937281 83063179090570548761952961)
            ·
              refine ⟨62297384317927911571464721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83063179090570548761952961 62297384317927911571464721)
              ·
                refine ⟨46723038238445933678598541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62297384317927911571464721 46723038238445933678598541)
                ·
                  refine ⟨17521139339417225129474453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46723038238445933678598541 17521139339417225129474453)
                  ·
                    refine ⟨821303406535182427944115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17521139339417225129474453 821303406535182427944115)
                    ·
                      rfl

theorem cell23_4798448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_4798448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798448 prefixEnd_4798448 := by exact prefixLift 4798448
  have htrace : WordTrace (prefixWord ++ tailWord_4798448) baseStart_4798448 baseEnd_4798448 := by
    simpa [prefixWord, tailWord_4798448, baseEnd_4798448] using wordTrace_append hprefix tailTrace_4798448
  have hstable : (prefixWord ++ tailWord_4798448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798448).length < 2 ^ (prefixWord ++ tailWord_4798448).sum := by decide
  have hdescent : baseEnd_4798448 < baseStart_4798448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798449 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 3, 1, 3]
def baseStart_4798449 : Nat := 118140960795 + 4798449 * 2 ^ 59
def prefixEnd_4798449 : Nat := 4983230072969 + 3 ^ 40 * 4798449 * 2
def baseEnd_4798449 : Nat := 2463910733086201779919841

theorem tailTrace_4798449 : CollatzResearch.WordTrace tailWord_4798449 prefixEnd_4798449 2463910733086201779919841 := by
  unfold tailWord_4798449
  simp only [CollatzResearch.WordTrace]
  refine ⟨175013812993046257689798401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116675875328697505126532267 175013812993046257689798401)
  ·
    refine ⟨131260359744784693267348801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175013812993046257689798401 131260359744784693267348801)
    ·
      refine ⟨98445269808588519950511601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131260359744784693267348801 98445269808588519950511601)
      ·
        refine ⟨73833952356441389962883701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98445269808588519950511601 73833952356441389962883701)
        ·
          refine ⟨6921933033416380309020347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73833952356441389962883701 6921933033416380309020347)
          ·
            refine ⟨10382899550124570463530521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6921933033416380309020347 10382899550124570463530521)
            ·
              refine ⟨7787174662593427847647891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10382899550124570463530521 7787174662593427847647891)
              ·
                refine ⟨11680761993890141771471837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7787174662593427847647891 11680761993890141771471837)
                ·
                  refine ⟨4380285747708803164301939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11680761993890141771471837 4380285747708803164301939)
                  ·
                    refine ⟨6570428621563204746452909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4380285747708803164301939 6570428621563204746452909)
                    ·
                      refine ⟨2463910733086201779919841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6570428621563204746452909 2463910733086201779919841)
                      ·
                        rfl

theorem cell23_4798449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_4798449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798449 prefixEnd_4798449 := by exact prefixLift 4798449
  have htrace : WordTrace (prefixWord ++ tailWord_4798449) baseStart_4798449 baseEnd_4798449 := by
    simpa [prefixWord, tailWord_4798449, baseEnd_4798449] using wordTrace_append hprefix tailTrace_4798449
  have hstable : (prefixWord ++ tailWord_4798449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798449).length < 2 ^ (prefixWord ++ tailWord_4798449).sum := by decide
  have hdescent : baseEnd_4798449 < baseStart_4798449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798472 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_4798472 : Nat := 118140960795 + 4798472 * 2 ^ 59
def prefixEnd_4798472 : Nat := 4983230072969 + 3 ^ 40 * 4798472 * 2
def baseEnd_4798472 : Nat := 2463922543141255189932235

theorem tailTrace_4798472 : CollatzResearch.WordTrace tailWord_4798472 prefixEnd_4798472 2463922543141255189932235 := by
  unfold tailWord_4798472
  simp only [CollatzResearch.WordTrace]
  refine ⟨87507325935981466308942835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116676434581308621745257113 87507325935981466308942835)
  ·
    refine ⟨131260988903972199463414253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87507325935981466308942835 131260988903972199463414253)
    ·
      refine ⟨49222870838989574798780345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131260988903972199463414253 49222870838989574798780345)
      ·
        refine ⟨36917153129242181099085259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49222870838989574798780345 36917153129242181099085259)
        ·
          refine ⟨55375729693863271648627889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36917153129242181099085259 55375729693863271648627889)
          ·
            refine ⟨41531797270397453736470917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55375729693863271648627889 41531797270397453736470917)
            ·
              refine ⟨7787211988199522575588297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41531797270397453736470917 7787211988199522575588297)
              ·
                refine ⟨5840408991149641931691223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7787211988199522575588297 5840408991149641931691223)
                ·
                  refine ⟨8760613486724462897536835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5840408991149641931691223 8760613486724462897536835)
                  ·
                    refine ⟨13140920230086694346305253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8760613486724462897536835 13140920230086694346305253)
                    ·
                      refine ⟨2463922543141255189932235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13140920230086694346305253 2463922543141255189932235)
                      ·
                        rfl

theorem cell23_4798472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_4798472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798472 prefixEnd_4798472 := by exact prefixLift 4798472
  have htrace : WordTrace (prefixWord ++ tailWord_4798472) baseStart_4798472 baseEnd_4798472 := by
    simpa [prefixWord, tailWord_4798472, baseEnd_4798472] using wordTrace_append hprefix tailTrace_4798472
  have hstable : (prefixWord ++ tailWord_4798472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798472).length < 2 ^ (prefixWord ++ tailWord_4798472).sum := by decide
  have hdescent : baseEnd_4798472 < baseStart_4798472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798477 : List Nat := [1, 7, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4798477 : Nat := 118140960795 + 4798477 * 2 ^ 59
def prefixEnd_4798477 : Nat := 4983230072969 + 3 ^ 40 * 4798477 * 2
def baseEnd_4798477 : Nat := 821308370181509223456571

theorem tailTrace_4798477 : CollatzResearch.WordTrace tailWord_4798477 prefixEnd_4798477 821308370181509223456571 := by
  unfold tailWord_4798477
  simp only [CollatzResearch.WordTrace]
  refine ⟨175014834236944818471817685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116676556157963212314545123 175014834236944818471817685)
  ·
    refine ⟨4101910177428394182933227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 175014834236944818471817685 4101910177428394182933227)
    ·
      refine ⟨6152865266142591274399841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4101910177428394182933227 6152865266142591274399841)
      ·
        refine ⟨4614648949606943455799881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6152865266142591274399841 4614648949606943455799881)
        ·
          refine ⟨3460986712205207591849911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4614648949606943455799881 3460986712205207591849911)
          ·
            refine ⟨5191480068307811387774867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3460986712205207591849911 5191480068307811387774867)
            ·
              refine ⟨7787220102461717081662301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191480068307811387774867 7787220102461717081662301)
              ·
                refine ⟨2920207538423143905623363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7787220102461717081662301 2920207538423143905623363)
                ·
                  refine ⟨4380311307634715858435045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920207538423143905623363 4380311307634715858435045)
                  ·
                    refine ⟨821308370181509223456571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4380311307634715858435045 821308370181509223456571)
                    ·
                      rfl

theorem cell23_4798477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4798477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798477 prefixEnd_4798477 := by exact prefixLift 4798477
  have htrace : WordTrace (prefixWord ++ tailWord_4798477) baseStart_4798477 baseEnd_4798477 := by
    simpa [prefixWord, tailWord_4798477, baseEnd_4798477] using wordTrace_append hprefix tailTrace_4798477
  have hstable : (prefixWord ++ tailWord_4798477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798477).length < 2 ^ (prefixWord ++ tailWord_4798477).sum := by decide
  have hdescent : baseEnd_4798477 < baseStart_4798477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798492 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_4798492 : Nat := 118140960795 + 4798492 * 2 ^ 59
def prefixEnd_4798492 : Nat := 4983230072969 + 3 ^ 40 * 4798492 * 2
def baseEnd_4798492 : Nat := 2463932812754345111682143

theorem tailTrace_4798492 : CollatzResearch.WordTrace tailWord_4798492 prefixEnd_4798492 2463932812754345111682143 := by
  unfold tailWord_4798492
  simp only [CollatzResearch.WordTrace]
  refine ⟨87507690665945238016806865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116676920887926984022409153 87507690665945238016806865)
  ·
    refine ⟨65630767999458928512605149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87507690665945238016806865 65630767999458928512605149)
    ·
      refine ⟨24611537999797098192226931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65630767999458928512605149 24611537999797098192226931)
      ·
        refine ⟨36917306999695647288340397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24611537999797098192226931 36917306999695647288340397)
        ·
          refine ⟨13843990124885867733127649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36917306999695647288340397 13843990124885867733127649)
          ·
            refine ⟨10382992593664400799845737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13843990124885867733127649 10382992593664400799845737)
            ·
              refine ⟨7787244445248300599884303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10382992593664400799845737 7787244445248300599884303)
              ·
                refine ⟨11680866667872450899826455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7787244445248300599884303 11680866667872450899826455)
                ·
                  refine ⟨17521300001808676349739683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11680866667872450899826455 17521300001808676349739683)
                  ·
                    refine ⟨26281950002713014524609525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17521300001808676349739683 26281950002713014524609525)
                    ·
                      refine ⟨2463932812754345111682143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26281950002713014524609525 2463932812754345111682143)
                      ·
                        rfl

theorem cell23_4798492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_4798492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798492 prefixEnd_4798492 := by exact prefixLift 4798492
  have htrace : WordTrace (prefixWord ++ tailWord_4798492) baseStart_4798492 baseEnd_4798492 := by
    simpa [prefixWord, tailWord_4798492, baseEnd_4798492] using wordTrace_append hprefix tailTrace_4798492
  have hstable : (prefixWord ++ tailWord_4798492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798492).length < 2 ^ (prefixWord ++ tailWord_4798492).sum := by decide
  have hdescent : baseEnd_4798492 < baseStart_4798492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798506 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_4798506 : Nat := 118140960795 + 4798506 * 2 ^ 59
def prefixEnd_4798506 : Nat := 4983230072969 + 3 ^ 40 * 4798506 * 2
def baseEnd_4798506 : Nat := 2463940001483508056907079

theorem tailTrace_4798506 : CollatzResearch.WordTrace tailWord_4798506 prefixEnd_4798506 2463940001483508056907079 := by
  unfold tailWord_4798506
  simp only [CollatzResearch.WordTrace]
  refine ⟨43753972988459939106155843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116677261302559837616415581 43753972988459939106155843)
  ·
    refine ⟨65630959482689908659233765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43753972988459939106155843 65630959482689908659233765)
    ·
      refine ⟨12305804903004357873606331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65630959482689908659233765 12305804903004357873606331)
      ·
        refine ⟨18458707354506536810409497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12305804903004357873606331 18458707354506536810409497)
        ·
          refine ⟨13844030515879902607807123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18458707354506536810409497 13844030515879902607807123)
          ·
            refine ⟨20766045773819853911710685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13844030515879902607807123 20766045773819853911710685)
            ·
              refine ⟨7787267165182445216891507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20766045773819853911710685 7787267165182445216891507)
              ·
                refine ⟨11680900747773667825337261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7787267165182445216891507 11680900747773667825337261)
                ·
                  refine ⟨4380337780415125434501473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11680900747773667825337261 4380337780415125434501473)
                  ·
                    refine ⟨3285253335311344075876105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4380337780415125434501473 3285253335311344075876105)
                    ·
                      refine ⟨2463940001483508056907079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285253335311344075876105 2463940001483508056907079)
                      ·
                        rfl

theorem cell23_4798506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_4798506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798506 prefixEnd_4798506 := by exact prefixLift 4798506
  have htrace : WordTrace (prefixWord ++ tailWord_4798506) baseStart_4798506 baseEnd_4798506 := by
    simpa [prefixWord, tailWord_4798506, baseEnd_4798506] using wordTrace_append hprefix tailTrace_4798506
  have hstable : (prefixWord ++ tailWord_4798506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798506).length < 2 ^ (prefixWord ++ tailWord_4798506).sum := by decide
  have hdescent : baseEnd_4798506 < baseStart_4798506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798516 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_4798516 : Nat := 118140960795 + 4798516 * 2 ^ 59
def prefixEnd_4798516 : Nat := 4983230072969 + 3 ^ 40 * 4798516 * 2
def baseEnd_4798516 : Nat := 821315045430017672594011

theorem tailTrace_4798516 : CollatzResearch.WordTrace tailWord_4798516 prefixEnd_4798516 821315045430017672594011 := by
  unfold tailWord_4798516
  simp only [CollatzResearch.WordTrace]
  refine ⟨87508128341901764066243701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116677504455869018754991601 87508128341901764066243701)
  ·
    refine ⟨8203887032053290381210347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87508128341901764066243701 8203887032053290381210347)
    ·
      refine ⟨12305830548079935571815521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8203887032053290381210347 12305830548079935571815521)
      ·
        refine ⟨9229372911059951678861641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12305830548079935571815521 9229372911059951678861641)
        ·
          refine ⟨6922029683294963759146231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9229372911059951678861641 6922029683294963759146231)
          ·
            refine ⟨10383044524942445638719347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6922029683294963759146231 10383044524942445638719347)
            ·
              refine ⟨15574566787413668458079021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10383044524942445638719347 15574566787413668458079021)
              ·
                refine ⟨5840462545280125671779633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15574566787413668458079021 5840462545280125671779633)
                ·
                  refine ⟨4380346908960094253834725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5840462545280125671779633 4380346908960094253834725)
                  ·
                    refine ⟨821315045430017672594011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4380346908960094253834725 821315045430017672594011)
                    ·
                      rfl

theorem cell23_4798516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_4798516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798516 prefixEnd_4798516 := by exact prefixLift 4798516
  have htrace : WordTrace (prefixWord ++ tailWord_4798516) baseStart_4798516 baseEnd_4798516 := by
    simpa [prefixWord, tailWord_4798516, baseEnd_4798516] using wordTrace_append hprefix tailTrace_4798516
  have hstable : (prefixWord ++ tailWord_4798516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798516).length < 2 ^ (prefixWord ++ tailWord_4798516).sum := by decide
  have hdescent : baseEnd_4798516 < baseStart_4798516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798556 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_4798556 : Nat := 118140960795 + 4798556 * 2 ^ 59
def prefixEnd_4798556 : Nat := 4983230072969 + 3 ^ 40 * 4798556 * 2
def baseEnd_4798556 : Nat := 2463965675516232861281849

theorem tailTrace_4798556 : CollatzResearch.WordTrace tailWord_4798556 prefixEnd_4798556 2463965675516232861281849 := by
  unfold tailWord_4798556
  simp only [CollatzResearch.WordTrace]
  refine ⟨87508857801829307481971761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116678477069105743309295681 87508857801829307481971761)
  ·
    refine ⟨65631643351371980611478821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87508857801829307481971761 65631643351371980611478821)
    ·
      refine ⟨12305933128382246364652279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65631643351371980611478821 12305933128382246364652279)
      ·
        refine ⟨18458899692573369546978419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12305933128382246364652279 18458899692573369546978419)
        ·
          refine ⟨27688349538860054320467629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18458899692573369546978419 27688349538860054320467629)
          ·
            refine ⟨10383131077072520370175361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27688349538860054320467629 10383131077072520370175361)
            ·
              refine ⟨7787348307804390277631521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10383131077072520370175361 7787348307804390277631521)
              ·
                refine ⟨5840511230853292708223641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7787348307804390277631521 5840511230853292708223641)
                ·
                  refine ⟨4380383423139969531167731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5840511230853292708223641 4380383423139969531167731)
                  ·
                    refine ⟨6570575134709954296751597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4380383423139969531167731 6570575134709954296751597)
                    ·
                      refine ⟨2463965675516232861281849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6570575134709954296751597 2463965675516232861281849)
                      ·
                        rfl

theorem cell23_4798556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_4798556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798556 prefixEnd_4798556 := by exact prefixLift 4798556
  have htrace : WordTrace (prefixWord ++ tailWord_4798556) baseStart_4798556 baseEnd_4798556 := by
    simpa [prefixWord, tailWord_4798556, baseEnd_4798556] using wordTrace_append hprefix tailTrace_4798556
  have hstable : (prefixWord ++ tailWord_4798556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798556).length < 2 ^ (prefixWord ++ tailWord_4798556).sum := by decide
  have hdescent : baseEnd_4798556 < baseStart_4798556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798557 : List Nat := [1, 4, 4, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4798557 : Nat := 118140960795 + 4798557 * 2 ^ 59
def prefixEnd_4798557 : Nat := 4983230072969 + 3 ^ 40 * 4798557 * 2
def baseEnd_4798557 : Nat := 2463966188996887357369345

theorem tailTrace_4798557 : CollatzResearch.WordTrace tailWord_4798557 prefixEnd_4798557 2463966188996887357369345 := by
  unfold tailWord_4798557
  simp only [CollatzResearch.WordTrace]
  refine ⟨175017752076654992134729925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116678501384436661423153283 175017752076654992134729925)
  ·
    refine ⟨32815828514372811025261861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175017752076654992134729925 32815828514372811025261861)
    ·
      refine ⟨6152967846444902067236599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32815828514372811025261861 6152967846444902067236599)
      ·
        refine ⟨9229451769667353100854899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6152967846444902067236599 9229451769667353100854899)
        ·
          refine ⟨13844177654501029651282349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9229451769667353100854899 13844177654501029651282349)
          ·
            refine ⟨5191566620437886119230881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13844177654501029651282349 5191566620437886119230881)
            ·
              refine ⟨3893674965328414589423161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5191566620437886119230881 3893674965328414589423161)
              ·
                refine ⟨2920256223996310942067371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3893674965328414589423161 2920256223996310942067371)
                ·
                  refine ⟨4380384335994466413101057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920256223996310942067371 4380384335994466413101057)
                  ·
                    refine ⟨3285288251995849809825793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4380384335994466413101057 3285288251995849809825793)
                    ·
                      refine ⟨2463966188996887357369345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285288251995849809825793 2463966188996887357369345)
                      ·
                        rfl

theorem cell23_4798557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4798557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798557 prefixEnd_4798557 := by exact prefixLift 4798557
  have htrace : WordTrace (prefixWord ++ tailWord_4798557) baseStart_4798557 baseEnd_4798557 := by
    simpa [prefixWord, tailWord_4798557, baseEnd_4798557] using wordTrace_append hprefix tailTrace_4798557
  have hstable : (prefixWord ++ tailWord_4798557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798557).length < 2 ^ (prefixWord ++ tailWord_4798557).sum := by decide
  have hdescent : baseEnd_4798557 < baseStart_4798557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798575 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 4]
def baseStart_4798575 : Nat := 118140960795 + 4798575 * 2 ^ 59
def prefixEnd_4798575 : Nat := 4983230072969 + 3 ^ 40 * 4798575 * 2
def baseEnd_4798575 : Nat := 2463975431648668286944261

theorem tailTrace_4798575 : CollatzResearch.WordTrace tailWord_4798575 prefixEnd_4798575 2463975431648668286944261 := by
  unfold tailWord_4798575
  simp only [CollatzResearch.WordTrace]
  refine ⟨175018408590589781208885179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116678939060393187472590119 175018408590589781208885179)
  ·
    refine ⟨262527612885884671813327769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175018408590589781208885179 262527612885884671813327769)
    ·
      refine ⟨196895709664413503859995827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262527612885884671813327769 196895709664413503859995827)
      ·
        refine ⟨295343564496620255789993741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196895709664413503859995827 295343564496620255789993741)
        ·
          refine ⟨110753836686232595921247653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295343564496620255789993741 110753836686232595921247653)
          ·
            refine ⟨20766344378668611735233935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110753836686232595921247653 20766344378668611735233935)
            ·
              refine ⟨31149516568002917602850903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20766344378668611735233935 31149516568002917602850903)
              ·
                refine ⟨46724274852004376404276355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31149516568002917602850903 46724274852004376404276355)
                ·
                  refine ⟨70086412278006564606414533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46724274852004376404276355 70086412278006564606414533)
                  ·
                    refine ⟨13141202302126230863702725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70086412278006564606414533 13141202302126230863702725)
                    ·
                      refine ⟨2463975431648668286944261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13141202302126230863702725 2463975431648668286944261)
                      ·
                        rfl

theorem cell23_4798575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_4798575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798575 prefixEnd_4798575 := by exact prefixLift 4798575
  have htrace : WordTrace (prefixWord ++ tailWord_4798575) baseStart_4798575 baseEnd_4798575 := by
    simpa [prefixWord, tailWord_4798575, baseEnd_4798575] using wordTrace_append hprefix tailTrace_4798575
  have hstable : (prefixWord ++ tailWord_4798575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798575).length < 2 ^ (prefixWord ++ tailWord_4798575).sum := by decide
  have hdescent : baseEnd_4798575 < baseStart_4798575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798585 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 9]
def baseStart_4798585 : Nat := 118140960795 + 4798585 * 2 ^ 59
def prefixEnd_4798585 : Nat := 4983230072969 + 3 ^ 40 * 4798585 * 2
def baseEnd_4798585 : Nat := 273775618495023694202135

theorem tailTrace_4798585 : CollatzResearch.WordTrace tailWord_4798585 prefixEnd_4798585 273775618495023694202135 := by
  unfold tailWord_4798585
  simp only [CollatzResearch.WordTrace]
  refine ⟨175018773320553552916749209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116679182213702368611166139 175018773320553552916749209)
  ·
    refine ⟨131264079990415164687561907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175018773320553552916749209 131264079990415164687561907)
    ·
      refine ⟨196896119985622747031342861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131264079990415164687561907 196896119985622747031342861)
      ·
        refine ⟨73836044994608530136753573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196896119985622747031342861 73836044994608530136753573)
        ·
          refine ⟨13844258436489099400641295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73836044994608530136753573 13844258436489099400641295)
          ·
            refine ⟨20766387654733649100961943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13844258436489099400641295 20766387654733649100961943)
            ·
              refine ⟨31149581482100473651442915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20766387654733649100961943 31149581482100473651442915)
              ·
                refine ⟨46724372223150710477164373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31149581482100473651442915 46724372223150710477164373)
                ·
                  refine ⟨273775618495023694202135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46724372223150710477164373 273775618495023694202135)
                  ·
                    rfl

theorem cell23_4798585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 9].length) (baseStart_4798585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798585 prefixEnd_4798585 := by exact prefixLift 4798585
  have htrace : WordTrace (prefixWord ++ tailWord_4798585) baseStart_4798585 baseEnd_4798585 := by
    simpa [prefixWord, tailWord_4798585, baseEnd_4798585] using wordTrace_append hprefix tailTrace_4798585
  have hstable : (prefixWord ++ tailWord_4798585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798585).length < 2 ^ (prefixWord ++ tailWord_4798585).sum := by decide
  have hdescent : baseEnd_4798585 < baseStart_4798585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798655 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_4798655 : Nat := 118140960795 + 4798655 * 2 ^ 59
def prefixEnd_4798655 : Nat := 4983230072969 + 3 ^ 40 * 4798655 * 2
def baseEnd_4798655 : Nat := 2464016510101027973943893

theorem tailTrace_4798655 : CollatzResearch.WordTrace tailWord_4798655 prefixEnd_4798655 2464016510101027973943893 := by
  unfold tailWord_4798655
  simp only [CollatzResearch.WordTrace]
  refine ⟨175021326430299954871797419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116680884286866636581198279 175021326430299954871797419)
  ·
    refine ⟨262531989645449932307696129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175021326430299954871797419 262531989645449932307696129)
    ·
      refine ⟨196898992234087449230772097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262531989645449932307696129 196898992234087449230772097)
      ·
        refine ⟨147674244175565586923079073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196898992234087449230772097 147674244175565586923079073)
        ·
          refine ⟨110755683131674190192309305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147674244175565586923079073 110755683131674190192309305)
          ·
            refine ⟨83066762348755642644231979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110755683131674190192309305 83066762348755642644231979)
            ·
              refine ⟨124600143523133463966347969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83066762348755642644231979 124600143523133463966347969)
              ·
                refine ⟨93450107642350097974760977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124600143523133463966347969 93450107642350097974760977)
                ·
                  refine ⟨70087580731762573481070733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93450107642350097974760977 70087580731762573481070733)
                  ·
                    refine ⟨26282842774410965055401525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70087580731762573481070733 26282842774410965055401525)
                    ·
                      refine ⟨2464016510101027973943893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26282842774410965055401525 2464016510101027973943893)
                      ·
                        rfl

theorem cell23_4798655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_4798655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798655 prefixEnd_4798655 := by exact prefixLift 4798655
  have htrace : WordTrace (prefixWord ++ tailWord_4798655) baseStart_4798655 baseEnd_4798655 := by
    simpa [prefixWord, tailWord_4798655, baseEnd_4798655] using wordTrace_append hprefix tailTrace_4798655
  have hstable : (prefixWord ++ tailWord_4798655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798655).length < 2 ^ (prefixWord ++ tailWord_4798655).sum := by decide
  have hdescent : baseEnd_4798655 < baseStart_4798655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798665 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_4798665 : Nat := 118140960795 + 4798665 * 2 ^ 59
def prefixEnd_4798665 : Nat := 4983230072969 + 3 ^ 40 * 4798665 * 2
def baseEnd_4798665 : Nat := 2464021644907572934818847

theorem tailTrace_4798665 : CollatzResearch.WordTrace tailWord_4798665 prefixEnd_4798665 2464021644907572934818847 := by
  unfold tailWord_4798665
  simp only [CollatzResearch.WordTrace]
  refine ⟨175021691160263726579661449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116681127440175817719774299 175021691160263726579661449)
  ·
    refine ⟨131266268370197794934746087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175021691160263726579661449 131266268370197794934746087)
    ·
      refine ⟨196899402555296692402119131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131266268370197794934746087 196899402555296692402119131)
      ·
        refine ⟨295349103832945038603178697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196899402555296692402119131 295349103832945038603178697)
        ·
          refine ⟨221511827874708778952384023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295349103832945038603178697 221511827874708778952384023)
          ·
            refine ⟨332267741812063168428576035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221511827874708778952384023 332267741812063168428576035)
            ·
              refine ⟨498401612718094752642864053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332267741812063168428576035 498401612718094752642864053)
              ·
                refine ⟨46725151192321383060268505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 498401612718094752642864053 46725151192321383060268505)
                ·
                  refine ⟨35043863394241037295201379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46725151192321383060268505 35043863394241037295201379)
                  ·
                    refine ⟨52565795091361555942802069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35043863394241037295201379 52565795091361555942802069)
                    ·
                      refine ⟨2464021644907572934818847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52565795091361555942802069 2464021644907572934818847)
                      ·
                        rfl

theorem cell23_4798665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_4798665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798665 prefixEnd_4798665 := by exact prefixLift 4798665
  have htrace : WordTrace (prefixWord ++ tailWord_4798665) baseStart_4798665 baseEnd_4798665 := by
    simpa [prefixWord, tailWord_4798665, baseEnd_4798665] using wordTrace_append hprefix tailTrace_4798665
  have hstable : (prefixWord ++ tailWord_4798665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798665).length < 2 ^ (prefixWord ++ tailWord_4798665).sum := by decide
  have hdescent : baseEnd_4798665 < baseStart_4798665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798706 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_4798706 : Nat := 118140960795 + 4798706 * 2 ^ 59
def prefixEnd_4798706 : Nat := 4983230072969 + 3 ^ 40 * 4798706 * 2
def baseEnd_4798706 : Nat := 2464042697614407274406159

theorem tailTrace_4798706 : CollatzResearch.WordTrace tailWord_4798706 prefixEnd_4798706 2464042697614407274406159 := by
  unfold tailWord_4798706
  simp only [CollatzResearch.WordTrace]
  refine ⟨43755796638278797645475993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116682124368743460387935981 43755796638278797645475993)
  ·
    refine ⟨32816847478709098234106995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43755796638278797645475993 32816847478709098234106995)
    ·
      refine ⟨49225271218063647351160493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32816847478709098234106995 49225271218063647351160493)
      ·
        refine ⟨18459476706773867756685185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49225271218063647351160493 18459476706773867756685185)
        ·
          refine ⟨13844607530080400817513889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18459476706773867756685185 13844607530080400817513889)
          ·
            refine ⟨10383455647560300613135417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13844607530080400817513889 10383455647560300613135417)
            ·
              refine ⟨7787591735670225459851563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10383455647560300613135417 7787591735670225459851563)
              ·
                refine ⟨11681387603505338189777345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7787591735670225459851563 11681387603505338189777345)
                ·
                  refine ⟨8761040702629003642333009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11681387603505338189777345 8761040702629003642333009)
                  ·
                    refine ⟨6570780526971752731749757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8761040702629003642333009 6570780526971752731749757)
                    ·
                      refine ⟨2464042697614407274406159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6570780526971752731749757 2464042697614407274406159)
                      ·
                        rfl

theorem cell23_4798706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_4798706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798706 prefixEnd_4798706 := by exact prefixLift 4798706
  have htrace : WordTrace (prefixWord ++ tailWord_4798706) baseStart_4798706 baseEnd_4798706 := by
    simpa [prefixWord, tailWord_4798706, baseEnd_4798706] using wordTrace_append hprefix tailTrace_4798706
  have hstable : (prefixWord ++ tailWord_4798706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798706).length < 2 ^ (prefixWord ++ tailWord_4798706).sum := by decide
  have hdescent : baseEnd_4798706 < baseStart_4798706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798715 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 7]
def baseStart_4798715 : Nat := 118140960795 + 4798715 * 2 ^ 59
def prefixEnd_4798715 : Nat := 4983230072969 + 3 ^ 40 * 4798715 * 2
def baseEnd_4798715 : Nat := 2464047318940297739193617

theorem tailTrace_4798715 : CollatzResearch.WordTrace tailWord_4798715 prefixEnd_4798715 2464047318940297739193617 := by
  unfold tailWord_4798715
  simp only [CollatzResearch.WordTrace]
  refine ⟨175023514810082585118981599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116682343206721723412654399 175023514810082585118981599)
  ·
    refine ⟨262535272215123877678472399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175023514810082585118981599 262535272215123877678472399)
    ·
      refine ⟨393802908322685816517708599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262535272215123877678472399 393802908322685816517708599)
      ·
        refine ⟨590704362484028724776562899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393802908322685816517708599 590704362484028724776562899)
        ·
          refine ⟨886056543726043087164844349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590704362484028724776562899 886056543726043087164844349)
          ·
            refine ⟨332271203897266157686816631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 886056543726043087164844349 332271203897266157686816631)
            ·
              refine ⟨498406805845899236530224947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332271203897266157686816631 498406805845899236530224947)
              ·
                refine ⟨747610208768848854795337421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498406805845899236530224947 747610208768848854795337421)
                ·
                  refine ⟨280353828288318320548251533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747610208768848854795337421 280353828288318320548251533)
                  ·
                    refine ⟨105132685608119370205594325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280353828288318320548251533 105132685608119370205594325)
                    ·
                      refine ⟨2464047318940297739193617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105132685608119370205594325 2464047318940297739193617)
                      ·
                        rfl

theorem cell23_4798715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_4798715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798715 prefixEnd_4798715 := by exact prefixLift 4798715
  have htrace : WordTrace (prefixWord ++ tailWord_4798715) baseStart_4798715 baseEnd_4798715 := by
    simpa [prefixWord, tailWord_4798715, baseEnd_4798715] using wordTrace_append hprefix tailTrace_4798715
  have hstable : (prefixWord ++ tailWord_4798715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798715).length < 2 ^ (prefixWord ++ tailWord_4798715).sum := by decide
  have hdescent : baseEnd_4798715 < baseStart_4798715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798770 : List Nat := [3, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3]
def baseStart_4798770 : Nat := 118140960795 + 4798770 * 2 ^ 59
def prefixEnd_4798770 : Nat := 4983230072969 + 3 ^ 40 * 4798770 * 2
def baseEnd_4798770 : Nat := 2464075560376295024005865

theorem tailTrace_4798770 : CollatzResearch.WordTrace tailWord_4798770 prefixEnd_4798770 2464075560376295024005865 := by
  unfold tailWord_4798770
  simp only [CollatzResearch.WordTrace]
  refine ⟨43756380206220832378058441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116683680549922219674822509 43756380206220832378058441)
  ·
    refine ⟨32817285154665624283543831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43756380206220832378058441 32817285154665624283543831)
    ·
      refine ⟨49225927731998436425315747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32817285154665624283543831 49225927731998436425315747)
      ·
        refine ⟨73838891597997654637973621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49225927731998436425315747 73838891597997654637973621)
        ·
          refine ⟨6922396087312280122310027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73838891597997654637973621 6922396087312280122310027)
          ·
            refine ⟨10383594130968420183465041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6922396087312280122310027 10383594130968420183465041)
            ·
              refine ⟨7787695598226315137598781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10383594130968420183465041 7787695598226315137598781)
              ·
                refine ⟨2920385849334868176599543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7787695598226315137598781 2920385849334868176599543)
                ·
                  refine ⟨4380578774002302264899315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920385849334868176599543 4380578774002302264899315)
                  ·
                    refine ⟨6570868161003453397348973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4380578774002302264899315 6570868161003453397348973)
                    ·
                      refine ⟨2464075560376295024005865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6570868161003453397348973 2464075560376295024005865)
                      ·
                        rfl

theorem cell23_4798770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_4798770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798770 prefixEnd_4798770 := by exact prefixLift 4798770
  have htrace : WordTrace (prefixWord ++ tailWord_4798770) baseStart_4798770 baseEnd_4798770 := by
    simpa [prefixWord, tailWord_4798770, baseEnd_4798770] using wordTrace_append hprefix tailTrace_4798770
  have hstable : (prefixWord ++ tailWord_4798770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798770).length < 2 ^ (prefixWord ++ tailWord_4798770).sum := by decide
  have hdescent : baseEnd_4798770 < baseStart_4798770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798776 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 1, 1, 4]
def baseStart_4798776 : Nat := 118140960795 + 4798776 * 2 ^ 59
def prefixEnd_4798776 : Nat := 4983230072969 + 3 ^ 40 * 4798776 * 2
def baseEnd_4798776 : Nat := 2464078641260222000530837

theorem tailTrace_4798776 : CollatzResearch.WordTrace tailWord_4798776 prefixEnd_4798776 2464078641260222000530837 := by
  unfold tailWord_4798776
  simp only [CollatzResearch.WordTrace]
  refine ⟨87512869831430796268476091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116683826441907728357968121 87512869831430796268476091)
  ·
    refine ⟨131269304747146194402714137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87512869831430796268476091 131269304747146194402714137)
    ·
      refine ⟨98451978560359645802035603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131269304747146194402714137 98451978560359645802035603)
      ·
        refine ⟨147677967840539468703053405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98451978560359645802035603 147677967840539468703053405)
        ·
          refine ⟨55379237940202300763645027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147677967840539468703053405 55379237940202300763645027)
          ·
            refine ⟨83068856910303451145467541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55379237940202300763645027 83068856910303451145467541)
            ·
              refine ⟨3893852667670474272443791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83068856910303451145467541 3893852667670474272443791)
              ·
                refine ⟨5840779001505711408665687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3893852667670474272443791 5840779001505711408665687)
                ·
                  refine ⟨8761168502258567112998531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5840779001505711408665687 8761168502258567112998531)
                  ·
                    refine ⟨13141752753387850669497797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8761168502258567112998531 13141752753387850669497797)
                    ·
                      refine ⟨2464078641260222000530837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13141752753387850669497797 2464078641260222000530837)
                      ·
                        rfl

theorem cell23_4798776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 1, 4].length) (baseStart_4798776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798776 prefixEnd_4798776 := by exact prefixLift 4798776
  have htrace : WordTrace (prefixWord ++ tailWord_4798776) baseStart_4798776 baseEnd_4798776 := by
    simpa [prefixWord, tailWord_4798776, baseEnd_4798776] using wordTrace_append hprefix tailTrace_4798776
  have hstable : (prefixWord ++ tailWord_4798776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798776).length < 2 ^ (prefixWord ++ tailWord_4798776).sum := by decide
  have hdescent : baseEnd_4798776 < baseStart_4798776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798816 : List Nat := [2, 1, 1, 3, 5, 2, 2, 7]
def baseStart_4798816 : Nat := 118140960795 + 4798816 * 2 ^ 59
def prefixEnd_4798816 : Nat := 4983230072969 + 3 ^ 40 * 4798816 * 2
def baseEnd_4798816 : Nat := 91262932610607475704839

theorem tailTrace_4798816 : CollatzResearch.WordTrace tailWord_4798816 prefixEnd_4798816 91262932610607475704839 := by
  unfold tailWord_4798816
  simp only [CollatzResearch.WordTrace]
  refine ⟨87513599291358339684204151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116684799055144452912272201 87513599291358339684204151)
  ·
    refine ⟨131270398937037509526306227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87513599291358339684204151 131270398937037509526306227)
    ·
      refine ⟨196905598405556264289459341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131270398937037509526306227 196905598405556264289459341)
      ·
        refine ⟨73839599402083599108547253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196905598405556264289459341 73839599402083599108547253)
        ·
          refine ⟨6922462443945337416426305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73839599402083599108547253 6922462443945337416426305)
          ·
            refine ⟨5191846832959003062319729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6922462443945337416426305 5191846832959003062319729)
            ·
              refine ⟨3893885124719252296739797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5191846832959003062319729 3893885124719252296739797)
              ·
                refine ⟨91262932610607475704839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3893885124719252296739797 91262932610607475704839)
                ·
                  rfl

theorem cell23_4798816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 7].length) (baseStart_4798816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798816 prefixEnd_4798816 := by exact prefixLift 4798816
  have htrace : WordTrace (prefixWord ++ tailWord_4798816) baseStart_4798816 baseEnd_4798816 := by
    simpa [prefixWord, tailWord_4798816, baseEnd_4798816] using wordTrace_append hprefix tailTrace_4798816
  have hstable : (prefixWord ++ tailWord_4798816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798816).length < 2 ^ (prefixWord ++ tailWord_4798816).sum := by decide
  have hdescent : baseEnd_4798816 < baseStart_4798816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798860 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 2, 1, 3]
def baseStart_4798860 : Nat := 118140960795 + 4798860 * 2 ^ 59
def prefixEnd_4798860 : Nat := 4983230072969 + 3 ^ 40 * 4798860 * 2
def baseEnd_4798860 : Nat := 2464121773635199671880451

theorem tailTrace_4798860 : CollatzResearch.WordTrace tailWord_4798860 prefixEnd_4798860 2464121773635199671880451 := by
  unfold tailWord_4798860
  simp only [CollatzResearch.WordTrace]
  refine ⟨87514401697278637441505017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116685868929704849922006689 87514401697278637441505017)
  ·
    refine ⟨65635801272958978081128763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87514401697278637441505017 65635801272958978081128763)
    ·
      refine ⟨98453701909438467121693145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65635801272958978081128763 98453701909438467121693145)
      ·
        refine ⟨73840276432078850341269859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98453701909438467121693145 73840276432078850341269859)
        ·
          refine ⟨110760414648118275511904789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73840276432078850341269859 110760414648118275511904789)
          ·
            refine ⟨5191894436630544164620537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110760414648118275511904789 5191894436630544164620537)
            ·
              refine ⟨3893920827472908123465403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5191894436630544164620537 3893920827472908123465403)
              ·
                refine ⟨5840881241209362185198105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3893920827472908123465403 5840881241209362185198105)
                ·
                  refine ⟨4380660930907021638898579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5840881241209362185198105 4380660930907021638898579)
                  ·
                    refine ⟨6570991396360532458347869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4380660930907021638898579 6570991396360532458347869)
                    ·
                      refine ⟨2464121773635199671880451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6570991396360532458347869 2464121773635199671880451)
                      ·
                        rfl

theorem cell23_4798860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_4798860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798860 prefixEnd_4798860 := by exact prefixLift 4798860
  have htrace : WordTrace (prefixWord ++ tailWord_4798860) baseStart_4798860 baseEnd_4798860 := by
    simpa [prefixWord, tailWord_4798860, baseEnd_4798860] using wordTrace_append hprefix tailTrace_4798860
  have hstable : (prefixWord ++ tailWord_4798860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798860).length < 2 ^ (prefixWord ++ tailWord_4798860).sum := by decide
  have hdescent : baseEnd_4798860 < baseStart_4798860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798926 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2]
def baseStart_4798926 : Nat := 118140960795 + 4798926 * 2 ^ 59
def prefixEnd_4798926 : Nat := 4983230072969 + 3 ^ 40 * 4798926 * 2
def baseEnd_4798926 : Nat := 2464155663358396413655147

theorem tailTrace_4798926 : CollatzResearch.WordTrace tailWord_4798926 prefixEnd_4798926 2464155663358396413655147 := by
  unfold tailWord_4798926
  simp only [CollatzResearch.WordTrace]
  refine ⟨21878901326539771019364079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116687473741545445436608421 21878901326539771019364079)
  ·
    refine ⟨32818351989809656529046119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21878901326539771019364079 32818351989809656529046119)
    ·
      refine ⟨49227527984714484793569179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32818351989809656529046119 49227527984714484793569179)
      ·
        refine ⟨73841291977071727190353769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49227527984714484793569179 73841291977071727190353769)
        ·
          refine ⟨55380968982803795392765327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73841291977071727190353769 55380968982803795392765327)
          ·
            refine ⟨83071453474205693089147991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55380968982803795392765327 83071453474205693089147991)
            ·
              refine ⟨124607180211308539633721987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83071453474205693089147991 124607180211308539633721987)
              ·
                refine ⟨186910770316962809450582981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124607180211308539633721987 186910770316962809450582981)
                ·
                  refine ⟨35045769434430526771984309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186910770316962809450582981 35045769434430526771984309)
                  ·
                    refine ⟨3285540884477861884873529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35045769434430526771984309 3285540884477861884873529)
                    ·
                      refine ⟨2464155663358396413655147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285540884477861884873529 2464155663358396413655147)
                      ·
                        rfl

theorem cell23_4798926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_4798926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798926 prefixEnd_4798926 := by exact prefixLift 4798926
  have htrace : WordTrace (prefixWord ++ tailWord_4798926) baseStart_4798926 baseEnd_4798926 := by
    simpa [prefixWord, tailWord_4798926, baseEnd_4798926] using wordTrace_append hprefix tailTrace_4798926
  have hstable : (prefixWord ++ tailWord_4798926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798926).length < 2 ^ (prefixWord ++ tailWord_4798926).sum := by decide
  have hdescent : baseEnd_4798926 < baseStart_4798926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4798956 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 4, 4, 2]
def baseStart_4798956 : Nat := 118140960795 + 4798956 * 2 ^ 59
def prefixEnd_4798956 : Nat := 4983230072969 + 3 ^ 40 * 4798956 * 2
def baseEnd_4798956 : Nat := 2464171067778031296280009

theorem tailTrace_4798956 : CollatzResearch.WordTrace tailWord_4798956 prefixEnd_4798956 2464171067778031296280009 := by
  unfold tailWord_4798956
  simp only [CollatzResearch.WordTrace]
  refine ⟨87516152401104741639252361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116688203201472988852336481 87516152401104741639252361)
  ·
    refine ⟨65637114300828556229439271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87516152401104741639252361 65637114300828556229439271)
    ·
      refine ⟨98455671451242834344158907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65637114300828556229439271 98455671451242834344158907)
      ·
        refine ⟨147683507176864251516238361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98455671451242834344158907 147683507176864251516238361)
        ·
          refine ⟨110762630382648188637178771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147683507176864251516238361 110762630382648188637178771)
          ·
            refine ⟨166143945573972282955768157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110762630382648188637178771 166143945573972282955768157)
            ·
              refine ⟨62303979590239606108413059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166143945573972282955768157 62303979590239606108413059)
              ·
                refine ⟨93455969385359409162619589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62303979590239606108413059 93455969385359409162619589)
                ·
                  refine ⟨17522994259754889217991173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93455969385359409162619589 17522994259754889217991173)
                  ·
                    refine ⟨3285561423704041728373345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17522994259754889217991173 3285561423704041728373345)
                    ·
                      refine ⟨2464171067778031296280009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285561423704041728373345 2464171067778031296280009)
                      ·
                        rfl

theorem cell23_4798956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 4, 2].length) (baseStart_4798956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4798956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4798956 prefixEnd_4798956 := by exact prefixLift 4798956
  have htrace : WordTrace (prefixWord ++ tailWord_4798956) baseStart_4798956 baseEnd_4798956 := by
    simpa [prefixWord, tailWord_4798956, baseEnd_4798956] using wordTrace_append hprefix tailTrace_4798956
  have hstable : (prefixWord ++ tailWord_4798956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4798956).length < 2 ^ (prefixWord ++ tailWord_4798956).sum := by decide
  have hdescent : baseEnd_4798956 < baseStart_4798956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4798956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799000 : List Nat := [2, 1, 2, 3, 3, 1, 3, 3, 1, 4]
def baseStart_4799000 : Nat := 118140960795 + 4799000 * 2 ^ 59
def prefixEnd_4799000 : Nat := 4983230072969 + 3 ^ 40 * 4799000 * 2
def baseEnd_4799000 : Nat := 821397886975609708043269

theorem tailTrace_4799000 : CollatzResearch.WordTrace tailWord_4799000 prefixEnd_4799000 821397886975609708043269 := by
  unfold tailWord_4799000
  simp only [CollatzResearch.WordTrace]
  refine ⟨87516954807025039396553227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116689273076033385862070969 87516954807025039396553227)
  ·
    refine ⟨131275432210537559094829841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87516954807025039396553227 131275432210537559094829841)
    ·
      refine ⟨98456574157903169321122381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131275432210537559094829841 98456574157903169321122381)
      ·
        refine ⟨36921215309213688495420893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98456574157903169321122381 36921215309213688495420893)
        ·
          refine ⟨13845455740955133185782835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36921215309213688495420893 13845455740955133185782835)
          ·
            refine ⟨20768183611432699778674253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13845455740955133185782835 20768183611432699778674253)
            ·
              refine ⟨7788068854287262417002845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20768183611432699778674253 7788068854287262417002845)
              ·
                refine ⟨2920525820357723406376067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7788068854287262417002845 2920525820357723406376067)
                ·
                  refine ⟨4380788730536585109564101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920525820357723406376067 4380788730536585109564101)
                  ·
                    refine ⟨821397886975609708043269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4380788730536585109564101 821397886975609708043269)
                    ·
                      rfl

theorem cell23_4799000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_4799000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799000 prefixEnd_4799000 := by exact prefixLift 4799000
  have htrace : WordTrace (prefixWord ++ tailWord_4799000) baseStart_4799000 baseEnd_4799000 := by
    simpa [prefixWord, tailWord_4799000, baseEnd_4799000] using wordTrace_append hprefix tailTrace_4799000
  have hstable : (prefixWord ++ tailWord_4799000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799000).length < 2 ^ (prefixWord ++ tailWord_4799000).sum := by decide
  have hdescent : baseEnd_4799000 < baseStart_4799000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799030 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_4799030 : Nat := 118140960795 + 4799030 * 2 ^ 59
def prefixEnd_4799030 : Nat := 4983230072969 + 3 ^ 40 * 4799030 * 2
def baseEnd_4799030 : Nat := 273801007260718222972741

theorem tailTrace_4799030 : CollatzResearch.WordTrace tailWord_4799030 prefixEnd_4799030 273801007260718222972741 := by
  unfold tailWord_4799030
  simp only [CollatzResearch.WordTrace]
  refine ⟨10939687737746337119793659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116690002535960929277799029 10939687737746337119793659)
  ·
    refine ⟨16409531606619505679690489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10939687737746337119793659 16409531606619505679690489)
    ·
      refine ⟨12307148704964629259767867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16409531606619505679690489 12307148704964629259767867)
      ·
        refine ⟨18460723057446943889651801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12307148704964629259767867 18460723057446943889651801)
        ·
          refine ⟨13845542293085207917238851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18460723057446943889651801 13845542293085207917238851)
          ·
            refine ⟨20768313439627811875858277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13845542293085207917238851 20768313439627811875858277)
            ·
              refine ⟨3894058769930214726723427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20768313439627811875858277 3894058769930214726723427)
              ·
                refine ⟨5841088154895322090085141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3894058769930214726723427 5841088154895322090085141)
                ·
                  refine ⟨273801007260718222972741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5841088154895322090085141 273801007260718222972741)
                  ·
                    rfl

theorem cell23_4799030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_4799030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799030 prefixEnd_4799030 := by exact prefixLift 4799030
  have htrace : WordTrace (prefixWord ++ tailWord_4799030) baseStart_4799030 baseEnd_4799030 := by
    simpa [prefixWord, tailWord_4799030, baseEnd_4799030] using wordTrace_append hprefix tailTrace_4799030
  have hstable : (prefixWord ++ tailWord_4799030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799030).length < 2 ^ (prefixWord ++ tailWord_4799030).sum := by decide
  have hdescent : baseEnd_4799030 < baseStart_4799030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799033 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 4, 3, 2]
def baseStart_4799033 : Nat := 118140960795 + 4799033 * 2 ^ 59
def prefixEnd_4799033 : Nat := 4983230072969 + 3 ^ 40 * 4799033 * 2
def baseEnd_4799033 : Nat := 2464210605788427495017155

theorem tailTrace_4799033 : CollatzResearch.WordTrace tailWord_4799033 prefixEnd_4799033 2464210605788427495017155 := by
  unfold tailWord_4799033
  simp only [CollatzResearch.WordTrace]
  refine ⟨175035113222930525429057753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116690075481953683619371835 175035113222930525429057753)
  ·
    refine ⟨131276334917197894071793315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175035113222930525429057753 131276334917197894071793315)
    ·
      refine ⟨196914502375796841107689973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131276334917197894071793315 196914502375796841107689973)
      ·
        refine ⟨18460734597730953853845935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 196914502375796841107689973 18460734597730953853845935)
        ·
          refine ⟨27691101896596430780768903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18460734597730953853845935 27691101896596430780768903)
          ·
            refine ⟨41536652844894646171153355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27691101896596430780768903 41536652844894646171153355)
            ·
              refine ⟨62304979267341969256730033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41536652844894646171153355 62304979267341969256730033)
              ·
                refine ⟨46728734450506476942547525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62304979267341969256730033 46728734450506476942547525)
                ·
                  refine ⟨8761637709469964426727661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46728734450506476942547525 8761637709469964426727661)
                  ·
                    refine ⟨3285614141051236660022873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8761637709469964426727661 3285614141051236660022873)
                    ·
                      refine ⟨2464210605788427495017155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285614141051236660022873 2464210605788427495017155)
                      ·
                        rfl

theorem cell23_4799033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_4799033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799033 prefixEnd_4799033 := by exact prefixLift 4799033
  have htrace : WordTrace (prefixWord ++ tailWord_4799033) baseStart_4799033 baseEnd_4799033 := by
    simpa [prefixWord, tailWord_4799033, baseEnd_4799033] using wordTrace_append hprefix tailTrace_4799033
  have hstable : (prefixWord ++ tailWord_4799033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799033).length < 2 ^ (prefixWord ++ tailWord_4799033).sum := by decide
  have hdescent : baseEnd_4799033 < baseStart_4799033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799044 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4799044 : Nat := 118140960795 + 4799044 * 2 ^ 59
def prefixEnd_4799044 : Nat := 4983230072969 + 3 ^ 40 * 4799044 * 2
def baseEnd_4799044 : Nat := 2464216254075626951979605

theorem tailTrace_4799044 : CollatzResearch.WordTrace tailWord_4799044 prefixEnd_4799044 2464216254075626951979605 := by
  unfold tailWord_4799044
  simp only [CollatzResearch.WordTrace]
  refine ⟨87517757212945337153854093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116690342950593782871805457 87517757212945337153854093)
  ·
    refine ⟨32819158954854501432695285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87517757212945337153854093 32819158954854501432695285)
    ·
      refine ⟨3076796152017609509315183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32819158954854501432695285 3076796152017609509315183)
      ·
        refine ⟨4615194228026414263972775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076796152017609509315183 4615194228026414263972775)
        ·
          refine ⟨6922791342039621395959163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4615194228026414263972775 6922791342039621395959163)
          ·
            refine ⟨10384187013059432093938745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6922791342039621395959163 10384187013059432093938745)
            ·
              refine ⟨7788140259794574070454059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10384187013059432093938745 7788140259794574070454059)
              ·
                refine ⟨11682210389691861105681089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7788140259794574070454059 11682210389691861105681089)
                ·
                  refine ⟨8761657792268895829260817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11682210389691861105681089 8761657792268895829260817)
                  ·
                    refine ⟨6571243344201671871945613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8761657792268895829260817 6571243344201671871945613)
                    ·
                      refine ⟨2464216254075626951979605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6571243344201671871945613 2464216254075626951979605)
                      ·
                        rfl

theorem cell23_4799044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4799044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799044 prefixEnd_4799044 := by exact prefixLift 4799044
  have htrace : WordTrace (prefixWord ++ tailWord_4799044) baseStart_4799044 baseEnd_4799044 := by
    simpa [prefixWord, tailWord_4799044, baseEnd_4799044] using wordTrace_append hprefix tailTrace_4799044
  have hstable : (prefixWord ++ tailWord_4799044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799044).length < 2 ^ (prefixWord ++ tailWord_4799044).sum := by decide
  have hdescent : baseEnd_4799044 < baseStart_4799044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799049 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_4799049 : Nat := 118140960795 + 4799049 * 2 ^ 59
def prefixEnd_4799049 : Nat := 4983230072969 + 3 ^ 40 * 4799049 * 2
def baseEnd_4799049 : Nat := 2464218821478899432417081

theorem tailTrace_4799049 : CollatzResearch.WordTrace tailWord_4799049 prefixEnd_4799049 2464218821478899432417081 := by
  unfold tailWord_4799049
  simp only [CollatzResearch.WordTrace]
  refine ⟨175035696790872560161640201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116690464527248373441093467 175035696790872560161640201)
  ·
    refine ⟨131276772593154420121230151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175035696790872560161640201 131276772593154420121230151)
    ·
      refine ⟨196915158889731630181845227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131276772593154420121230151 196915158889731630181845227)
      ·
        refine ⟨295372738334597445272767841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196915158889731630181845227 295372738334597445272767841)
        ·
          refine ⟨221529553750948083954575881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295372738334597445272767841 221529553750948083954575881)
          ·
            refine ⟨166147165313211062965931911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221529553750948083954575881 166147165313211062965931911)
            ·
              refine ⟨249220747969816594448897867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166147165313211062965931911 249220747969816594448897867)
              ·
                refine ⟨373831121954724891673346801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249220747969816594448897867 373831121954724891673346801)
                ·
                  refine ⟨280373341466043668755010101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373831121954724891673346801 280373341466043668755010101)
                  ·
                    refine ⟨26285000762441593945782197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 280373341466043668755010101 26285000762441593945782197)
                    ·
                      refine ⟨2464218821478899432417081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26285000762441593945782197 2464218821478899432417081)
                      ·
                        rfl

theorem cell23_4799049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_4799049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799049 prefixEnd_4799049 := by exact prefixLift 4799049
  have htrace : WordTrace (prefixWord ++ tailWord_4799049) baseStart_4799049 baseEnd_4799049 := by
    simpa [prefixWord, tailWord_4799049, baseEnd_4799049] using wordTrace_append hprefix tailTrace_4799049
  have hstable : (prefixWord ++ tailWord_4799049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799049).length < 2 ^ (prefixWord ++ tailWord_4799049).sum := by decide
  have hdescent : baseEnd_4799049 < baseStart_4799049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799050 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2]
def baseStart_4799050 : Nat := 118140960795 + 4799050 * 2 ^ 59
def prefixEnd_4799050 : Nat := 4983230072969 + 3 ^ 40 * 4799050 * 2
def baseEnd_4799050 : Nat := 2464219334959553928504577

theorem tailTrace_4799050 : CollatzResearch.WordTrace tailWord_4799050 prefixEnd_4799050 2464219334959553928504577 := by
  unfold tailWord_4799050
  simp only [CollatzResearch.WordTrace]
  refine ⟨43758933315967234333106651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116690488842579291554951069 43758933315967234333106651)
  ·
    refine ⟨65638399973950851499659977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43758933315967234333106651 65638399973950851499659977)
    ·
      refine ⟨49228799980463138624744983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65638399973950851499659977 49228799980463138624744983)
      ·
        refine ⟨73843199970694707937117475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49228799980463138624744983 73843199970694707937117475)
        ·
          refine ⟨110764799956042061905676213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73843199970694707937117475 110764799956042061905676213)
          ·
            refine ⟨10384199995878943303657145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110764799956042061905676213 10384199995878943303657145)
            ·
              refine ⟨7788149996909207477742859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10384199995878943303657145 7788149996909207477742859)
              ·
                refine ⟨11682224995363811216614289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7788149996909207477742859 11682224995363811216614289)
                ·
                  refine ⟨8761668746522858412460717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11682224995363811216614289 8761668746522858412460717)
                  ·
                    refine ⟨3285625779946071904672769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8761668746522858412460717 3285625779946071904672769)
                    ·
                      refine ⟨2464219334959553928504577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285625779946071904672769 2464219334959553928504577)
                      ·
                        rfl

theorem cell23_4799050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_4799050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799050 prefixEnd_4799050 := by exact prefixLift 4799050
  have htrace : WordTrace (prefixWord ++ tailWord_4799050) baseStart_4799050 baseEnd_4799050 := by
    simpa [prefixWord, tailWord_4799050, baseEnd_4799050] using wordTrace_append hprefix tailTrace_4799050
  have hstable : (prefixWord ++ tailWord_4799050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799050).length < 2 ^ (prefixWord ++ tailWord_4799050).sum := by decide
  have hdescent : baseEnd_4799050 < baseStart_4799050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799056 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 4, 4]
def baseStart_4799056 : Nat := 118140960795 + 4799056 * 2 ^ 59
def prefixEnd_4799056 : Nat := 4983230072969 + 3 ^ 40 * 4799056 * 2
def baseEnd_4799056 : Nat := 821407471947826968343183

theorem tailTrace_4799056 : CollatzResearch.WordTrace tailWord_4799056 prefixEnd_4799056 821407471947826968343183 := by
  unfold tailWord_4799056
  simp only [CollatzResearch.WordTrace]
  refine ⟨87517976050923600178572511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116690634734564800238096681 87517976050923600178572511)
  ·
    refine ⟨131276964076385400267858767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87517976050923600178572511 131276964076385400267858767)
    ·
      refine ⟨196915446114578100401788151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131276964076385400267858767 196915446114578100401788151)
      ·
        refine ⟨295373169171867150602682227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196915446114578100401788151 295373169171867150602682227)
        ·
          refine ⟨443059753757800725904023341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295373169171867150602682227 443059753757800725904023341)
          ·
            refine ⟨166147407659175272214008753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 443059753757800725904023341 166147407659175272214008753)
            ·
              refine ⟨124610555744381454160506565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166147407659175272214008753 124610555744381454160506565)
              ·
                refine ⟨23364479202071522655094981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124610555744381454160506565 23364479202071522655094981)
                ·
                  refine ⟨4380839850388410497830309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23364479202071522655094981 4380839850388410497830309)
                  ·
                    refine ⟨821407471947826968343183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4380839850388410497830309 821407471947826968343183)
                    ·
                      rfl

theorem cell23_4799056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4, 4].length) (baseStart_4799056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799056 prefixEnd_4799056 := by exact prefixLift 4799056
  have htrace : WordTrace (prefixWord ++ tailWord_4799056) baseStart_4799056 baseEnd_4799056 := by
    simpa [prefixWord, tailWord_4799056, baseEnd_4799056] using wordTrace_append hprefix tailTrace_4799056
  have hstable : (prefixWord ++ tailWord_4799056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799056).length < 2 ^ (prefixWord ++ tailWord_4799056).sum := by decide
  have hdescent : baseEnd_4799056 < baseStart_4799056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799060 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_4799060 : Nat := 118140960795 + 4799060 * 2 ^ 59
def prefixEnd_4799060 : Nat := 4983230072969 + 3 ^ 40 * 4799060 * 2
def baseEnd_4799060 : Nat := 821408156588699629793177

theorem tailTrace_4799060 : CollatzResearch.WordTrace tailWord_4799060 prefixEnd_4799060 821408156588699629793177 := by
  unfold tailWord_4799060
  simp only [CollatzResearch.WordTrace]
  refine ⟨87518048996916354520145317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116690731995888472693527089 87518048996916354520145317)
  ·
    refine ⟨16409634186921816472527247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87518048996916354520145317 16409634186921816472527247)
    ·
      refine ⟨24614451280382724708790871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16409634186921816472527247 24614451280382724708790871)
      ·
        refine ⟨36921676920574087063186307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24614451280382724708790871 36921676920574087063186307)
        ·
          refine ⟨55382515380861130594779461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36921676920574087063186307 55382515380861130594779461)
          ·
            refine ⟨10384221633911461986521149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55382515380861130594779461 10384221633911461986521149)
            ·
              refine ⟨3894083112716798244945431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10384221633911461986521149 3894083112716798244945431)
              ·
                refine ⟨5841124669075197367418147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3894083112716798244945431 5841124669075197367418147)
                ·
                  refine ⟨8761687003612796051127221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5841124669075197367418147 8761687003612796051127221)
                  ·
                    refine ⟨821408156588699629793177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8761687003612796051127221 821408156588699629793177)
                    ·
                      rfl

theorem cell23_4799060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_4799060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799060 prefixEnd_4799060 := by exact prefixLift 4799060
  have htrace : WordTrace (prefixWord ++ tailWord_4799060) baseStart_4799060 baseEnd_4799060 := by
    simpa [prefixWord, tailWord_4799060, baseEnd_4799060] using wordTrace_append hprefix tailTrace_4799060
  have hstable : (prefixWord ++ tailWord_4799060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799060).length < 2 ^ (prefixWord ++ tailWord_4799060).sum := by decide
  have hdescent : baseEnd_4799060 < baseStart_4799060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799073 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 2, 4]
def baseStart_4799073 : Nat := 118140960795 + 4799073 * 2 ^ 59
def prefixEnd_4799073 : Nat := 4983230072969 + 3 ^ 40 * 4799073 * 2
def baseEnd_4799073 : Nat := 821410381671535779505657

theorem tailTrace_4799073 : CollatzResearch.WordTrace tailWord_4799073 prefixEnd_4799073 821410381671535779505657 := by
  unfold tailWord_4799073
  simp only [CollatzResearch.WordTrace]
  refine ⟨175036572142785612260513873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116691048095190408173675915 175036572142785612260513873)
  ·
    refine ⟨131277429107089209195385405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175036572142785612260513873 131277429107089209195385405)
    ·
      refine ⟨49229035915158453448269527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131277429107089209195385405 49229035915158453448269527)
      ·
        refine ⟨73843553872737680172404291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49229035915158453448269527 73843553872737680172404291)
        ·
          refine ⟨110765330809106520258606437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73843553872737680172404291 110765330809106520258606437)
          ·
            refine ⟨20768499526707472548488707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110765330809106520258606437 20768499526707472548488707)
            ·
              refine ⟨31152749290061208822733061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20768499526707472548488707 31152749290061208822733061)
              ·
                refine ⟨5841140491886476654262449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31152749290061208822733061 5841140491886476654262449)
                ·
                  refine ⟨4380855368914857490696837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5841140491886476654262449 4380855368914857490696837)
                  ·
                    refine ⟨821410381671535779505657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4380855368914857490696837 821410381671535779505657)
                    ·
                      rfl

theorem cell23_4799073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_4799073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799073 prefixEnd_4799073 := by exact prefixLift 4799073
  have htrace : WordTrace (prefixWord ++ tailWord_4799073) baseStart_4799073 baseEnd_4799073 := by
    simpa [prefixWord, tailWord_4799073, baseEnd_4799073] using wordTrace_append hprefix tailTrace_4799073
  have hstable : (prefixWord ++ tailWord_4799073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799073).length < 2 ^ (prefixWord ++ tailWord_4799073).sum := by decide
  have hdescent : baseEnd_4799073 < baseStart_4799073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799076 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_4799076 : Nat := 118140960795 + 4799076 * 2 ^ 59
def prefixEnd_4799076 : Nat := 4983230072969 + 3 ^ 40 * 4799076 * 2
def baseEnd_4799076 : Nat := 2464232685456570826779457

theorem tailTrace_4799076 : CollatzResearch.WordTrace tailWord_4799076 prefixEnd_4799076 2464232685456570826779457 := by
  unfold tailWord_4799076
  simp only [CollatzResearch.WordTrace]
  refine ⟨87518340780887371886436541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116691121041183162515248721 87518340780887371886436541)
  ·
    refine ⟨32819377792832764457413703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87518340780887371886436541 32819377792832764457413703)
    ·
      refine ⟨49229066689249146686120555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32819377792832764457413703 49229066689249146686120555)
      ·
        refine ⟨73843600033873720029180833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49229066689249146686120555 73843600033873720029180833)
        ·
          refine ⟨55382700025405290021885625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73843600033873720029180833 55382700025405290021885625)
          ·
            refine ⟨41537025019053967516414219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55382700025405290021885625 41537025019053967516414219)
            ·
              refine ⟨62305537528580951274621329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41537025019053967516414219 62305537528580951274621329)
              ·
                refine ⟨46729153146435713455965997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62305537528580951274621329 46729153146435713455965997)
                ·
                  refine ⟨17523432429913392545987249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46729153146435713455965997 17523432429913392545987249)
                  ·
                    refine ⟨13142574322435044409490437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17523432429913392545987249 13142574322435044409490437)
                    ·
                      refine ⟨2464232685456570826779457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13142574322435044409490437 2464232685456570826779457)
                      ·
                        rfl

theorem cell23_4799076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_4799076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799076 prefixEnd_4799076 := by exact prefixLift 4799076
  have htrace : WordTrace (prefixWord ++ tailWord_4799076) baseStart_4799076 baseEnd_4799076 := by
    simpa [prefixWord, tailWord_4799076, baseEnd_4799076] using wordTrace_append hprefix tailTrace_4799076
  have hstable : (prefixWord ++ tailWord_4799076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799076).length < 2 ^ (prefixWord ++ tailWord_4799076).sum := by decide
  have hdescent : baseEnd_4799076 < baseStart_4799076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799096 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 5, 3, 3]
def baseStart_4799096 : Nat := 118140960795 + 4799096 * 2 ^ 59
def prefixEnd_4799096 : Nat := 4983230072969 + 3 ^ 40 * 4799096 * 2
def baseEnd_4799096 : Nat := 2464242955069660748529365

theorem tailTrace_4799096 : CollatzResearch.WordTrace tailWord_4799096 prefixEnd_4799096 2464242955069660748529365 := by
  unfold tailWord_4799096
  simp only [CollatzResearch.WordTrace]
  refine ⟨87518705510851143594300571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116691607347801524792400761 87518705510851143594300571)
  ·
    refine ⟨131278058266276715391450857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87518705510851143594300571 131278058266276715391450857)
    ·
      refine ⟨98458543699707536543588143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131278058266276715391450857 98458543699707536543588143)
      ·
        refine ⟨147687815549561304815382215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98458543699707536543588143 147687815549561304815382215)
        ·
          refine ⟨221531723324341957223073323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147687815549561304815382215 221531723324341957223073323)
          ·
            refine ⟨332297584986512935834609985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221531723324341957223073323 332297584986512935834609985)
            ·
              refine ⟨249223188739884701875957489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332297584986512935834609985 249223188739884701875957489)
              ·
                refine ⟨186917391554913526406968117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249223188739884701875957489 186917391554913526406968117)
                ·
                  refine ⟨17523505458273143100653261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 186917391554913526406968117 17523505458273143100653261)
                  ·
                    refine ⟨6571314546852428662744973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17523505458273143100653261 6571314546852428662744973)
                    ·
                      refine ⟨2464242955069660748529365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6571314546852428662744973 2464242955069660748529365)
                      ·
                        rfl

theorem cell23_4799096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_4799096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799096 prefixEnd_4799096 := by exact prefixLift 4799096
  have htrace : WordTrace (prefixWord ++ tailWord_4799096) baseStart_4799096 baseEnd_4799096 := by
    simpa [prefixWord, tailWord_4799096, baseEnd_4799096] using wordTrace_append hprefix tailTrace_4799096
  have hstable : (prefixWord ++ tailWord_4799096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799096).length < 2 ^ (prefixWord ++ tailWord_4799096).sum := by decide
  have hdescent : baseEnd_4799096 < baseStart_4799096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799113 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 4, 1, 3]
def baseStart_4799113 : Nat := 118140960795 + 4799113 * 2 ^ 59
def prefixEnd_4799113 : Nat := 4983230072969 + 3 ^ 40 * 4799113 * 2
def baseEnd_4799113 : Nat := 2464251684240787182016787

theorem tailTrace_4799113 : CollatzResearch.WordTrace tailWord_4799113 prefixEnd_4799113 2464251684240787182016787 := by
  unfold tailWord_4799113
  simp only [CollatzResearch.WordTrace]
  refine ⟨175038031062640699091969993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116692020708427132727979995 175038031062640699091969993)
  ·
    refine ⟨131278523296980524318977495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175038031062640699091969993 131278523296980524318977495)
    ·
      refine ⟨196917784945470786478466243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131278523296980524318977495 196917784945470786478466243)
      ·
        refine ⟨295376677418206179717699365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196917784945470786478466243 295376677418206179717699365)
        ·
          refine ⟨55383127015913658697068631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 295376677418206179717699365 55383127015913658697068631)
          ·
            refine ⟨83074690523870488045602947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55383127015913658697068631 83074690523870488045602947)
            ·
              refine ⟨124612035785805732068404421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83074690523870488045602947 124612035785805732068404421)
              ·
                refine ⟨23364756709838574762825829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124612035785805732068404421 23364756709838574762825829)
                ·
                  refine ⟨4380891883094732768029843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23364756709838574762825829 4380891883094732768029843)
                  ·
                    refine ⟨6571337824642099152044765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4380891883094732768029843 6571337824642099152044765)
                    ·
                      refine ⟨2464251684240787182016787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6571337824642099152044765 2464251684240787182016787)
                      ·
                        rfl

theorem cell23_4799113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 1, 3].length) (baseStart_4799113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799113 prefixEnd_4799113 := by exact prefixLift 4799113
  have htrace : WordTrace (prefixWord ++ tailWord_4799113) baseStart_4799113 baseEnd_4799113 := by
    simpa [prefixWord, tailWord_4799113, baseEnd_4799113] using wordTrace_append hprefix tailTrace_4799113
  have hstable : (prefixWord ++ tailWord_4799113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799113).length < 2 ^ (prefixWord ++ tailWord_4799113).sum := by decide
  have hdescent : baseEnd_4799113 < baseStart_4799113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799114 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4]
def baseStart_4799114 : Nat := 118140960795 + 4799114 * 2 ^ 59
def prefixEnd_4799114 : Nat := 4983230072969 + 3 ^ 40 * 4799114 * 2
def baseEnd_4799114 : Nat := 2464252197721441678104283

theorem tailTrace_4799114 : CollatzResearch.WordTrace tailWord_4799114 prefixEnd_4799114 2464252197721441678104283 := by
  unfold tailWord_4799114
  simp only [CollatzResearch.WordTrace]
  refine ⟨43759516883909269065689099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116692045023758050841837597 43759516883909269065689099)
  ·
    refine ⟨65639275325863903598533649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43759516883909269065689099 65639275325863903598533649)
    ·
      refine ⟨49229456494397927698900237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65639275325863903598533649 49229456494397927698900237)
      ·
        refine ⟨18461046185399222887087589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49229456494397927698900237 18461046185399222887087589)
        ·
          refine ⟨3461446159762354291328923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18461046185399222887087589 3461446159762354291328923)
          ·
            refine ⟨5192169239643531436993385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3461446159762354291328923 5192169239643531436993385)
            ·
              refine ⟨3894126929732648577745039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5192169239643531436993385 3894126929732648577745039)
              ·
                refine ⟨5841190394598972866617559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3894126929732648577745039 5841190394598972866617559)
                ·
                  refine ⟨8761785591898459299926339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5841190394598972866617559 8761785591898459299926339)
                  ·
                    refine ⟨13142678387847688949889509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8761785591898459299926339 13142678387847688949889509)
                    ·
                      refine ⟨2464252197721441678104283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13142678387847688949889509 2464252197721441678104283)
                      ·
                        rfl

theorem cell23_4799114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_4799114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799114 prefixEnd_4799114 := by exact prefixLift 4799114
  have htrace : WordTrace (prefixWord ++ tailWord_4799114) baseStart_4799114 baseEnd_4799114 := by
    simpa [prefixWord, tailWord_4799114, baseEnd_4799114] using wordTrace_append hprefix tailTrace_4799114
  have hstable : (prefixWord ++ tailWord_4799114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799114).length < 2 ^ (prefixWord ++ tailWord_4799114).sum := by decide
  have hdescent : baseEnd_4799114 < baseStart_4799114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799157 : List Nat := [1, 3, 3, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_4799157 : Nat := 118140960795 + 4799157 * 2 ^ 59
def prefixEnd_4799157 : Nat := 4983230072969 + 3 ^ 40 * 4799157 * 2
def baseEnd_4799157 : Nat := 2464274277389585009866585

theorem tailTrace_4799157 : CollatzResearch.WordTrace tailWord_4799157 prefixEnd_4799157 2464274277389585009866585 := by
  unfold tailWord_4799157
  simp only [CollatzResearch.WordTrace]
  refine ⟨175039635874481294606571725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116693090582987529737714483 175039635874481294606571725)
  ·
    refine ⟨65639863452930485477464397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175039635874481294606571725 65639863452930485477464397)
    ·
      refine ⟨24614948794848932054049149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65639863452930485477464397 24614948794848932054049149)
      ·
        refine ⟨9230605798068349520268431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24614948794848932054049149 9230605798068349520268431)
        ·
          refine ⟨13845908697102524280402647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9230605798068349520268431 13845908697102524280402647)
          ·
            refine ⟨20768863045653786420603971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13845908697102524280402647 20768863045653786420603971)
            ·
              refine ⟨31153294568480679630905957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20768863045653786420603971 31153294568480679630905957)
              ·
                refine ⟨5841242731590127430794867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31153294568480679630905957 5841242731590127430794867)
                ·
                  refine ⟨8761864097385191146192301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5841242731590127430794867 8761864097385191146192301)
                  ·
                    refine ⟨3285699036519446679822113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8761864097385191146192301 3285699036519446679822113)
                    ·
                      refine ⟨2464274277389585009866585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285699036519446679822113 2464274277389585009866585)
                      ·
                        rfl

theorem cell23_4799157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_4799157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799157 prefixEnd_4799157 := by exact prefixLift 4799157
  have htrace : WordTrace (prefixWord ++ tailWord_4799157) baseStart_4799157 baseEnd_4799157 := by
    simpa [prefixWord, tailWord_4799157, baseEnd_4799157] using wordTrace_append hprefix tailTrace_4799157
  have hstable : (prefixWord ++ tailWord_4799157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799157).length < 2 ^ (prefixWord ++ tailWord_4799157).sum := by decide
  have hdescent : baseEnd_4799157 < baseStart_4799157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799204 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 2, 2, 2]
def baseStart_4799204 : Nat := 118140960795 + 4799204 * 2 ^ 59
def prefixEnd_4799204 : Nat := 4983230072969 + 3 ^ 40 * 4799204 * 2
def baseEnd_4799204 : Nat := 2464298410980346325978869

theorem tailTrace_4799204 : CollatzResearch.WordTrace tailWord_4799204 prefixEnd_4799204 2464298410980346325978869 := by
  unfold tailWord_4799204
  simp only [CollatzResearch.WordTrace]
  refine ⟨87520675052655510816766333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116694233403540681089021777 87520675052655510816766333)
  ·
    refine ⟨32820253144745816556287375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87520675052655510816766333 32820253144745816556287375)
    ·
      refine ⟨49230379717118724834431063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32820253144745816556287375 49230379717118724834431063)
      ·
        refine ⟨73845569575678087251646595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49230379717118724834431063 73845569575678087251646595)
        ·
          refine ⟨110768354363517130877469893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73845569575678087251646595 110768354363517130877469893)
          ·
            refine ⟨20769066443159462039525605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110768354363517130877469893 20769066443159462039525605)
            ·
              refine ⟨3894199958092399132411051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20769066443159462039525605 3894199958092399132411051)
              ·
                refine ⟨5841299937138598698616577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3894199958092399132411051 5841299937138598698616577)
                ·
                  refine ⟨4380974952853949023962433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5841299937138598698616577 4380974952853949023962433)
                  ·
                    refine ⟨3285731214640461767971825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4380974952853949023962433 3285731214640461767971825)
                    ·
                      refine ⟨2464298410980346325978869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285731214640461767971825 2464298410980346325978869)
                      ·
                        rfl

theorem cell23_4799204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_4799204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799204 prefixEnd_4799204 := by exact prefixLift 4799204
  have htrace : WordTrace (prefixWord ++ tailWord_4799204) baseStart_4799204 baseEnd_4799204 := by
    simpa [prefixWord, tailWord_4799204, baseEnd_4799204] using wordTrace_append hprefix tailTrace_4799204
  have hstable : (prefixWord ++ tailWord_4799204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799204).length < 2 ^ (prefixWord ++ tailWord_4799204).sum := by decide
  have hdescent : baseEnd_4799204 < baseStart_4799204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799216 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_4799216 : Nat := 118140960795 + 4799216 * 2 ^ 59
def prefixEnd_4799216 : Nat := 4983230072969 + 3 ^ 40 * 4799216 * 2
def baseEnd_4799216 : Nat := 2464304572748200279028813

theorem tailTrace_4799216 : CollatzResearch.WordTrace tailWord_4799216 prefixEnd_4799216 2464304572748200279028813 := by
  unfold tailWord_4799216
  simp only [CollatzResearch.WordTrace]
  refine ⟨87520893890633773841484751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116694525187511698455313001 87520893890633773841484751)
  ·
    refine ⟨131281340835950660762227127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87520893890633773841484751 131281340835950660762227127)
    ·
      refine ⟨196922011253925991143340691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131281340835950660762227127 196922011253925991143340691)
      ·
        refine ⟨295383016880888986715011037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196922011253925991143340691 295383016880888986715011037)
        ·
          refine ⟨110768631330333370018129139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295383016880888986715011037 110768631330333370018129139)
          ·
            refine ⟨166152946995500055027193709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110768631330333370018129139 166152946995500055027193709)
            ·
              refine ⟨62307355123312520635197641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166152946995500055027193709 62307355123312520635197641)
              ·
                refine ⟨46730516342484390476398231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62307355123312520635197641 46730516342484390476398231)
                ·
                  refine ⟨70095774513726585714597347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46730516342484390476398231 70095774513726585714597347)
                  ·
                    refine ⟨105143661770589878571896021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70095774513726585714597347 105143661770589878571896021)
                    ·
                      refine ⟨2464304572748200279028813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105143661770589878571896021 2464304572748200279028813)
                      ·
                        rfl

theorem cell23_4799216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_4799216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799216 prefixEnd_4799216 := by exact prefixLift 4799216
  have htrace : WordTrace (prefixWord ++ tailWord_4799216) baseStart_4799216 baseEnd_4799216 := by
    simpa [prefixWord, tailWord_4799216, baseEnd_4799216] using wordTrace_append hprefix tailTrace_4799216
  have hstable : (prefixWord ++ tailWord_4799216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799216).length < 2 ^ (prefixWord ++ tailWord_4799216).sum := by decide
  have hdescent : baseEnd_4799216 < baseStart_4799216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799221 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4799221 : Nat := 118140960795 + 4799221 * 2 ^ 59
def prefixEnd_4799221 : Nat := 4983230072969 + 3 ^ 40 * 4799221 * 2
def baseEnd_4799221 : Nat := 2464307140151472759466291

theorem tailTrace_4799221 : CollatzResearch.WordTrace tailWord_4799221 prefixEnd_4799221 2464307140151472759466291 := by
  unfold tailWord_4799221
  simp only [CollatzResearch.WordTrace]
  refine ⟨175041970146249433536901517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116694646764166289024601011 175041970146249433536901517)
  ·
    refine ⟨65640738804843537576338069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175041970146249433536901517 65640738804843537576338069)
    ·
      refine ⟨3076909631477040823890847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65640738804843537576338069 3076909631477040823890847)
      ·
        refine ⟨4615364447215561235836271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076909631477040823890847 4615364447215561235836271)
        ·
          refine ⟨6923046670823341853754407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4615364447215561235836271 6923046670823341853754407)
          ·
            refine ⟨10384570006235012780631611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6923046670823341853754407 10384570006235012780631611)
            ·
              refine ⟨15576855009352519170947417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10384570006235012780631611 15576855009352519170947417)
              ·
                refine ⟨11682641257014389378210563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15576855009352519170947417 11682641257014389378210563)
                ·
                  refine ⟨17523961885521584067315845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11682641257014389378210563 17523961885521584067315845)
                  ·
                    refine ⟨3285742853535297012621721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17523961885521584067315845 3285742853535297012621721)
                    ·
                      refine ⟨2464307140151472759466291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285742853535297012621721 2464307140151472759466291)
                      ·
                        rfl

theorem cell23_4799221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4799221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799221 prefixEnd_4799221 := by exact prefixLift 4799221
  have htrace : WordTrace (prefixWord ++ tailWord_4799221) baseStart_4799221 baseEnd_4799221 := by
    simpa [prefixWord, tailWord_4799221, baseEnd_4799221] using wordTrace_append hprefix tailTrace_4799221
  have hstable : (prefixWord ++ tailWord_4799221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799221).length < 2 ^ (prefixWord ++ tailWord_4799221).sum := by decide
  have hdescent : baseEnd_4799221 < baseStart_4799221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799260 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_4799260 : Nat := 118140960795 + 4799260 * 2 ^ 59
def prefixEnd_4799260 : Nat := 4983230072969 + 3 ^ 40 * 4799260 * 2
def baseEnd_4799260 : Nat := 2464327165896998106878611

theorem tailTrace_4799260 : CollatzResearch.WordTrace tailWord_4799260 prefixEnd_4799260 2464327165896998106878611 := by
  unfold tailWord_4799260
  simp only [CollatzResearch.WordTrace]
  refine ⟨87521696296554071598785617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116695595062072095465047489 87521696296554071598785617)
  ·
    refine ⟨65641272222415553699089213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87521696296554071598785617 65641272222415553699089213)
    ·
      refine ⟨24615477083405832637158455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65641272222415553699089213 24615477083405832637158455)
      ·
        refine ⟨36923215625108748955737683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24615477083405832637158455 36923215625108748955737683)
        ·
          refine ⟨55384823437663123433606525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36923215625108748955737683 55384823437663123433606525)
          ·
            refine ⟨20769308789123671287602447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55384823437663123433606525 20769308789123671287602447)
            ·
              refine ⟨31153963183685506931403671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20769308789123671287602447 31153963183685506931403671)
              ·
                refine ⟨46730944775528260397105507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31153963183685506931403671 46730944775528260397105507)
                ·
                  refine ⟨70096417163292390595658261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46730944775528260397105507 70096417163292390595658261)
                  ·
                    refine ⟨3285769554529330809171481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70096417163292390595658261 3285769554529330809171481)
                    ·
                      refine ⟨2464327165896998106878611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285769554529330809171481 2464327165896998106878611)
                      ·
                        rfl

theorem cell23_4799260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_4799260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799260 prefixEnd_4799260 := by exact prefixLift 4799260
  have htrace : WordTrace (prefixWord ++ tailWord_4799260) baseStart_4799260 baseEnd_4799260 := by
    simpa [prefixWord, tailWord_4799260, baseEnd_4799260] using wordTrace_append hprefix tailTrace_4799260
  have hstable : (prefixWord ++ tailWord_4799260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799260).length < 2 ^ (prefixWord ++ tailWord_4799260).sum := by decide
  have hdescent : baseEnd_4799260 < baseStart_4799260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799274 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 2, 5]
def baseStart_4799274 : Nat := 118140960795 + 4799274 * 2 ^ 59
def prefixEnd_4799274 : Nat := 4983230072969 + 3 ^ 40 * 4799274 * 2
def baseEnd_4799274 : Nat := 821444784875387017367849

theorem tailTrace_4799274 : CollatzResearch.WordTrace tailWord_4799274 prefixEnd_4799274 821444784875387017367849 := by
  unfold tailWord_4799274
  simp only [CollatzResearch.WordTrace]
  refine ⟨43760975803764355897145219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116695935476704949059053917 43760975803764355897145219)
  ·
    refine ⟨65641463705646533845717829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43760975803764355897145219 65641463705646533845717829)
    ·
      refine ⟨12307774444808725096072093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65641463705646533845717829 12307774444808725096072093)
      ·
        refine ⟨4615415416803271911027035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12307774444808725096072093 4615415416803271911027035)
        ·
          refine ⟨6923123125204907866540553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4615415416803271911027035 6923123125204907866540553)
          ·
            refine ⟨5192342343903680899905415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6923123125204907866540553 5192342343903680899905415)
            ·
              refine ⟨7788513515855521349858123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5192342343903680899905415 7788513515855521349858123)
              ·
                refine ⟨11682770273783282024787185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7788513515855521349858123 11682770273783282024787185)
                ·
                  refine ⟨8762077705337461518590389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11682770273783282024787185 8762077705337461518590389)
                  ·
                    refine ⟨821444784875387017367849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8762077705337461518590389 821444784875387017367849)
                    ·
                      rfl

theorem cell23_4799274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_4799274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799274 prefixEnd_4799274 := by exact prefixLift 4799274
  have htrace : WordTrace (prefixWord ++ tailWord_4799274) baseStart_4799274 baseEnd_4799274 := by
    simpa [prefixWord, tailWord_4799274, baseEnd_4799274] using wordTrace_append hprefix tailTrace_4799274
  have hstable : (prefixWord ++ tailWord_4799274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799274).length < 2 ^ (prefixWord ++ tailWord_4799274).sum := by decide
  have hdescent : baseEnd_4799274 < baseStart_4799274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799287 : List Nat := [1, 1, 3, 1, 2, 1, 6, 3, 1, 4]
def baseStart_4799287 : Nat := 118140960795 + 4799287 * 2 ^ 59
def prefixEnd_4799287 : Nat := 4983230072969 + 3 ^ 40 * 4799287 * 2
def baseEnd_4799287 : Nat := 821447009958223167080329

theorem tailTrace_4799287 : CollatzResearch.WordTrace tailWord_4799287 prefixEnd_4799287 821447009958223167080329 := by
  unfold tailWord_4799287
  simp only [CollatzResearch.WordTrace]
  refine ⟨175044377364010326808804115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116696251576006884539202743 175044377364010326808804115)
  ·
    refine ⟨262566566046015490213206173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175044377364010326808804115 262566566046015490213206173)
    ·
      refine ⟨98462462267255808829952315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262566566046015490213206173 98462462267255808829952315)
      ·
        refine ⟨147693693400883713244928473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98462462267255808829952315 147693693400883713244928473)
        ·
          refine ⟨110770270050662784933696355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147693693400883713244928473 110770270050662784933696355)
          ·
            refine ⟨166155405075994177400544533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110770270050662784933696355 166155405075994177400544533)
            ·
              refine ⟨7788534612937227065650525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166155405075994177400544533 7788534612937227065650525)
              ·
                refine ⟨2920700479851460149618947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7788534612937227065650525 2920700479851460149618947)
                ·
                  refine ⟨4381050719777190224428421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920700479851460149618947 4381050719777190224428421)
                  ·
                    refine ⟨821447009958223167080329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4381050719777190224428421 821447009958223167080329)
                    ·
                      rfl

theorem cell23_4799287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_4799287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799287 prefixEnd_4799287 := by exact prefixLift 4799287
  have htrace : WordTrace (prefixWord ++ tailWord_4799287) baseStart_4799287 baseEnd_4799287 := by
    simpa [prefixWord, tailWord_4799287, baseEnd_4799287] using wordTrace_append hprefix tailTrace_4799287
  have hstable : (prefixWord ++ tailWord_4799287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799287).length < 2 ^ (prefixWord ++ tailWord_4799287).sum := by decide
  have hdescent : baseEnd_4799287 < baseStart_4799287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799343 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 1, 6]
def baseStart_4799343 : Nat := 118140960795 + 4799343 * 2 ^ 59
def prefixEnd_4799343 : Nat := 4983230072969 + 3 ^ 40 * 4799343 * 2
def baseEnd_4799343 : Nat := 821456594930440427380243

theorem tailTrace_4799343 : CollatzResearch.WordTrace tailWord_4799343 prefixEnd_4799343 821456594930440427380243 := by
  unfold tailWord_4799343
  simp only [CollatzResearch.WordTrace]
  refine ⟨175046419851807448372842683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116697613234538298915228455 175046419851807448372842683)
  ·
    refine ⟨262569629777711172559264025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175046419851807448372842683 262569629777711172559264025)
    ·
      refine ⟨196927222333283379419448019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262569629777711172559264025 196927222333283379419448019)
      ·
        refine ⟨295390833499925069129172029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196927222333283379419448019 295390833499925069129172029)
        ·
          refine ⟨110771562562471900923439511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295390833499925069129172029 110771562562471900923439511)
          ·
            refine ⟨166157343843707851385159267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110771562562471900923439511 166157343843707851385159267)
            ·
              refine ⟨249236015765561777077738901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166157343843707851385159267 249236015765561777077738901)
              ·
                refine ⟨11682938239010708300519011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 249236015765561777077738901 11682938239010708300519011)
                ·
                  refine ⟨17524407358516062450778517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11682938239010708300519011 17524407358516062450778517)
                  ·
                    refine ⟨821456594930440427380243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17524407358516062450778517 821456594930440427380243)
                    ·
                      rfl

theorem cell23_4799343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_4799343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799343 prefixEnd_4799343 := by exact prefixLift 4799343
  have htrace : WordTrace (prefixWord ++ tailWord_4799343) baseStart_4799343 baseEnd_4799343 := by
    simpa [prefixWord, tailWord_4799343, baseEnd_4799343] using wordTrace_append hprefix tailTrace_4799343
  have hstable : (prefixWord ++ tailWord_4799343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799343).length < 2 ^ (prefixWord ++ tailWord_4799343).sum := by decide
  have hdescent : baseEnd_4799343 < baseStart_4799343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799344 : List Nat := [2, 1, 1, 1, 4, 1, 5, 3, 1, 1, 3]
def baseStart_4799344 : Nat := 118140960795 + 4799344 * 2 ^ 59
def prefixEnd_4799344 : Nat := 4983230072969 + 3 ^ 40 * 4799344 * 2
def baseEnd_4799344 : Nat := 2464370298271975778228225

theorem tailTrace_4799344 : CollatzResearch.WordTrace tailWord_4799344 prefixEnd_4799344 2464370298271975778228225 := by
  unfold tailWord_4799344
  simp only [CollatzResearch.WordTrace]
  refine ⟨87523228162401912771814543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116697637549869217029086057 87523228162401912771814543)
  ·
    refine ⟨131284842243602869157721815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87523228162401912771814543 131284842243602869157721815)
    ·
      refine ⟨196927263365404303736582723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131284842243602869157721815 196927263365404303736582723)
      ·
        refine ⟨295390895048106455604874085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196927263365404303736582723 295390895048106455604874085)
        ·
          refine ⟨55385792821519960425913891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 295390895048106455604874085 55385792821519960425913891)
          ·
            refine ⟨83078689232279940638870837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55385792821519960425913891 83078689232279940638870837)
            ·
              refine ⟨7788627115526244434894141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83078689232279940638870837 7788627115526244434894141)
              ·
                refine ⟨2920735168322341663085303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7788627115526244434894141 2920735168322341663085303)
                ·
                  refine ⟨4381102752483512494627955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920735168322341663085303 4381102752483512494627955)
                  ·
                    refine ⟨6571654128725268741941933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4381102752483512494627955 6571654128725268741941933)
                    ·
                      refine ⟨2464370298271975778228225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6571654128725268741941933 2464370298271975778228225)
                      ·
                        rfl

theorem cell23_4799344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 1, 1, 3].length) (baseStart_4799344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799344 prefixEnd_4799344 := by exact prefixLift 4799344
  have htrace : WordTrace (prefixWord ++ tailWord_4799344) baseStart_4799344 baseEnd_4799344 := by
    simpa [prefixWord, tailWord_4799344, baseEnd_4799344] using wordTrace_append hprefix tailTrace_4799344
  have hstable : (prefixWord ++ tailWord_4799344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799344).length < 2 ^ (prefixWord ++ tailWord_4799344).sum := by decide
  have hdescent : baseEnd_4799344 < baseStart_4799344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799363 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 6]
def baseStart_4799363 : Nat := 118140960795 + 4799363 * 2 ^ 59
def prefixEnd_4799363 : Nat := 4983230072969 + 3 ^ 40 * 4799363 * 2
def baseEnd_4799363 : Nat := 2464380054404411203890637

theorem tailTrace_4799363 : CollatzResearch.WordTrace tailWord_4799363 prefixEnd_4799363 2464380054404411203890637 := by
  unfold tailWord_4799363
  simp only [CollatzResearch.WordTrace]
  refine ⟨175047149311734991788570743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116698099541156661192380495 175047149311734991788570743)
  ·
    refine ⟨262570723967602487682856115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175047149311734991788570743 262570723967602487682856115)
    ·
      refine ⟨393856085951403731524284173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262570723967602487682856115 393856085951403731524284173)
      ·
        refine ⟨147696032231776399321606565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393856085951403731524284173 147696032231776399321606565)
        ·
          refine ⟨27693006043458074872801231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147696032231776399321606565 27693006043458074872801231)
          ·
            refine ⟨41539509065187112309201847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27693006043458074872801231 41539509065187112309201847)
            ·
              refine ⟨62309263597780668463802771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41539509065187112309201847 62309263597780668463802771)
              ·
                refine ⟨93463895396671002695704157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62309263597780668463802771 93463895396671002695704157)
                ·
                  refine ⟨35048960773751626010889059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93463895396671002695704157 35048960773751626010889059)
                  ·
                    refine ⟨52573441160627439016333589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35048960773751626010889059 52573441160627439016333589)
                    ·
                      refine ⟨2464380054404411203890637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52573441160627439016333589 2464380054404411203890637)
                      ·
                        rfl

theorem cell23_4799363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_4799363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799363 prefixEnd_4799363 := by exact prefixLift 4799363
  have htrace : WordTrace (prefixWord ++ tailWord_4799363) baseStart_4799363 baseEnd_4799363 := by
    simpa [prefixWord, tailWord_4799363, baseEnd_4799363] using wordTrace_append hprefix tailTrace_4799363
  have hstable : (prefixWord ++ tailWord_4799363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799363).length < 2 ^ (prefixWord ++ tailWord_4799363).sum := by decide
  have hdescent : baseEnd_4799363 < baseStart_4799363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799380 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_4799380 : Nat := 118140960795 + 4799380 * 2 ^ 59
def prefixEnd_4799380 : Nat := 4983230072969 + 3 ^ 40 * 4799380 * 2
def baseEnd_4799380 : Nat := 2464388783575537637378059

theorem tailTrace_4799380 : CollatzResearch.WordTrace tailWord_4799380 prefixEnd_4799380 2464388783575537637378059 := by
  unfold tailWord_4799380
  simp only [CollatzResearch.WordTrace]
  refine ⟨87523884676336701845969797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116698512901782269127959729 87523884676336701845969797)
  ·
    refine ⟨16410728376813131596119337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87523884676336701845969797 16410728376813131596119337)
    ·
      refine ⟨12308046282609848697089503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16410728376813131596119337 12308046282609848697089503)
      ·
        refine ⟨18462069423914773045634255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12308046282609848697089503 18462069423914773045634255)
        ·
          refine ⟨27693104135872159568451383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18462069423914773045634255 27693104135872159568451383)
          ·
            refine ⟨41539656203808239352677075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27693104135872159568451383 41539656203808239352677075)
            ·
              refine ⟨62309484305712359029015613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41539656203808239352677075 62309484305712359029015613)
              ·
                refine ⟨23366056614642134635880855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62309484305712359029015613 23366056614642134635880855)
                ·
                  refine ⟨35049084921963201953821283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23366056614642134635880855 35049084921963201953821283)
                  ·
                    refine ⟨52573627382944802930731925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35049084921963201953821283 52573627382944802930731925)
                    ·
                      refine ⟨2464388783575537637378059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52573627382944802930731925 2464388783575537637378059)
                      ·
                        rfl

theorem cell23_4799380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_4799380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799380 prefixEnd_4799380 := by exact prefixLift 4799380
  have htrace : WordTrace (prefixWord ++ tailWord_4799380) baseStart_4799380 baseEnd_4799380 := by
    simpa [prefixWord, tailWord_4799380, baseEnd_4799380] using wordTrace_append hprefix tailTrace_4799380
  have hstable : (prefixWord ++ tailWord_4799380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799380).length < 2 ^ (prefixWord ++ tailWord_4799380).sum := by decide
  have hdescent : baseEnd_4799380 < baseStart_4799380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799444 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_4799444 : Nat := 118140960795 + 4799444 * 2 ^ 59
def prefixEnd_4799444 : Nat := 4983230072969 + 3 ^ 40 * 4799444 * 2
def baseEnd_4799444 : Nat := 2464421646337425386977765

theorem tailTrace_4799444 : CollatzResearch.WordTrace tailWord_4799444 prefixEnd_4799444 2464421646337425386977765 := by
  unfold tailWord_4799444
  simp only [CollatzResearch.WordTrace]
  refine ⟨87525051812220771311134693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116700069082961028414846257 87525051812220771311134693)
  ·
    refine ⟨16410947214791394620837755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87525051812220771311134693 16410947214791394620837755)
    ·
      refine ⟨24616420822187091931256633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16410947214791394620837755 24616420822187091931256633)
      ·
        refine ⟨18462315616640318948442475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24616420822187091931256633 18462315616640318948442475)
        ·
          refine ⟨27693473424960478422663713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18462315616640318948442475 27693473424960478422663713)
          ·
            refine ⟨20770105068720358816997785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27693473424960478422663713 20770105068720358816997785)
            ·
              refine ⟨15577578801540269112748339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20770105068720358816997785 15577578801540269112748339)
              ·
                refine ⟨23366368202310403669122509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15577578801540269112748339 23366368202310403669122509)
                ·
                  refine ⟨8762388075866401375920941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23366368202310403669122509 8762388075866401375920941)
                  ·
                    refine ⟨3285895528449900515970353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8762388075866401375920941 3285895528449900515970353)
                    ·
                      refine ⟨2464421646337425386977765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285895528449900515970353 2464421646337425386977765)
                      ·
                        rfl

theorem cell23_4799444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_4799444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799444 prefixEnd_4799444 := by exact prefixLift 4799444
  have htrace : WordTrace (prefixWord ++ tailWord_4799444) baseStart_4799444 baseEnd_4799444 := by
    simpa [prefixWord, tailWord_4799444, baseEnd_4799444] using wordTrace_append hprefix tailTrace_4799444
  have hstable : (prefixWord ++ tailWord_4799444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799444).length < 2 ^ (prefixWord ++ tailWord_4799444).sum := by decide
  have hdescent : baseEnd_4799444 < baseStart_4799444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799460 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_4799460 : Nat := 118140960795 + 4799460 * 2 ^ 59
def prefixEnd_4799460 : Nat := 4983230072969 + 3 ^ 40 * 4799460 * 2
def baseEnd_4799460 : Nat := 2464429862027897324377691

theorem tailTrace_4799460 : CollatzResearch.WordTrace tailWord_4799460 prefixEnd_4799460 2464429862027897324377691 := by
  unfold tailWord_4799460
  simp only [CollatzResearch.WordTrace]
  refine ⟨87525343596191788677425917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116700458128255718236567889 87525343596191788677425917)
  ·
    refine ⟨32822003848571920754034719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87525343596191788677425917 32822003848571920754034719)
    ·
      refine ⟨49233005772857881131052079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32822003848571920754034719 49233005772857881131052079)
      ·
        refine ⟨73849508659286821696578119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49233005772857881131052079 73849508659286821696578119)
        ·
          refine ⟨110774262988930232544867179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73849508659286821696578119 110774262988930232544867179)
          ·
            refine ⟨166161394483395348817300769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110774262988930232544867179 166161394483395348817300769)
            ·
              refine ⟨124621045862546511612975577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166161394483395348817300769 124621045862546511612975577)
              ·
                refine ⟨93465784396909883709731683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124621045862546511612975577 93465784396909883709731683)
                ·
                  refine ⟨140198676595364825564597525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93465784396909883709731683 140198676595364825564597525)
                  ·
                    refine ⟨6571812965407726198340509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 140198676595364825564597525 6571812965407726198340509)
                    ·
                      refine ⟨2464429862027897324377691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6571812965407726198340509 2464429862027897324377691)
                      ·
                        rfl

theorem cell23_4799460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_4799460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799460 prefixEnd_4799460 := by exact prefixLift 4799460
  have htrace : WordTrace (prefixWord ++ tailWord_4799460) baseStart_4799460 baseEnd_4799460 := by
    simpa [prefixWord, tailWord_4799460, baseEnd_4799460] using wordTrace_append hprefix tailTrace_4799460
  have hstable : (prefixWord ++ tailWord_4799460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799460).length < 2 ^ (prefixWord ++ tailWord_4799460).sum := by decide
  have hdescent : baseEnd_4799460 < baseStart_4799460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799534 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_4799534 : Nat := 118140960795 + 4799534 * 2 ^ 59
def prefixEnd_4799534 : Nat := 4983230072969 + 3 ^ 40 * 4799534 * 2
def baseEnd_4799534 : Nat := 2464467859596330034852351

theorem tailTrace_4799534 : CollatzResearch.WordTrace tailWord_4799534 prefixEnd_4799534 2464467859596330034852351 := by
  unfold tailWord_4799534
  simp only [CollatzResearch.WordTrace]
  refine ⟨21881673274264435999130707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116702257462743658662030437 21881673274264435999130707)
  ·
    refine ⟨32822509911396653998696061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21881673274264435999130707 32822509911396653998696061)
    ·
      refine ⟨12308441216773745249511023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32822509911396653998696061 12308441216773745249511023)
      ·
        refine ⟨18462661825160617874266535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12308441216773745249511023 18462661825160617874266535)
        ·
          refine ⟨27693992737740926811399803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18462661825160617874266535 27693992737740926811399803)
          ·
            refine ⟨41540989106611390217099705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27693992737740926811399803 41540989106611390217099705)
            ·
              refine ⟨31155741829958542662824779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41540989106611390217099705 31155741829958542662824779)
              ·
                refine ⟨46733612744937813994237169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31155741829958542662824779 46733612744937813994237169)
                ·
                  refine ⟨35050209558703360495677877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46733612744937813994237169 35050209558703360495677877)
                  ·
                    refine ⟨3285957146128440046469801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35050209558703360495677877 3285957146128440046469801)
                    ·
                      refine ⟨2464467859596330034852351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3285957146128440046469801 2464467859596330034852351)
                      ·
                        rfl

theorem cell23_4799534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_4799534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799534 prefixEnd_4799534 := by exact prefixLift 4799534
  have htrace : WordTrace (prefixWord ++ tailWord_4799534) baseStart_4799534 baseEnd_4799534 := by
    simpa [prefixWord, tailWord_4799534, baseEnd_4799534] using wordTrace_append hprefix tailTrace_4799534
  have hstable : (prefixWord ++ tailWord_4799534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799534).length < 2 ^ (prefixWord ++ tailWord_4799534).sum := by decide
  have hdescent : baseEnd_4799534 < baseStart_4799534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799557 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 3, 4]
def baseStart_4799557 : Nat := 118140960795 + 4799557 * 2 ^ 59
def prefixEnd_4799557 : Nat := 4983230072969 + 3 ^ 40 * 4799557 * 2
def baseEnd_4799557 : Nat := 821493223217127814954915

theorem tailTrace_4799557 : CollatzResearch.WordTrace tailWord_4799557 prefixEnd_4799557 821493223217127814954915 := by
  unfold tailWord_4799557
  simp only [CollatzResearch.WordTrace]
  refine ⟨175054225073032162921132925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116702816715354775280755283 175054225073032162921132925)
  ·
    refine ⟨65645334402387061095424847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175054225073032162921132925 65645334402387061095424847)
    ·
      refine ⟨98468001603580591643137271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65645334402387061095424847 98468001603580591643137271)
      ·
        refine ⟨147702002405370887464705907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98468001603580591643137271 147702002405370887464705907)
        ·
          refine ⟨221553003608056331197058861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147702002405370887464705907 221553003608056331197058861)
          ·
            refine ⟨83082376353021124198897073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221553003608056331197058861 83082376353021124198897073)
            ·
              refine ⟨62311782264765843149172805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83082376353021124198897073 62311782264765843149172805)
              ·
                refine ⟨11683459174643595590469901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62311782264765843149172805 11683459174643595590469901)
                ·
                  refine ⟨4381297190491348346426213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11683459174643595590469901 4381297190491348346426213)
                  ·
                    refine ⟨821493223217127814954915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4381297190491348346426213 821493223217127814954915)
                    ·
                      rfl

theorem cell23_4799557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_4799557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799557 prefixEnd_4799557 := by exact prefixLift 4799557
  have htrace : WordTrace (prefixWord ++ tailWord_4799557) baseStart_4799557 baseEnd_4799557 := by
    simpa [prefixWord, tailWord_4799557, baseEnd_4799557] using wordTrace_append hprefix tailTrace_4799557
  have hstable : (prefixWord ++ tailWord_4799557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799557).length < 2 ^ (prefixWord ++ tailWord_4799557).sum := by decide
  have hdescent : baseEnd_4799557 < baseStart_4799557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799591 : List Nat := [1, 1, 5, 1, 1, 4, 1, 4, 1, 4]
def baseStart_4799591 : Nat := 118140960795 + 4799591 * 2 ^ 59
def prefixEnd_4799591 : Nat := 4983230072969 + 3 ^ 40 * 4799591 * 2
def baseEnd_4799591 : Nat := 821499042664545437279863

theorem tailTrace_4799591 : CollatzResearch.WordTrace tailWord_4799591 prefixEnd_4799591 821499042664545437279863 := by
  unfold tailWord_4799591
  simp only [CollatzResearch.WordTrace]
  refine ⟨175055465154908986727870627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116703643436605991151913751 175055465154908986727870627)
  ·
    refine ⟨262583197732363480091805941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175055465154908986727870627 262583197732363480091805941)
    ·
      refine ⟨24617174787409076258606807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 262583197732363480091805941 24617174787409076258606807)
      ·
        refine ⟨36925762181113614387910211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24617174787409076258606807 36925762181113614387910211)
        ·
          refine ⟨55388643271670421581865317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36925762181113614387910211 55388643271670421581865317)
          ·
            refine ⟨10385370613438204046599747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55388643271670421581865317 10385370613438204046599747)
            ·
              refine ⟨15578055920157306069899621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10385370613438204046599747 15578055920157306069899621)
              ·
                refine ⟨2920885485029494888106179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15578055920157306069899621 2920885485029494888106179)
                ·
                  refine ⟨4381328227544242332159269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920885485029494888106179 4381328227544242332159269)
                  ·
                    refine ⟨821499042664545437279863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4381328227544242332159269 821499042664545437279863)
                    ·
                      rfl

theorem cell23_4799591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_4799591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799591 prefixEnd_4799591 := by exact prefixLift 4799591
  have htrace : WordTrace (prefixWord ++ tailWord_4799591) baseStart_4799591 baseEnd_4799591 := by
    simpa [prefixWord, tailWord_4799591, baseEnd_4799591] using wordTrace_append hprefix tailTrace_4799591
  have hstable : (prefixWord ++ tailWord_4799591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799591).length < 2 ^ (prefixWord ++ tailWord_4799591).sum := by decide
  have hdescent : baseEnd_4799591 < baseStart_4799591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799637 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_4799637 : Nat := 118140960795 + 4799637 * 2 ^ 59
def prefixEnd_4799637 : Nat := 4983230072969 + 3 ^ 40 * 4799637 * 2
def baseEnd_4799637 : Nat := 2464520748103743131864377

theorem tailTrace_4799637 : CollatzResearch.WordTrace tailWord_4799637 prefixEnd_4799637 2464520748103743131864377 := by
  unfold tailWord_4799637
  simp only [CollatzResearch.WordTrace]
  refine ⟨175057142912742336584045165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116704761941828224389363443 175057142912742336584045165)
  ·
    refine ⟨65646428592278376219016937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175057142912742336584045165 65646428592278376219016937)
    ·
      refine ⟨49234821444208782164262703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65646428592278376219016937 49234821444208782164262703)
      ·
        refine ⟨73852232166313173246394055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49234821444208782164262703 73852232166313173246394055)
        ·
          refine ⟨110778348249469759869591083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73852232166313173246394055 110778348249469759869591083)
          ·
            refine ⟨166167522374204639804386625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110778348249469759869591083 166167522374204639804386625)
            ·
              refine ⟨124625641780653479853289969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166167522374204639804386625 124625641780653479853289969)
              ·
                refine ⟨93469231335490109889967477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124625641780653479853289969 93469231335490109889967477)
                ·
                  refine ⟨8762740437702197802184451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93469231335490109889967477 8762740437702197802184451)
                  ·
                    refine ⟨13144110656553296703276677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8762740437702197802184451 13144110656553296703276677)
                    ·
                      refine ⟨2464520748103743131864377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13144110656553296703276677 2464520748103743131864377)
                      ·
                        rfl

theorem cell23_4799637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_4799637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799637 prefixEnd_4799637 := by exact prefixLift 4799637
  have htrace : WordTrace (prefixWord ++ tailWord_4799637) baseStart_4799637 baseEnd_4799637 := by
    simpa [prefixWord, tailWord_4799637, baseEnd_4799637] using wordTrace_append hprefix tailTrace_4799637
  have hstable : (prefixWord ++ tailWord_4799637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799637).length < 2 ^ (prefixWord ++ tailWord_4799637).sum := by decide
  have hdescent : baseEnd_4799637 < baseStart_4799637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799671 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 3, 2, 2]
def baseStart_4799671 : Nat := 118140960795 + 4799671 * 2 ^ 59
def prefixEnd_4799671 : Nat := 4983230072969 + 3 ^ 40 * 4799671 * 2
def baseEnd_4799671 : Nat := 2464538206445995998839221

theorem tailTrace_4799671 : CollatzResearch.WordTrace tailWord_4799671 prefixEnd_4799671 2464538206445995998839221 := by
  unfold tailWord_4799671
  simp only [CollatzResearch.WordTrace]
  refine ⟨175058382994619160390782867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116705588663079440260521911 175058382994619160390782867)
  ·
    refine ⟨262587574491928740586174301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175058382994619160390782867 262587574491928740586174301)
    ·
      refine ⟨98470340434473277719815363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262587574491928740586174301 98470340434473277719815363)
      ·
        refine ⟨147705510651709916579723045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98470340434473277719815363 147705510651709916579723045)
        ·
          refine ⟨27694783247195609358698071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147705510651709916579723045 27694783247195609358698071)
          ·
            refine ⟨41542174870793414038047107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27694783247195609358698071 41542174870793414038047107)
            ·
              refine ⟨62313262306190121057070661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41542174870793414038047107 62313262306190121057070661)
              ·
                refine ⟨11683736682410647698200749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62313262306190121057070661 11683736682410647698200749)
                ·
                  refine ⟨4381401255903992886825281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11683736682410647698200749 4381401255903992886825281)
                  ·
                    refine ⟨3286050941927994665118961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4381401255903992886825281 3286050941927994665118961)
                    ·
                      refine ⟨2464538206445995998839221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286050941927994665118961 2464538206445995998839221)
                      ·
                        rfl

theorem cell23_4799671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3, 2, 2].length) (baseStart_4799671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799671 prefixEnd_4799671 := by exact prefixLift 4799671
  have htrace : WordTrace (prefixWord ++ tailWord_4799671) baseStart_4799671 baseEnd_4799671 := by
    simpa [prefixWord, tailWord_4799671, baseEnd_4799671] using wordTrace_append hprefix tailTrace_4799671
  have hstable : (prefixWord ++ tailWord_4799671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799671).length < 2 ^ (prefixWord ++ tailWord_4799671).sum := by decide
  have hdescent : baseEnd_4799671 < baseStart_4799671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799681 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4799681 : Nat := 118140960795 + 4799681 * 2 ^ 59
def prefixEnd_4799681 : Nat := 4983230072969 + 3 ^ 40 * 4799681 * 2
def baseEnd_4799681 : Nat := 821514447084180319904725

theorem tailTrace_4799681 : CollatzResearch.WordTrace tailWord_4799681 prefixEnd_4799681 821514447084180319904725 := by
  unfold tailWord_4799681
  simp only [CollatzResearch.WordTrace]
  refine ⟨175058747724582932098646897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116705831816388621399097931 175058747724582932098646897)
  ·
    refine ⟨131294060793437199073985173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175058747724582932098646897 131294060793437199073985173)
    ·
      refine ⟨6154409099692368706593055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131294060793437199073985173 6154409099692368706593055)
      ·
        refine ⟨9231613649538553059889583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6154409099692368706593055 9231613649538553059889583)
        ·
          refine ⟨13847420474307829589834375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9231613649538553059889583 13847420474307829589834375)
          ·
            refine ⟨20771130711461744384751563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13847420474307829589834375 20771130711461744384751563)
            ·
              refine ⟨31156696067192616577127345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20771130711461744384751563 31156696067192616577127345)
              ·
                refine ⟨23367522050394462432845509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31156696067192616577127345 23367522050394462432845509)
                ·
                  refine ⟨4381410384448961706158533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23367522050394462432845509 4381410384448961706158533)
                  ·
                    refine ⟨821514447084180319904725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4381410384448961706158533 821514447084180319904725)
                    ·
                      rfl

theorem cell23_4799681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4799681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799681 prefixEnd_4799681 := by exact prefixLift 4799681
  have htrace : WordTrace (prefixWord ++ tailWord_4799681) baseStart_4799681 baseEnd_4799681 := by
    simpa [prefixWord, tailWord_4799681, baseEnd_4799681] using wordTrace_append hprefix tailTrace_4799681
  have hstable : (prefixWord ++ tailWord_4799681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799681).length < 2 ^ (prefixWord ++ tailWord_4799681).sum := by decide
  have hdescent : baseEnd_4799681 < baseStart_4799681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799694 : List Nat := [4, 1, 1, 1, 5, 2, 9]
def baseStart_4799694 : Nat := 118140960795 + 4799694 * 2 ^ 59
def prefixEnd_4799694 : Nat := 4983230072969 + 3 ^ 40 * 4799694 * 2
def baseEnd_4799694 : Nat := 30426543413593202578415

theorem tailTrace_4799694 : CollatzResearch.WordTrace tailWord_4799694 prefixEnd_4799694 30426543413593202578415 := by
  unfold tailWord_4799694
  simp only [CollatzResearch.WordTrace]
  refine ⟨21882402734191979414858767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116706147915690556879246757 21882402734191979414858767)
  ·
    refine ⟨32823604101287969122288151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21882402734191979414858767 32823604101287969122288151)
    ·
      refine ⟨49235406151931953683432227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32823604101287969122288151 49235406151931953683432227)
      ·
        refine ⟨73853109227897930525148341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49235406151931953683432227 73853109227897930525148341)
        ·
          refine ⟨6923728990115430986732657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73853109227897930525148341 6923728990115430986732657)
          ·
            refine ⟨5192796742586573240049493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6923728990115430986732657 5192796742586573240049493)
            ·
              refine ⟨30426543413593202578415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5192796742586573240049493 30426543413593202578415)
              ·
                rfl

theorem cell23_4799694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 9].length) (baseStart_4799694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799694 prefixEnd_4799694 := by exact prefixLift 4799694
  have htrace : WordTrace (prefixWord ++ tailWord_4799694) baseStart_4799694 baseEnd_4799694 := by
    simpa [prefixWord, tailWord_4799694, baseEnd_4799694] using wordTrace_append hprefix tailTrace_4799694
  have hstable : (prefixWord ++ tailWord_4799694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799694).length < 2 ^ (prefixWord ++ tailWord_4799694).sum := by decide
  have hdescent : baseEnd_4799694 < baseStart_4799694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799731 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 3, 3, 2]
def baseStart_4799731 : Nat := 118140960795 + 4799731 * 2 ^ 59
def prefixEnd_4799731 : Nat := 4983230072969 + 3 ^ 40 * 4799731 * 2
def baseEnd_4799731 : Nat := 2464569015285265764088945

theorem tailTrace_4799731 : CollatzResearch.WordTrace tailWord_4799731 prefixEnd_4799731 2464569015285265764088945 := by
  unfold tailWord_4799731
  simp only [CollatzResearch.WordTrace]
  refine ⟨175060571374401790637967047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116707047582934527091978031 175060571374401790637967047)
  ·
    refine ⟨262590857061602685956950571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175060571374401790637967047 262590857061602685956950571)
    ·
      refine ⟨393886285592404028935425857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262590857061602685956950571 393886285592404028935425857)
      ·
        refine ⟨295414714194303021701569393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393886285592404028935425857 295414714194303021701569393)
        ·
          refine ⟨221561035645727266276177045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295414714194303021701569393 221561035645727266276177045)
          ·
            refine ⟨10385673545893465606695799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 221561035645727266276177045 10385673545893465606695799)
            ·
              refine ⟨15578510318840198410043699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10385673545893465606695799 15578510318840198410043699)
              ·
                refine ⟨23367765478260297615065549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15578510318840198410043699 23367765478260297615065549)
                ·
                  refine ⟨8762912054347611605649581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23367765478260297615065549 8762912054347611605649581)
                  ·
                    refine ⟨3286092020380354352118593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8762912054347611605649581 3286092020380354352118593)
                    ·
                      refine ⟨2464569015285265764088945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286092020380354352118593 2464569015285265764088945)
                      ·
                        rfl

theorem cell23_4799731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 3, 2].length) (baseStart_4799731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799731 prefixEnd_4799731 := by exact prefixLift 4799731
  have htrace : WordTrace (prefixWord ++ tailWord_4799731) baseStart_4799731 baseEnd_4799731 := by
    simpa [prefixWord, tailWord_4799731, baseEnd_4799731] using wordTrace_append hprefix tailTrace_4799731
  have hstable : (prefixWord ++ tailWord_4799731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799731).length < 2 ^ (prefixWord ++ tailWord_4799731).sum := by decide
  have hdescent : baseEnd_4799731 < baseStart_4799731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799784 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 9]
def baseStart_4799784 : Nat := 118140960795 + 4799784 * 2 ^ 59
def prefixEnd_4799784 : Nat := 4983230072969 + 3 ^ 40 * 4799784 * 2
def baseEnd_4799784 : Nat := 273844025528883784080689

theorem tailTrace_4799784 : CollatzResearch.WordTrace tailWord_4799784 prefixEnd_4799784 273844025528883784080689 := by
  unfold tailWord_4799784
  simp only [CollatzResearch.WordTrace]
  refine ⟨87531252221604890344823203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116708336295473187126430937 87531252221604890344823203)
  ·
    refine ⟨131296878332407335517234805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87531252221604890344823203 131296878332407335517234805)
    ·
      refine ⟨12309082343663187704740763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131296878332407335517234805 12309082343663187704740763)
      ·
        refine ⟨18463623515494781557111145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12309082343663187704740763 18463623515494781557111145)
        ·
          refine ⟨13847717636621086167833359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18463623515494781557111145 13847717636621086167833359)
          ·
            refine ⟨20771576454931629251750039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13847717636621086167833359 20771576454931629251750039)
            ·
              refine ⟨31157364682397443877625059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20771576454931629251750039 31157364682397443877625059)
              ·
                refine ⟨46736047023596165816437589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31157364682397443877625059 46736047023596165816437589)
                ·
                  refine ⟨273844025528883784080689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46736047023596165816437589 273844025528883784080689)
                  ·
                    rfl

theorem cell23_4799784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 9].length) (baseStart_4799784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799784 prefixEnd_4799784 := by exact prefixLift 4799784
  have htrace : WordTrace (prefixWord ++ tailWord_4799784) baseStart_4799784 baseEnd_4799784 := by
    simpa [prefixWord, tailWord_4799784, baseEnd_4799784] using wordTrace_append hprefix tailTrace_4799784
  have hstable : (prefixWord ++ tailWord_4799784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799784).length < 2 ^ (prefixWord ++ tailWord_4799784).sum := by decide
  have hdescent : baseEnd_4799784 < baseStart_4799784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799812 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_4799812 : Nat := 118140960795 + 4799812 * 2 ^ 59
def prefixEnd_4799812 : Nat := 4983230072969 + 3 ^ 40 * 4799812 * 2
def baseEnd_4799812 : Nat := 2464610607218279947176073

theorem tailTrace_4799812 : CollatzResearch.WordTrace tailWord_4799812 prefixEnd_4799812 2464610607218279947176073 := by
  unfold tailWord_4799812
  simp only [CollatzResearch.WordTrace]
  refine ⟨87531762843554170735832845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116709017124738894314443793 87531762843554170735832845)
  ·
    refine ⟨32824411066332814025937317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87531762843554170735832845 32824411066332814025937317)
    ·
      refine ⟨6154577074937402629863247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32824411066332814025937317 6154577074937402629863247)
      ·
        refine ⟨9231865612406103944794871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6154577074937402629863247 9231865612406103944794871)
        ·
          refine ⟨13847798418609155917192307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9231865612406103944794871 13847798418609155917192307)
          ·
            refine ⟨20771697627913733875788461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13847798418609155917192307 20771697627913733875788461)
            ·
              refine ⟨7789386610467650203420673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20771697627913733875788461 7789386610467650203420673)
              ·
                refine ⟨5842039957850737652565505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7789386610467650203420673 5842039957850737652565505)
                ·
                  refine ⟨4381529968388053239424129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5842039957850737652565505 4381529968388053239424129)
                  ·
                    refine ⟨3286147476291039929568097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4381529968388053239424129 3286147476291039929568097)
                    ·
                      refine ⟨2464610607218279947176073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286147476291039929568097 2464610607218279947176073)
                      ·
                        rfl

theorem cell23_4799812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_4799812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799812 prefixEnd_4799812 := by exact prefixLift 4799812
  have htrace : WordTrace (prefixWord ++ tailWord_4799812) baseStart_4799812 baseEnd_4799812 := by
    simpa [prefixWord, tailWord_4799812, baseEnd_4799812] using wordTrace_append hprefix tailTrace_4799812
  have hstable : (prefixWord ++ tailWord_4799812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799812).length < 2 ^ (prefixWord ++ tailWord_4799812).sum := by decide
  have hdescent : baseEnd_4799812 < baseStart_4799812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799834 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_4799834 : Nat := 118140960795 + 4799834 * 2 ^ 59
def prefixEnd_4799834 : Nat := 4983230072969 + 3 ^ 40 * 4799834 * 2
def baseEnd_4799834 : Nat := 2464621903792678861100971

theorem tailTrace_4799834 : CollatzResearch.WordTrace tailWord_4799834 prefixEnd_4799834 2464621903792678861100971 := by
  unfold tailWord_4799834
  simp only [CollatzResearch.WordTrace]
  refine ⟨43766082023257159807241639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116709552062019092819311037 43766082023257159807241639)
  ·
    refine ⟨65649123034885739710862459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43766082023257159807241639 65649123034885739710862459)
    ·
      refine ⟨98473684552328609566293689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65649123034885739710862459 98473684552328609566293689)
      ·
        refine ⟨73855263414246457174720267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98473684552328609566293689 73855263414246457174720267)
        ·
          refine ⟨110782895121369685762080401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73855263414246457174720267 110782895121369685762080401)
          ·
            refine ⟨83087171341027264321560301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110782895121369685762080401 83087171341027264321560301)
            ·
              refine ⟨31157689252885224120585113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83087171341027264321560301 31157689252885224120585113)
              ·
                refine ⟨23368266939663918090438835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31157689252885224120585113 23368266939663918090438835)
                ·
                  refine ⟨35052400409495877135658253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23368266939663918090438835 35052400409495877135658253)
                  ·
                    refine ⟨13144650153560953925871845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35052400409495877135658253 13144650153560953925871845)
                    ·
                      refine ⟨2464621903792678861100971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13144650153560953925871845 2464621903792678861100971)
                      ·
                        rfl

theorem cell23_4799834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_4799834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799834 prefixEnd_4799834 := by exact prefixLift 4799834
  have htrace : WordTrace (prefixWord ++ tailWord_4799834) baseStart_4799834 baseEnd_4799834 := by
    simpa [prefixWord, tailWord_4799834, baseEnd_4799834] using wordTrace_append hprefix tailTrace_4799834
  have hstable : (prefixWord ++ tailWord_4799834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799834).length < 2 ^ (prefixWord ++ tailWord_4799834).sum := by decide
  have hdescent : baseEnd_4799834 < baseStart_4799834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799928 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 2, 3, 2]
def baseStart_4799928 : Nat := 118140960795 + 4799928 * 2 ^ 59
def prefixEnd_4799928 : Nat := 4983230072969 + 3 ^ 40 * 4799928 * 2
def baseEnd_4799928 : Nat := 2464670170974201493325539

theorem tailTrace_4799928 : CollatzResearch.WordTrace tailWord_4799928 prefixEnd_4799928 2464670170974201493325539 := by
  unfold tailWord_4799928
  simp only [CollatzResearch.WordTrace]
  refine ⟨87533878277344046641444219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116711837703125395521925625 87533878277344046641444219)
  ·
    refine ⟨131300817416016069962166329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87533878277344046641444219 131300817416016069962166329)
    ·
      refine ⟨98475613062012052471624747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131300817416016069962166329 98475613062012052471624747)
      ·
        refine ⟨147713419593018078707437121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98475613062012052471624747 147713419593018078707437121)
        ·
          refine ⟨110785064694763559030577841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147713419593018078707437121 110785064694763559030577841)
          ·
            refine ⟨83088798521072669272933381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110785064694763559030577841 83088798521072669272933381)
            ·
              refine ⟨15579149722701125488675009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83088798521072669272933381 15579149722701125488675009)
              ·
                refine ⟨11684362292025844116506257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15579149722701125488675009 11684362292025844116506257)
                ·
                  refine ⟨8763271719019383087379693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11684362292025844116506257 8763271719019383087379693)
                  ·
                    refine ⟨3286226894632268657767385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8763271719019383087379693 3286226894632268657767385)
                    ·
                      refine ⟨2464670170974201493325539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286226894632268657767385 2464670170974201493325539)
                      ·
                        rfl

theorem cell23_4799928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 3, 2].length) (baseStart_4799928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799928 prefixEnd_4799928 := by exact prefixLift 4799928
  have htrace : WordTrace (prefixWord ++ tailWord_4799928) baseStart_4799928 baseEnd_4799928 := by
    simpa [prefixWord, tailWord_4799928, baseEnd_4799928] using wordTrace_append hprefix tailTrace_4799928
  have hstable : (prefixWord ++ tailWord_4799928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799928).length < 2 ^ (prefixWord ++ tailWord_4799928).sum := by decide
  have hdescent : baseEnd_4799928 < baseStart_4799928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799929 : List Nat := [1, 2, 1, 4, 5, 1, 2, 2, 1, 4]
def baseStart_4799929 : Nat := 118140960795 + 4799929 * 2 ^ 59
def prefixEnd_4799929 : Nat := 4983230072969 + 3 ^ 40 * 4799929 * 2
def baseEnd_4799929 : Nat := 821556894818285329804345

theorem tailTrace_4799929 : CollatzResearch.WordTrace tailWord_4799929 prefixEnd_4799929 821556894818285329804345 := by
  unfold tailWord_4799929
  simp only [CollatzResearch.WordTrace]
  refine ⟨175067793027684470453674841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116711862018456313635783227 175067793027684470453674841)
  ·
    refine ⟨131300844770763352840256131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175067793027684470453674841 131300844770763352840256131)
    ·
      refine ⟨196951267156145029260384197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131300844770763352840256131 196951267156145029260384197)
      ·
        refine ⟨36928362591777192986322037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196951267156145029260384197 36928362591777192986322037)
        ·
          refine ⟨3462033992979111842467691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36928362591777192986322037 3462033992979111842467691)
          ·
            refine ⟨5193050989468667763701537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3462033992979111842467691 5193050989468667763701537)
            ·
              refine ⟨3894788242101500822776153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5193050989468667763701537 3894788242101500822776153)
              ·
                refine ⟨2921091181576125617082115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3894788242101500822776153 2921091181576125617082115)
                ·
                  refine ⟨4381636772364188425623173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921091181576125617082115 4381636772364188425623173)
                  ·
                    refine ⟨821556894818285329804345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4381636772364188425623173 821556894818285329804345)
                    ·
                      rfl

theorem cell23_4799929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 1, 4].length) (baseStart_4799929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799929 prefixEnd_4799929 := by exact prefixLift 4799929
  have htrace : WordTrace (prefixWord ++ tailWord_4799929) baseStart_4799929 baseEnd_4799929 := by
    simpa [prefixWord, tailWord_4799929, baseEnd_4799929] using wordTrace_append hprefix tailTrace_4799929
  have hstable : (prefixWord ++ tailWord_4799929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799929).length < 2 ^ (prefixWord ++ tailWord_4799929).sum := by decide
  have hdescent : baseEnd_4799929 < baseStart_4799929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799975 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_4799975 : Nat := 118140960795 + 4799975 * 2 ^ 59
def prefixEnd_4799975 : Nat := 4983230072969 + 3 ^ 40 * 4799975 * 2
def baseEnd_4799975 : Nat := 2464694304564962809437823

theorem tailTrace_4799975 : CollatzResearch.WordTrace tailWord_4799975 prefixEnd_4799975 2464694304564962809437823 := by
  unfold tailWord_4799975
  simp only [CollatzResearch.WordTrace]
  refine ⟨175069470785517820309849379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116712980523678546873232919 175069470785517820309849379)
  ·
    refine ⟨262604206178276730464774069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175069470785517820309849379 262604206178276730464774069)
    ·
      refine ⟨24619144329213443481072569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 262604206178276730464774069 24619144329213443481072569)
      ·
        refine ⟨18464358246910082610804427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24619144329213443481072569 18464358246910082610804427)
        ·
          refine ⟨27696537370365123916206641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18464358246910082610804427 27696537370365123916206641)
          ·
            refine ⟨20772403027773842937154981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27696537370365123916206641 20772403027773842937154981)
            ·
              refine ⟨3894825567707595550716559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20772403027773842937154981 3894825567707595550716559)
              ·
                refine ⟨5842238351561393326074839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3894825567707595550716559 5842238351561393326074839)
                ·
                  refine ⟨8763357527342089989112259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5842238351561393326074839 8763357527342089989112259)
                  ·
                    refine ⟨13145036291013134983668389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8763357527342089989112259 13145036291013134983668389)
                    ·
                      refine ⟨2464694304564962809437823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13145036291013134983668389 2464694304564962809437823)
                      ·
                        rfl

theorem cell23_4799975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_4799975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799975 prefixEnd_4799975 := by exact prefixLift 4799975
  have htrace : WordTrace (prefixWord ++ tailWord_4799975) baseStart_4799975 baseEnd_4799975 := by
    simpa [prefixWord, tailWord_4799975, baseEnd_4799975] using wordTrace_append hprefix tailTrace_4799975
  have hstable : (prefixWord ++ tailWord_4799975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799975).length < 2 ^ (prefixWord ++ tailWord_4799975).sum := by decide
  have hdescent : baseEnd_4799975 < baseStart_4799975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799985 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 2, 4]
def baseStart_4799985 : Nat := 118140960795 + 4799985 * 2 ^ 59
def prefixEnd_4799985 : Nat := 4983230072969 + 3 ^ 40 * 4799985 * 2
def baseEnd_4799985 : Nat := 821566479790502590104259

theorem tailTrace_4799985 : CollatzResearch.WordTrace tailWord_4799985 prefixEnd_4799985 821566479790502590104259 := by
  unfold tailWord_4799985
  simp only [CollatzResearch.WordTrace]
  refine ⟨175069835515481592017713409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116713223676987728011808939 175069835515481592017713409)
  ·
    refine ⟨131302376636611194013285057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175069835515481592017713409 131302376636611194013285057)
    ·
      refine ⟨98476782477458395509963793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131302376636611194013285057 98476782477458395509963793)
      ·
        refine ⟨73857586858093796632472845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98476782477458395509963793 73857586858093796632472845)
        ·
          refine ⟨27696595071785173737177317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73857586858093796632472845 27696595071785173737177317)
          ·
            refine ⟨5193111575959720075720747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27696595071785173737177317 5193111575959720075720747)
            ·
              refine ⟨7789667363939580113581121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5193111575959720075720747 7789667363939580113581121)
              ·
                refine ⟨5842250522954685085185841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7789667363939580113581121 5842250522954685085185841)
                ·
                  refine ⟨4381687892216013813889381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5842250522954685085185841 4381687892216013813889381)
                  ·
                    refine ⟨821566479790502590104259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4381687892216013813889381 821566479790502590104259)
                    ·
                      rfl

theorem cell23_4799985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_4799985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799985 prefixEnd_4799985 := by exact prefixLift 4799985
  have htrace : WordTrace (prefixWord ++ tailWord_4799985) baseStart_4799985 baseEnd_4799985 := by
    simpa [prefixWord, tailWord_4799985, baseEnd_4799985] using wordTrace_append hprefix tailTrace_4799985
  have hstable : (prefixWord ++ tailWord_4799985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799985).length < 2 ^ (prefixWord ++ tailWord_4799985).sum := by decide
  have hdescent : baseEnd_4799985 < baseStart_4799985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4799992 : List Nat := [2, 1, 2, 1, 1, 5, 2, 4, 1, 2, 2]
def baseStart_4799992 : Nat := 118140960795 + 4799992 * 2 ^ 59
def prefixEnd_4799992 : Nat := 4983230072969 + 3 ^ 40 * 4799992 * 2
def baseEnd_4799992 : Nat := 2464703033736089242925245

theorem tailTrace_4799992 : CollatzResearch.WordTrace tailWord_4799992 prefixEnd_4799992 2464703033736089242925245 := by
  unfold tailWord_4799992
  simp only [CollatzResearch.WordTrace]
  refine ⟨87535045413228116106609115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116713393884304154808812153 87535045413228116106609115)
  ·
    refine ⟨131302568119842174159913673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87535045413228116106609115 131302568119842174159913673)
    ·
      refine ⟨98476926089881630619935255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131302568119842174159913673 98476926089881630619935255)
      ·
        refine ⟨147715389134822445929902883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98476926089881630619935255 147715389134822445929902883)
        ·
          refine ⟨221573083702233668894854325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147715389134822445929902883 221573083702233668894854325)
          ·
            refine ⟨20772476597084406458892593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221573083702233668894854325 20772476597084406458892593)
            ·
              refine ⟨15579357447813304844169445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20772476597084406458892593 15579357447813304844169445)
              ·
                refine ⟨2921129521464994658281771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15579357447813304844169445 2921129521464994658281771)
                ·
                  refine ⟨4381694282197491987422657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921129521464994658281771 4381694282197491987422657)
                  ·
                    refine ⟨3286270711648118990566993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4381694282197491987422657 3286270711648118990566993)
                    ·
                      refine ⟨2464703033736089242925245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286270711648118990566993 2464703033736089242925245)
                      ·
                        rfl

theorem cell23_4799992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 1, 2, 2].length) (baseStart_4799992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4799992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4799992 prefixEnd_4799992 := by exact prefixLift 4799992
  have htrace : WordTrace (prefixWord ++ tailWord_4799992) baseStart_4799992 baseEnd_4799992 := by
    simpa [prefixWord, tailWord_4799992, baseEnd_4799992] using wordTrace_append hprefix tailTrace_4799992
  have hstable : (prefixWord ++ tailWord_4799992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4799992).length < 2 ^ (prefixWord ++ tailWord_4799992).sum := by decide
  have hdescent : baseEnd_4799992 < baseStart_4799992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4799992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800008 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_4800008 : Nat := 118140960795 + 4800008 * 2 ^ 59
def prefixEnd_4800008 : Nat := 4983230072969 + 3 ^ 40 * 4800008 * 2
def baseEnd_4800008 : Nat := 2464711249426561180325171

theorem tailTrace_4800008 : CollatzResearch.WordTrace tailWord_4800008 prefixEnd_4800008 2464711249426561180325171 := by
  unfold tailWord_4800008
  simp only [CollatzResearch.WordTrace]
  refine ⟨87535337197199133472900339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116713782929598844630533785 87535337197199133472900339)
  ·
    refine ⟨131303005795798700209350509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87535337197199133472900339 131303005795798700209350509)
    ·
      refine ⟨49238627173424512578506441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131303005795798700209350509 49238627173424512578506441)
      ·
        refine ⟨36928970380068384433879831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49238627173424512578506441 36928970380068384433879831)
        ·
          refine ⟨55393455570102576650819747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36928970380068384433879831 55393455570102576650819747)
          ·
            refine ⟨83090183355153864976229621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55393455570102576650819747 83090183355153864976229621)
            ·
              refine ⟨7789704689545674841521527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83090183355153864976229621 7789704689545674841521527)
              ·
                refine ⟨11684557034318512262282291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7789704689545674841521527 11684557034318512262282291)
                ·
                  refine ⟨17526835551477768393423437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11684557034318512262282291 17526835551477768393423437)
                  ·
                    refine ⟨6572563331804163147533789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17526835551477768393423437 6572563331804163147533789)
                    ·
                      refine ⟨2464711249426561180325171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6572563331804163147533789 2464711249426561180325171)
                      ·
                        rfl

theorem cell23_4800008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_4800008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800008 prefixEnd_4800008 := by exact prefixLift 4800008
  have htrace : WordTrace (prefixWord ++ tailWord_4800008) baseStart_4800008 baseEnd_4800008 := by
    simpa [prefixWord, tailWord_4800008, baseEnd_4800008] using wordTrace_append hprefix tailTrace_4800008
  have hstable : (prefixWord ++ tailWord_4800008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800008).length < 2 ^ (prefixWord ++ tailWord_4800008).sum := by decide
  have hdescent : baseEnd_4800008 < baseStart_4800008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800021 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_4800021 : Nat := 118140960795 + 4800021 * 2 ^ 59
def prefixEnd_4800021 : Nat := 4983230072969 + 3 ^ 40 * 4800021 * 2
def baseEnd_4800021 : Nat := 2464717924675069629462611

theorem tailTrace_4800021 : CollatzResearch.WordTrace tailWord_4800021 prefixEnd_4800021 2464717924675069629462611 := by
  unfold tailWord_4800021
  simp only [CollatzResearch.WordTrace]
  refine ⟨175071148543351170166023917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116714099028900780110682611 175071148543351170166023917)
  ·
    refine ⟨65651680703756688812258969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175071148543351170166023917 65651680703756688812258969)
    ·
      refine ⟨49238760527817516609194227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65651680703756688812258969 49238760527817516609194227)
      ·
        refine ⟨73858140791726274913791341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49238760527817516609194227 73858140791726274913791341)
        ·
          refine ⟨27696802796897353092671753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73858140791726274913791341 27696802796897353092671753)
          ·
            refine ⟨20772602097673014819503815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27696802796897353092671753 20772602097673014819503815)
            ·
              refine ⟨31158903146509522229255723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20772602097673014819503815 31158903146509522229255723)
              ·
                refine ⟨46738354719764283343883585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31158903146509522229255723 46738354719764283343883585)
                ·
                  refine ⟨35053766039823212507912689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46738354719764283343883585 35053766039823212507912689)
                  ·
                    refine ⟨26290324529867409380934517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35053766039823212507912689 26290324529867409380934517)
                    ·
                      refine ⟨2464717924675069629462611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26290324529867409380934517 2464717924675069629462611)
                      ·
                        rfl

theorem cell23_4800021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_4800021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800021 prefixEnd_4800021 := by exact prefixLift 4800021
  have htrace : WordTrace (prefixWord ++ tailWord_4800021) baseStart_4800021 baseEnd_4800021 := by
    simpa [prefixWord, tailWord_4800021, baseEnd_4800021] using wordTrace_append hprefix tailTrace_4800021
  have hstable : (prefixWord ++ tailWord_4800021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800021).length < 2 ^ (prefixWord ++ tailWord_4800021).sum := by decide
  have hdescent : baseEnd_4800021 < baseStart_4800021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800065 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_4800065 : Nat := 118140960795 + 4800065 * 2 ^ 59
def prefixEnd_4800065 : Nat := 4983230072969 + 3 ^ 40 * 4800065 * 2
def baseEnd_4800065 : Nat := 2464740517823867457312409

theorem tailTrace_4800065 : CollatzResearch.WordTrace tailWord_4800065 prefixEnd_4800065 2464740517823867457312409 := by
  unfold tailWord_4800065
  simp only [CollatzResearch.WordTrace]
  refine ⟨175072753355191765680625649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116715168903461177120417099 175072753355191765680625649)
  ·
    refine ⟨131304565016393824260469237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175072753355191765680625649 131304565016393824260469237)
    ·
      refine ⟨12309802970286921024418991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131304565016393824260469237 12309802970286921024418991)
      ·
        refine ⟨18464704455430381536628487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12309802970286921024418991 18464704455430381536628487)
        ·
          refine ⟨27697056683145572304942731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18464704455430381536628487 27697056683145572304942731)
          ·
            refine ⟨41545585024718358457414097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27697056683145572304942731 41545585024718358457414097)
            ·
              refine ⟨31159188768538768843060573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41545585024718358457414097 31159188768538768843060573)
              ·
                refine ⟨11684695788202038316147715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31159188768538768843060573 11684695788202038316147715)
                ·
                  refine ⟨17527043682303057474221573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11684695788202038316147715 17527043682303057474221573)
                  ·
                    refine ⟨3286320690431823276416545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17527043682303057474221573 3286320690431823276416545)
                    ·
                      refine ⟨2464740517823867457312409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286320690431823276416545 2464740517823867457312409)
                      ·
                        rfl

theorem cell23_4800065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_4800065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800065 prefixEnd_4800065 := by exact prefixLift 4800065
  have htrace : WordTrace (prefixWord ++ tailWord_4800065) baseStart_4800065 baseEnd_4800065 := by
    simpa [prefixWord, tailWord_4800065, baseEnd_4800065] using wordTrace_append hprefix tailTrace_4800065
  have hstable : (prefixWord ++ tailWord_4800065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800065).length < 2 ^ (prefixWord ++ tailWord_4800065).sum := by decide
  have hdescent : baseEnd_4800065 < baseStart_4800065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800088 : List Nat := [2, 1, 2, 2, 1, 2, 1, 7, 5]
def baseStart_4800088 : Nat := 118140960795 + 4800088 * 2 ^ 59
def prefixEnd_4800088 : Nat := 4983230072969 + 3 ^ 40 * 4800088 * 2
def baseEnd_4800088 : Nat := 273861369764324540813867

theorem tailTrace_4800088 : CollatzResearch.WordTrace tailWord_4800088 prefixEnd_4800088 273861369764324540813867 := by
  unfold tailWord_4800088
  simp only [CollatzResearch.WordTrace]
  refine ⟨87536796117054220304356459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116715728156072293739141945 87536796117054220304356459)
  ·
    refine ⟨131305194175581330456534689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87536796117054220304356459 131305194175581330456534689)
    ·
      refine ⟨98478895631685997842401017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131305194175581330456534689 98478895631685997842401017)
      ·
        refine ⟨73859171723764498381800763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98478895631685997842401017 73859171723764498381800763)
        ·
          refine ⟨110788757585646747572701145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73859171723764498381800763 110788757585646747572701145)
          ·
            refine ⟨83091568189235060679525859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110788757585646747572701145 83091568189235060679525859)
            ·
              refine ⟨124637352283852591019288789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83091568189235060679525859 124637352283852591019288789)
              ·
                refine ⟨2921187944152795102014581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 124637352283852591019288789 2921187944152795102014581)
                ·
                  refine ⟨273861369764324540813867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2921187944152795102014581 273861369764324540813867)
                  ·
                    rfl

theorem cell23_4800088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 5].length) (baseStart_4800088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800088 prefixEnd_4800088 := by exact prefixLift 4800088
  have htrace : WordTrace (prefixWord ++ tailWord_4800088) baseStart_4800088 baseEnd_4800088 := by
    simpa [prefixWord, tailWord_4800088, baseEnd_4800088] using wordTrace_append hprefix tailTrace_4800088
  have hstable : (prefixWord ++ tailWord_4800088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800088).length < 2 ^ (prefixWord ++ tailWord_4800088).sum := by decide
  have hdescent : baseEnd_4800088 < baseStart_4800088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800105 : List Nat := [1, 2, 1, 1, 1, 4, 6, 2, 5]
def baseStart_4800105 : Nat := 118140960795 + 4800105 * 2 ^ 59
def prefixEnd_4800105 : Nat := 4983230072969 + 3 ^ 40 * 4800105 * 2
def baseEnd_4800105 : Nat := 273862339672227477868025

theorem tailTrace_4800105 : CollatzResearch.WordTrace tailWord_4800105 prefixEnd_4800105 273862339672227477868025 := by
  unfold tailWord_4800105
  simp only [CollatzResearch.WordTrace]
  refine ⟨175074212275046852512081769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116716141516697901674721179 175074212275046852512081769)
  ·
    refine ⟨131305659206285139384061327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175074212275046852512081769 131305659206285139384061327)
    ·
      refine ⟨196958488809427709076091991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131305659206285139384061327 196958488809427709076091991)
      ·
        refine ⟨295437733214141563614137987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196958488809427709076091991 295437733214141563614137987)
        ·
          refine ⟨443156599821212345421206981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295437733214141563614137987 443156599821212345421206981)
          ·
            refine ⟨83091862466477314766476309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 443156599821212345421206981 83091862466477314766476309)
            ·
              refine ⟨3894931053116124129678577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83091862466477314766476309 3894931053116124129678577)
              ·
                refine ⟨2921198289837093097258933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3894931053116124129678577 2921198289837093097258933)
                ·
                  refine ⟨273862339672227477868025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2921198289837093097258933 273862339672227477868025)
                  ·
                    rfl

theorem cell23_4800105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 5].length) (baseStart_4800105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800105 prefixEnd_4800105 := by exact prefixLift 4800105
  have htrace : WordTrace (prefixWord ++ tailWord_4800105) baseStart_4800105 baseEnd_4800105 := by
    simpa [prefixWord, tailWord_4800105, baseEnd_4800105] using wordTrace_append hprefix tailTrace_4800105
  have hstable : (prefixWord ++ tailWord_4800105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800105).length < 2 ^ (prefixWord ++ tailWord_4800105).sum := by decide
  have hdescent : baseEnd_4800105 < baseStart_4800105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800135 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 2, 5]
def baseStart_4800135 : Nat := 118140960795 + 4800135 * 2 ^ 59
def prefixEnd_4800135 : Nat := 4983230072969 + 3 ^ 40 * 4800135 * 2
def baseEnd_4800135 : Nat := 821592153823227394479029

theorem tailTrace_4800135 : CollatzResearch.WordTrace tailWord_4800135 prefixEnd_4800135 821592153823227394479029 := by
  unfold tailWord_4800135
  simp only [CollatzResearch.WordTrace]
  refine ⟨175075306464938167635673859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116716870976625445090449239 175075306464938167635673859)
  ·
    refine ⟨262612959697407251453510789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175075306464938167635673859 262612959697407251453510789)
    ·
      refine ⟨49239929943263859647533273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262612959697407251453510789 49239929943263859647533273)
      ·
        refine ⟨36929947457447894735649955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49239929943263859647533273 36929947457447894735649955)
        ·
          refine ⟨55394921186171842103474933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36929947457447894735649955 55394921186171842103474933)
          ·
            refine ⟨5193273861203610197200775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55394921186171842103474933 5193273861203610197200775)
            ·
              refine ⟨7789910791805415295801163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5193273861203610197200775 7789910791805415295801163)
              ·
                refine ⟨11684866187708122943701745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7789910791805415295801163 11684866187708122943701745)
                ·
                  refine ⟨8763649640781092207776309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11684866187708122943701745 8763649640781092207776309)
                  ·
                    refine ⟨821592153823227394479029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8763649640781092207776309 821592153823227394479029)
                    ·
                      rfl

theorem cell23_4800135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_4800135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800135 prefixEnd_4800135 := by exact prefixLift 4800135
  have htrace : WordTrace (prefixWord ++ tailWord_4800135) baseStart_4800135 baseEnd_4800135 := by
    simpa [prefixWord, tailWord_4800135, baseEnd_4800135] using wordTrace_append hprefix tailTrace_4800135
  have hstable : (prefixWord ++ tailWord_4800135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800135).length < 2 ^ (prefixWord ++ tailWord_4800135).sum := by decide
  have hdescent : baseEnd_4800135 < baseStart_4800135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800178 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 6]
def baseStart_4800178 : Nat := 118140960795 + 4800178 * 2 ^ 59
def prefixEnd_4800178 : Nat := 4983230072969 + 3 ^ 40 * 4800178 * 2
def baseEnd_4800178 : Nat := 273866504570869501688821

theorem tailTrace_4800178 : CollatzResearch.WordTrace tailWord_4800178 prefixEnd_4800178 273866504570869501688821 := by
  unfold tailWord_4800178
  simp only [CollatzResearch.WordTrace]
  refine ⟨43769218700945596494872297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116717916535854923986326125 43769218700945596494872297)
  ·
    refine ⟨32826914025709197371154223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43769218700945596494872297 32826914025709197371154223)
    ·
      refine ⟨49240371038563796056731335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32826914025709197371154223 49240371038563796056731335)
      ·
        refine ⟨73860556557845694085097003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49240371038563796056731335 73860556557845694085097003)
        ·
          refine ⟨110790834836768541127645505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73860556557845694085097003 110790834836768541127645505)
          ·
            refine ⟨83093126127576405845734129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110790834836768541127645505 83093126127576405845734129)
            ·
              refine ⟨62319844595682304384300597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83093126127576405845734129 62319844595682304384300597)
              ·
                refine ⟨5842485430845216036028181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62319844595682304384300597 5842485430845216036028181)
                ·
                  refine ⟨273866504570869501688821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5842485430845216036028181 273866504570869501688821)
                  ·
                    rfl

theorem cell23_4800178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_4800178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800178 prefixEnd_4800178 := by exact prefixLift 4800178
  have htrace : WordTrace (prefixWord ++ tailWord_4800178) baseStart_4800178 baseEnd_4800178 := by
    simpa [prefixWord, tailWord_4800178, baseEnd_4800178] using wordTrace_append hprefix tailTrace_4800178
  have hstable : (prefixWord ++ tailWord_4800178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800178).length < 2 ^ (prefixWord ++ tailWord_4800178).sum := by decide
  have hdescent : baseEnd_4800178 < baseStart_4800178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800292 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_4800292 : Nat := 118140960795 + 4800292 * 2 ^ 59
def prefixEnd_4800292 : Nat := 4983230072969 + 3 ^ 40 * 4800292 * 2
def baseEnd_4800292 : Nat := 2464857077932438069173865

theorem tailTrace_4800292 : CollatzResearch.WordTrace tailWord_4800292 prefixEnd_4800292 2464857077932438069173865 := by
  unfold tailWord_4800292
  simp only [CollatzResearch.WordTrace]
  refine ⟨87540516362684691724569565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116720688483579588966092753 87540516362684691724569565)
  ·
    refine ⟨32827693636006759396713587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87540516362684691724569565 32827693636006759396713587)
    ·
      refine ⟨49241540454010139095070381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32827693636006759396713587 49241540454010139095070381)
      ·
        refine ⟨18465577670253802160651393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49241540454010139095070381 18465577670253802160651393)
        ·
          refine ⟨13849183252690351620488545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18465577670253802160651393 13849183252690351620488545)
          ·
            refine ⟨10386887439517763715366409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13849183252690351620488545 10386887439517763715366409)
            ·
              refine ⟨7790165579638322786524807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10386887439517763715366409 7790165579638322786524807)
              ·
                refine ⟨11685248369457484179787211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7790165579638322786524807 11685248369457484179787211)
                ·
                  refine ⟨17527872554186226269680817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11685248369457484179787211 17527872554186226269680817)
                  ·
                    refine ⟨13145904415639669702260613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17527872554186226269680817 13145904415639669702260613)
                    ·
                      refine ⟨2464857077932438069173865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13145904415639669702260613 2464857077932438069173865)
                      ·
                        rfl

theorem cell23_4800292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_4800292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800292 prefixEnd_4800292 := by exact prefixLift 4800292
  have htrace : WordTrace (prefixWord ++ tailWord_4800292) baseStart_4800292 baseEnd_4800292 := by
    simpa [prefixWord, tailWord_4800292, baseEnd_4800292] using wordTrace_append hprefix tailTrace_4800292
  have hstable : (prefixWord ++ tailWord_4800292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800292).length < 2 ^ (prefixWord ++ tailWord_4800292).sum := by decide
  have hdescent : baseEnd_4800292 < baseStart_4800292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800313 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4800313 : Nat := 118140960795 + 4800313 * 2 ^ 59
def prefixEnd_4800313 : Nat := 4983230072969 + 3 ^ 40 * 4800313 * 2
def baseEnd_4800313 : Nat := 2464867861026182487011269

theorem tailTrace_4800313 : CollatzResearch.WordTrace tailWord_4800313 prefixEnd_4800313 2464867861026182487011269 := by
  unfold tailWord_4800313
  simp only [CollatzResearch.WordTrace]
  refine ⟨175081798658293304035653593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116721199105528869357102395 175081798658293304035653593)
  ·
    refine ⟨131311348993719978026740195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175081798658293304035653593 131311348993719978026740195)
    ·
      refine ⟨196967023490579967040110293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131311348993719978026740195 196967023490579967040110293)
      ·
        refine ⟨4616414613060467977502585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 196967023490579967040110293 4616414613060467977502585)
        ·
          refine ⟨3462310959795350983126939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4616414613060467977502585 3462310959795350983126939)
          ·
            refine ⟨5193466439693026474690409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3462310959795350983126939 5193466439693026474690409)
            ·
              refine ⟨3895099829769769856017807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5193466439693026474690409 3895099829769769856017807)
              ·
                refine ⟨5842649744654654784026711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3895099829769769856017807 5842649744654654784026711)
                ·
                  refine ⟨8763974616981982176040067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5842649744654654784026711 8763974616981982176040067)
                  ·
                    refine ⟨13145961925472973264060101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8763974616981982176040067 13145961925472973264060101)
                    ·
                      refine ⟨2464867861026182487011269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13145961925472973264060101 2464867861026182487011269)
                      ·
                        rfl

theorem cell23_4800313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4800313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800313 prefixEnd_4800313 := by exact prefixLift 4800313
  have htrace : WordTrace (prefixWord ++ tailWord_4800313) baseStart_4800313 baseEnd_4800313 := by
    simpa [prefixWord, tailWord_4800313, baseEnd_4800313] using wordTrace_append hprefix tailTrace_4800313
  have hstable : (prefixWord ++ tailWord_4800313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800313).length < 2 ^ (prefixWord ++ tailWord_4800313).sum := by decide
  have hdescent : baseEnd_4800313 < baseStart_4800313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800335 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 1, 10, 2]
def baseStart_4800335 : Nat := 118140960795 + 4800335 * 2 ^ 59
def prefixEnd_4800335 : Nat := 4983230072969 + 3 ^ 40 * 4800335 * 2
def baseEnd_4800335 : Nat := 2464879157600581400936167

theorem tailTrace_4800335 : CollatzResearch.WordTrace tailWord_4800335 prefixEnd_4800335 2464879157600581400936167 := by
  unfold tailWord_4800335
  simp only [CollatzResearch.WordTrace]
  refine ⟨175082601064213601792954459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116721734042809067861969639 175082601064213601792954459)
  ·
    refine ⟨262623901596320402689431689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175082601064213601792954459 262623901596320402689431689)
    ·
      refine ⟨196967926197240302017073767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262623901596320402689431689 196967926197240302017073767)
      ·
        refine ⟨295451889295860453025610651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196967926197240302017073767 295451889295860453025610651)
        ·
          refine ⟨443177833943790679538415977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295451889295860453025610651 443177833943790679538415977)
          ·
            refine ⟨332383375457843009653811983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443177833943790679538415977 332383375457843009653811983)
            ·
              refine ⟨498575063186764514480717975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332383375457843009653811983 498575063186764514480717975)
              ·
                refine ⟨747862594780146771721076963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498575063186764514480717975 747862594780146771721076963)
                ·
                  refine ⟨1121793892170220157581615445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747862594780146771721076963 1121793892170220157581615445)
                  ·
                    refine ⟨3286505543467441867914889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1121793892170220157581615445 3286505543467441867914889)
                    ·
                      refine ⟨2464879157600581400936167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286505543467441867914889 2464879157600581400936167)
                      ·
                        rfl

theorem cell23_4800335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 10, 2].length) (baseStart_4800335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800335 prefixEnd_4800335 := by exact prefixLift 4800335
  have htrace : WordTrace (prefixWord ++ tailWord_4800335) baseStart_4800335 baseEnd_4800335 := by
    simpa [prefixWord, tailWord_4800335, baseEnd_4800335] using wordTrace_append hprefix tailTrace_4800335
  have hstable : (prefixWord ++ tailWord_4800335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800335).length < 2 ^ (prefixWord ++ tailWord_4800335).sum := by decide
  have hdescent : baseEnd_4800335 < baseStart_4800335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800356 : List Nat := [2, 3, 1, 1, 5, 1, 2, 2, 1, 3, 2]
def baseStart_4800356 : Nat := 118140960795 + 4800356 * 2 ^ 59
def prefixEnd_4800356 : Nat := 4983230072969 + 3 ^ 40 * 4800356 * 2
def baseEnd_4800356 : Nat := 2464889940694325818773571

theorem tailTrace_4800356 : CollatzResearch.WordTrace tailWord_4800356 prefixEnd_4800356 2464889940694325818773571 := by
  unfold tailWord_4800356
  simp only [CollatzResearch.WordTrace]
  refine ⟨87541683498568761189734461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116722244664758348252979281 87541683498568761189734461)
  ·
    refine ⟨32828131311963285446150423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87541683498568761189734461 32828131311963285446150423)
    ·
      refine ⟨49242196967944928169225635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32828131311963285446150423 49242196967944928169225635)
      ·
        refine ⟨73863295451917392253838453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49242196967944928169225635 73863295451917392253838453)
        ·
          refine ⟨6924683948617255523797355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73863295451917392253838453 6924683948617255523797355)
          ·
            refine ⟨10387025922925883285696033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6924683948617255523797355 10387025922925883285696033)
            ·
              refine ⟨7790269442194412464272025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10387025922925883285696033 7790269442194412464272025)
              ·
                refine ⟨5842702081645809348204019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7790269442194412464272025 5842702081645809348204019)
                ·
                  refine ⟨8764053122468714022306029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5842702081645809348204019 8764053122468714022306029)
                  ·
                    refine ⟨3286519920925767758364761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8764053122468714022306029 3286519920925767758364761)
                    ·
                      refine ⟨2464889940694325818773571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286519920925767758364761 2464889940694325818773571)
                      ·
                        rfl

theorem cell23_4800356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_4800356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800356 prefixEnd_4800356 := by exact prefixLift 4800356
  have htrace : WordTrace (prefixWord ++ tailWord_4800356) baseStart_4800356 baseEnd_4800356 := by
    simpa [prefixWord, tailWord_4800356, baseEnd_4800356] using wordTrace_append hprefix tailTrace_4800356
  have hstable : (prefixWord ++ tailWord_4800356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800356).length < 2 ^ (prefixWord ++ tailWord_4800356).sum := by decide
  have hdescent : baseEnd_4800356 < baseStart_4800356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800365 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_4800365 : Nat := 118140960795 + 4800365 * 2 ^ 59
def prefixEnd_4800365 : Nat := 4983230072969 + 3 ^ 40 * 4800365 * 2
def baseEnd_4800365 : Nat := 2464894562020216283561029

theorem tailTrace_4800365 : CollatzResearch.WordTrace tailWord_4800365 prefixEnd_4800365 2464894562020216283561029 := by
  unfold tailWord_4800365
  simp only [CollatzResearch.WordTrace]
  refine ⟨175083695254104916916546549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116722463502736611277697699 175083695254104916916546549)
  ·
    refine ⟨16414096430072335960926239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175083695254104916916546549 16414096430072335960926239)
    ·
      refine ⟨24621144645108503941389359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16414096430072335960926239 24621144645108503941389359)
      ·
        refine ⟨36931716967662755912084039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24621144645108503941389359 36931716967662755912084039)
        ·
          refine ⟨55397575451494133868126059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36931716967662755912084039 55397575451494133868126059)
          ·
            refine ⟨83096363177241200802189089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55397575451494133868126059 83096363177241200802189089)
            ·
              refine ⟨62322272382930900601641817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83096363177241200802189089 62322272382930900601641817)
              ·
                refine ⟨46741704287198175451231363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62322272382930900601641817 46741704287198175451231363)
                ·
                  refine ⟨70112556430797263176847045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46741704287198175451231363 70112556430797263176847045)
                  ·
                    refine ⟨13146104330774486845658821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70112556430797263176847045 13146104330774486845658821)
                    ·
                      refine ⟨2464894562020216283561029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13146104330774486845658821 2464894562020216283561029)
                      ·
                        rfl

theorem cell23_4800365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_4800365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800365 prefixEnd_4800365 := by exact prefixLift 4800365
  have htrace : WordTrace (prefixWord ++ tailWord_4800365) baseStart_4800365 baseEnd_4800365 := by
    simpa [prefixWord, tailWord_4800365, baseEnd_4800365] using wordTrace_append hprefix tailTrace_4800365
  have hstable : (prefixWord ++ tailWord_4800365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800365).length < 2 ^ (prefixWord ++ tailWord_4800365).sum := by decide
  have hdescent : baseEnd_4800365 < baseStart_4800365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800405 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_4800405 : Nat := 118140960795 + 4800405 * 2 ^ 59
def prefixEnd_4800405 : Nat := 4983230072969 + 3 ^ 40 * 4800405 * 2
def baseEnd_4800405 : Nat := 821638367082132042353615

theorem tailTrace_4800405 : CollatzResearch.WordTrace tailWord_4800405 prefixEnd_4800405 821638367082132042353615 := by
  unfold tailWord_4800405
  simp only [CollatzResearch.WordTrace]
  refine ⟨175085154173960003748002669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116723436115973335832001779 175085154173960003748002669)
  ·
    refine ⟨65656932815235001405501001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175085154173960003748002669 65656932815235001405501001)
    ·
      refine ⟨49242699611426251054125751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65656932815235001405501001 49242699611426251054125751)
      ·
        refine ⟨73864049417139376581188627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49242699611426251054125751 73864049417139376581188627)
        ·
          refine ⟨110796074125709064871782941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73864049417139376581188627 110796074125709064871782941)
          ·
            refine ⟨41548527797140899326918603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110796074125709064871782941 41548527797140899326918603)
            ·
              refine ⟨62322791695711348990377905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41548527797140899326918603 62322791695711348990377905)
              ·
                refine ⟨46742093771783511742783429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62322791695711348990377905 46742093771783511742783429)
                ·
                  refine ⟨8764142582209408451771893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46742093771783511742783429 8764142582209408451771893)
                  ·
                    refine ⟨821638367082132042353615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8764142582209408451771893 821638367082132042353615)
                    ·
                      rfl

theorem cell23_4800405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_4800405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800405 prefixEnd_4800405 := by exact prefixLift 4800405
  have htrace : WordTrace (prefixWord ++ tailWord_4800405) baseStart_4800405 baseEnd_4800405 := by
    simpa [prefixWord, tailWord_4800405, baseEnd_4800405] using wordTrace_append hprefix tailTrace_4800405
  have hstable : (prefixWord ++ tailWord_4800405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800405).length < 2 ^ (prefixWord ++ tailWord_4800405).sum := by decide
  have hdescent : baseEnd_4800405 < baseStart_4800405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800455 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_4800455 : Nat := 118140960795 + 4800455 * 2 ^ 59
def prefixEnd_4800455 : Nat := 4983230072969 + 3 ^ 40 * 4800455 * 2
def baseEnd_4800455 : Nat := 2464940775279120931435615

theorem tailTrace_4800455 : CollatzResearch.WordTrace tailWord_4800455 prefixEnd_4800455 2464940775279120931435615 := by
  unfold tailWord_4800455
  simp only [CollatzResearch.WordTrace]
  refine ⟨175086977823778862287322819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116724651882519241524881879 175086977823778862287322819)
  ·
    refine ⟨262630466735668293430984229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175086977823778862287322819 262630466735668293430984229)
    ·
      refine ⟨49243212512937805018309543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262630466735668293430984229 49243212512937805018309543)
      ·
        refine ⟨73864818769406707527464315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49243212512937805018309543 73864818769406707527464315)
        ·
          refine ⟨110797228154110061291196473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73864818769406707527464315 110797228154110061291196473)
          ·
            refine ⟨83097921115582545968397355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110797228154110061291196473 83097921115582545968397355)
            ·
              refine ⟨124646881673373818952596033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83097921115582545968397355 124646881673373818952596033)
              ·
                refine ⟨93485161255030364214447025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124646881673373818952596033 93485161255030364214447025)
                ·
                  refine ⟨70113870941272773160835269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93485161255030364214447025 70113870941272773160835269)
                  ·
                    refine ⟨13146350801488644967656613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70113870941272773160835269 13146350801488644967656613)
                    ·
                      refine ⟨2464940775279120931435615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13146350801488644967656613 2464940775279120931435615)
                      ·
                        rfl

theorem cell23_4800455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_4800455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800455 prefixEnd_4800455 := by exact prefixLift 4800455
  have htrace : WordTrace (prefixWord ++ tailWord_4800455) baseStart_4800455 baseEnd_4800455 := by
    simpa [prefixWord, tailWord_4800455, baseEnd_4800455] using wordTrace_append hprefix tailTrace_4800455
  have hstable : (prefixWord ++ tailWord_4800455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800455).length < 2 ^ (prefixWord ++ tailWord_4800455).sum := by decide
  have hdescent : baseEnd_4800455 < baseStart_4800455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800462 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_4800462 : Nat := 118140960795 + 4800462 * 2 ^ 59
def prefixEnd_4800462 : Nat := 4983230072969 + 3 ^ 40 * 4800462 * 2
def baseEnd_4800462 : Nat := 2464944369643702404048083

theorem tailTrace_4800462 : CollatzResearch.WordTrace tailWord_4800462 prefixEnd_4800462 2464944369643702404048083 := by
  unfold tailWord_4800462
  simp only [CollatzResearch.WordTrace]
  refine ⟨21885904141844187810353455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116724822089835668321885093 21885904141844187810353455)
  ·
    refine ⟨32828856212766281715530183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21885904141844187810353455 32828856212766281715530183)
    ·
      refine ⟨49243284319149422573295275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32828856212766281715530183 49243284319149422573295275)
      ·
        refine ⟨73864926478724133859942913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49243284319149422573295275 73864926478724133859942913)
        ·
          refine ⟨55398694859043100394957185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73864926478724133859942913 55398694859043100394957185)
          ·
            refine ⟨41549021144282325296217889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55398694859043100394957185 41549021144282325296217889)
            ·
              refine ⟨31161765858211743972163417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41549021144282325296217889 31161765858211743972163417)
              ·
                refine ⟨23371324393658807979122563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31161765858211743972163417 23371324393658807979122563)
                ·
                  refine ⟨35056986590488211968683845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23371324393658807979122563 35056986590488211968683845)
                  ·
                    refine ⟨6573184985716539744128221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35056986590488211968683845 6573184985716539744128221)
                    ·
                      refine ⟨2464944369643702404048083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6573184985716539744128221 2464944369643702404048083)
                      ·
                        rfl

theorem cell23_4800462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_4800462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800462 prefixEnd_4800462 := by exact prefixLift 4800462
  have htrace : WordTrace (prefixWord ++ tailWord_4800462) baseStart_4800462 baseEnd_4800462 := by
    simpa [prefixWord, tailWord_4800462, baseEnd_4800462] using wordTrace_append hprefix tailTrace_4800462
  have hstable : (prefixWord ++ tailWord_4800462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800462).length < 2 ^ (prefixWord ++ tailWord_4800462).sum := by decide
  have hdescent : baseEnd_4800462 < baseStart_4800462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800469 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 3, 4]
def baseStart_4800469 : Nat := 118140960795 + 4800469 * 2 ^ 59
def prefixEnd_4800469 : Nat := 4983230072969 + 3 ^ 40 * 4800469 * 2
def baseEnd_4800469 : Nat := 821649321336094625553517

theorem tailTrace_4800469 : CollatzResearch.WordTrace tailWord_4800469 prefixEnd_4800469 821649321336094625553517 := by
  unfold tailWord_4800469
  simp only [CollatzResearch.WordTrace]
  refine ⟨175087488445728142678332461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116724992297152095118888307 175087488445728142678332461)
  ·
    refine ⟨65657808167148053504374673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175087488445728142678332461 65657808167148053504374673)
    ·
      refine ⟨49243356125361040128281005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65657808167148053504374673 49243356125361040128281005)
      ·
        refine ⟨18466258547010390048105377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49243356125361040128281005 18466258547010390048105377)
        ·
          refine ⟨13849693910257792536079033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18466258547010390048105377 13849693910257792536079033)
          ·
            refine ⟨10387270432693344402059275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13849693910257792536079033 10387270432693344402059275)
            ·
              refine ⟨15580905649040016603088913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10387270432693344402059275 15580905649040016603088913)
              ·
                refine ⟨11685679236780012452316685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15580905649040016603088913 11685679236780012452316685)
                ·
                  refine ⟨4382129713792504669618757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11685679236780012452316685 4382129713792504669618757)
                  ·
                    refine ⟨821649321336094625553517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382129713792504669618757 821649321336094625553517)
                    ·
                      rfl

theorem cell23_4800469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_4800469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800469 prefixEnd_4800469 := by exact prefixLift 4800469
  have htrace : WordTrace (prefixWord ++ tailWord_4800469) baseStart_4800469 baseEnd_4800469 := by
    simpa [prefixWord, tailWord_4800469, baseEnd_4800469] using wordTrace_append hprefix tailTrace_4800469
  have hstable : (prefixWord ++ tailWord_4800469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800469).length < 2 ^ (prefixWord ++ tailWord_4800469).sum := by decide
  have hdescent : baseEnd_4800469 < baseStart_4800469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800479 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 3]
def baseStart_4800479 : Nat := 118140960795 + 4800479 * 2 ^ 59
def prefixEnd_4800479 : Nat := 4983230072969 + 3 ^ 40 * 4800479 * 2
def baseEnd_4800479 : Nat := 2464953098814828837535505

theorem tailTrace_4800479 : CollatzResearch.WordTrace tailWord_4800479 prefixEnd_4800479 2464953098814828837535505 := by
  unfold tailWord_4800479
  simp only [CollatzResearch.WordTrace]
  refine ⟨175087853175691914386196491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116725235450461276257464327 175087853175691914386196491)
  ·
    refine ⟨262631779763537871579294737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175087853175691914386196491 262631779763537871579294737)
    ·
      refine ⟨196973834822653403684471053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262631779763537871579294737 196973834822653403684471053)
      ·
        refine ⟨73865188058495026381676645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196973834822653403684471053 73865188058495026381676645)
        ·
          refine ⟨13849722760967817446564371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73865188058495026381676645 13849722760967817446564371)
          ·
            refine ⟨20774584141451726169846557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13849722760967817446564371 20774584141451726169846557)
            ·
              refine ⟨7790469053044397313692459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20774584141451726169846557 7790469053044397313692459)
              ·
                refine ⟨11685703579566595970538689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7790469053044397313692459 11685703579566595970538689)
                ·
                  refine ⟨8764277684674946977904017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11685703579566595970538689 8764277684674946977904017)
                  ·
                    refine ⟨6573208263506210233428013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8764277684674946977904017 6573208263506210233428013)
                    ·
                      refine ⟨2464953098814828837535505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6573208263506210233428013 2464953098814828837535505)
                      ·
                        rfl

theorem cell23_4800479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_4800479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800479 prefixEnd_4800479 := by exact prefixLift 4800479
  have htrace : WordTrace (prefixWord ++ tailWord_4800479) baseStart_4800479 baseEnd_4800479 := by
    simpa [prefixWord, tailWord_4800479, baseEnd_4800479] using wordTrace_append hprefix tailTrace_4800479
  have hstable : (prefixWord ++ tailWord_4800479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800479).length < 2 ^ (prefixWord ++ tailWord_4800479).sum := by decide
  have hdescent : baseEnd_4800479 < baseStart_4800479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800509 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_4800509 : Nat := 118140960795 + 4800509 * 2 ^ 59
def prefixEnd_4800509 : Nat := 4983230072969 + 3 ^ 40 * 4800509 * 2
def baseEnd_4800509 : Nat := 2464968503234463720160367

theorem tailTrace_4800509 : CollatzResearch.WordTrace tailWord_4800509 prefixEnd_4800509 2464968503234463720160367 := by
  unfold tailWord_4800509
  simp only [CollatzResearch.WordTrace]
  refine ⟨175088947365583229509788581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116725964910388819673192387 175088947365583229509788581)
  ·
    refine ⟨32829177631046855533085359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175088947365583229509788581 32829177631046855533085359)
    ·
      refine ⟨49243766446570283299628039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32829177631046855533085359 49243766446570283299628039)
      ·
        refine ⟨73865649669855424949442059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49243766446570283299628039 73865649669855424949442059)
        ·
          refine ⟨110798474504783137424163089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73865649669855424949442059 110798474504783137424163089)
          ·
            refine ⟨83098855878587353068122317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110798474504783137424163089 83098855878587353068122317)
            ·
              refine ⟨31162070954470257400545869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83098855878587353068122317 31162070954470257400545869)
              ·
                refine ⟨11685776607926346525204701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31162070954470257400545869 11685776607926346525204701)
                ·
                  refine ⟨4382166227972379946951763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11685776607926346525204701 4382166227972379946951763)
                  ·
                    refine ⟨6573249341958569920427645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4382166227972379946951763 6573249341958569920427645)
                    ·
                      refine ⟨2464968503234463720160367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6573249341958569920427645 2464968503234463720160367)
                      ·
                        rfl

theorem cell23_4800509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_4800509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800509 prefixEnd_4800509 := by exact prefixLift 4800509
  have htrace : WordTrace (prefixWord ++ tailWord_4800509) baseStart_4800509 baseEnd_4800509 := by
    simpa [prefixWord, tailWord_4800509, baseEnd_4800509] using wordTrace_append hprefix tailTrace_4800509
  have hstable : (prefixWord ++ tailWord_4800509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800509).length < 2 ^ (prefixWord ++ tailWord_4800509).sum := by decide
  have hdescent : baseEnd_4800509 < baseStart_4800509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800519 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 1, 5, 2]
def baseStart_4800519 : Nat := 118140960795 + 4800519 * 2 ^ 59
def prefixEnd_4800519 : Nat := 4983230072969 + 3 ^ 40 * 4800519 * 2
def baseEnd_4800519 : Nat := 2464973638041008681035321

theorem tailTrace_4800519 : CollatzResearch.WordTrace tailWord_4800519 prefixEnd_4800519 2464973638041008681035321 := by
  unfold tailWord_4800519
  simp only [CollatzResearch.WordTrace]
  refine ⟨175089312095547001217652611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116726208063698000811768407 175089312095547001217652611)
  ·
    refine ⟨262633968143320501826478917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175089312095547001217652611 262633968143320501826478917)
    ·
      refine ⟨49243869026872594092464797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262633968143320501826478917 49243869026872594092464797)
      ·
        refine ⟨18466450885077222784674299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49243869026872594092464797 18466450885077222784674299)
        ·
          refine ⟨27699676327615834177011449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18466450885077222784674299 27699676327615834177011449)
          ·
            refine ⟨20774757245711875632758587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27699676327615834177011449 20774757245711875632758587)
            ·
              refine ⟨31162135868567813449137881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20774757245711875632758587 31162135868567813449137881)
              ·
                refine ⟨23371601901425860086853411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31162135868567813449137881 23371601901425860086853411)
                ·
                  refine ⟨35057402852138790130280117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23371601901425860086853411 35057402852138790130280117)
                  ·
                    refine ⟨3286631517388011574713761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35057402852138790130280117 3286631517388011574713761)
                    ·
                      refine ⟨2464973638041008681035321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286631517388011574713761 2464973638041008681035321)
                      ·
                        rfl

theorem cell23_4800519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_4800519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800519 prefixEnd_4800519 := by exact prefixLift 4800519
  have htrace : WordTrace (prefixWord ++ tailWord_4800519) baseStart_4800519 baseEnd_4800519 := by
    simpa [prefixWord, tailWord_4800519, baseEnd_4800519] using wordTrace_append hprefix tailTrace_4800519
  have hstable : (prefixWord ++ tailWord_4800519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800519).length < 2 ^ (prefixWord ++ tailWord_4800519).sum := by decide
  have hdescent : baseEnd_4800519 < baseStart_4800519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800549 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 4]
def baseStart_4800549 : Nat := 118140960795 + 4800549 * 2 ^ 59
def prefixEnd_4800549 : Nat := 4983230072969 + 3 ^ 40 * 4800549 * 2
def baseEnd_4800549 : Nat := 2464989042460643563660183

theorem tailTrace_4800549 : CollatzResearch.WordTrace tailWord_4800549 prefixEnd_4800549 2464989042460643563660183 := by
  unfold tailWord_4800549
  simp only [CollatzResearch.WordTrace]
  refine ⟨175090406285438316341244701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116726937523625544227496467 175090406285438316341244701)
  ·
    refine ⟨65658902357039368627966763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175090406285438316341244701 65658902357039368627966763)
    ·
      refine ⟨98488353535559052941950145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65658902357039368627966763 98488353535559052941950145)
      ·
        refine ⟨73866265151669289706462609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98488353535559052941950145 73866265151669289706462609)
        ·
          refine ⟨55399698863751967279846957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73866265151669289706462609 55399698863751967279846957)
          ·
            refine ⟨20774887073906987729942609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55399698863751967279846957 20774887073906987729942609)
            ·
              refine ⟨15581165305430240797456957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20774887073906987729942609 15581165305430240797456957)
              ·
                refine ⟨5842936989536340299046359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15581165305430240797456957 5842936989536340299046359)
                ·
                  refine ⟨8764405484304510448569539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5842936989536340299046359 8764405484304510448569539)
                  ·
                    refine ⟨13146608226456765672854309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8764405484304510448569539 13146608226456765672854309)
                    ·
                      refine ⟨2464989042460643563660183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13146608226456765672854309 2464989042460643563660183)
                      ·
                        rfl

theorem cell23_4800549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_4800549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800549 prefixEnd_4800549 := by exact prefixLift 4800549
  have htrace : WordTrace (prefixWord ++ tailWord_4800549) baseStart_4800549 baseEnd_4800549 := by
    simpa [prefixWord, tailWord_4800549, baseEnd_4800549] using wordTrace_append hprefix tailTrace_4800549
  have hstable : (prefixWord ++ tailWord_4800549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800549).length < 2 ^ (prefixWord ++ tailWord_4800549).sum := by decide
  have hdescent : baseEnd_4800549 < baseStart_4800549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800562 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_4800562 : Nat := 118140960795 + 4800562 * 2 ^ 59
def prefixEnd_4800562 : Nat := 4983230072969 + 3 ^ 40 * 4800562 * 2
def baseEnd_4800562 : Nat := 2464995717709152012797623

theorem tailTrace_4800562 : CollatzResearch.WordTrace tailWord_4800562 prefixEnd_4800562 2464995717709152012797623 := by
  unfold tailWord_4800562
  simp only [CollatzResearch.WordTrace]
  refine ⟨43772720108597804890366985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116727253622927479707645293 43772720108597804890366985)
  ·
    refine ⟨32829540081448353667775239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43772720108597804890366985 32829540081448353667775239)
    ·
      refine ⟨49244310122172530501662859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32829540081448353667775239 49244310122172530501662859)
      ·
        refine ⟨73866465183258795752494289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49244310122172530501662859 73866465183258795752494289)
        ·
          refine ⟨55399848887444096814370717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73866465183258795752494289 55399848887444096814370717)
          ·
            refine ⟨20774943332791536305389019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55399848887444096814370717 20774943332791536305389019)
            ·
              refine ⟨31162414999187304458083529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20774943332791536305389019 31162414999187304458083529)
              ·
                refine ⟨23371811249390478343562647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31162414999187304458083529 23371811249390478343562647)
                ·
                  refine ⟨35057716874085717515343971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23371811249390478343562647 35057716874085717515343971)
                  ·
                    refine ⟨52586575311128576273015957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35057716874085717515343971 52586575311128576273015957)
                    ·
                      refine ⟨2464995717709152012797623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52586575311128576273015957 2464995717709152012797623)
                      ·
                        rfl

theorem cell23_4800562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_4800562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800562 prefixEnd_4800562 := by exact prefixLift 4800562
  have htrace : WordTrace (prefixWord ++ tailWord_4800562) baseStart_4800562 baseEnd_4800562 := by
    simpa [prefixWord, tailWord_4800562, baseEnd_4800562] using wordTrace_append hprefix tailTrace_4800562
  have hstable : (prefixWord ++ tailWord_4800562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800562).length < 2 ^ (prefixWord ++ tailWord_4800562).sum := by decide
  have hdescent : baseEnd_4800562 < baseStart_4800562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800572 : List Nat := [2, 2, 2, 2, 2, 1, 4, 8]
def baseStart_4800572 : Nat := 118140960795 + 4800572 * 2 ^ 59
def prefixEnd_4800572 : Nat := 4983230072969 + 3 ^ 40 * 4800572 * 2
def baseEnd_4800572 : Nat := 91296327870951739765651

theorem tailTrace_4800572 : CollatzResearch.WordTrace tailWord_4800572 prefixEnd_4800572 91296327870951739765651 := by
  unfold tailWord_4800572
  simp only [CollatzResearch.WordTrace]
  refine ⟨87545622582177495634665985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116727496776236660846221313 87545622582177495634665985)
  ·
    refine ⟨65659216936633121725999489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87545622582177495634665985 65659216936633121725999489)
    ·
      refine ⟨49244412702474841294499617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65659216936633121725999489 49244412702474841294499617)
      ·
        refine ⟨36933309526856130970874713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49244412702474841294499617 36933309526856130970874713)
        ·
          refine ⟨27699982145142098228156035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36933309526856130970874713 27699982145142098228156035)
          ·
            refine ⟨41549973217713147342234053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27699982145142098228156035 41549973217713147342234053)
            ·
              refine ⟨7790619978321215126668885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41549973217713147342234053 7790619978321215126668885)
              ·
                refine ⟨91296327870951739765651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7790619978321215126668885 91296327870951739765651)
                ·
                  rfl

theorem cell23_4800572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 8].length) (baseStart_4800572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800572 prefixEnd_4800572 := by exact prefixLift 4800572
  have htrace : WordTrace (prefixWord ++ tailWord_4800572) baseStart_4800572 baseEnd_4800572 := by
    simpa [prefixWord, tailWord_4800572, baseEnd_4800572] using wordTrace_append hprefix tailTrace_4800572
  have hstable : (prefixWord ++ tailWord_4800572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800572).length < 2 ^ (prefixWord ++ tailWord_4800572).sum := by decide
  have hdescent : baseEnd_4800572 < baseStart_4800572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800576 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 2, 4]
def baseStart_4800576 : Nat := 118140960795 + 4800576 * 2 ^ 59
def prefixEnd_4800576 : Nat := 4983230072969 + 3 ^ 40 * 4800576 * 2
def baseEnd_4800576 : Nat := 821667635479438319340853

theorem tailTrace_4800576 : CollatzResearch.WordTrace tailWord_4800576 prefixEnd_4800576 821667635479438319340853 := by
  unfold tailWord_4800576
  simp only [CollatzResearch.WordTrace]
  refine ⟨87545695528170249976238791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116727594037560333301651721 87545695528170249976238791)
  ·
    refine ⟨131318543292255374964358187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87545695528170249976238791 131318543292255374964358187)
    ·
      refine ⟨196977814938383062446537281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131318543292255374964358187 196977814938383062446537281)
      ·
        refine ⟨147733361203787296834902961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196977814938383062446537281 147733361203787296834902961)
        ·
          refine ⟨110800020902840472626177221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147733361203787296834902961 110800020902840472626177221)
          ·
            refine ⟨20775003919282588617408229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110800020902840472626177221 20775003919282588617408229)
            ·
              refine ⟨3895313234865485365764043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20775003919282588617408229 3895313234865485365764043)
              ·
                refine ⟨5842969852298228048646065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3895313234865485365764043 5842969852298228048646065)
                ·
                  refine ⟨4382227389223671036484549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5842969852298228048646065 4382227389223671036484549)
                  ·
                    refine ⟨821667635479438319340853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382227389223671036484549 821667635479438319340853)
                    ·
                      rfl

theorem cell23_4800576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 2, 4].length) (baseStart_4800576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800576 prefixEnd_4800576 := by exact prefixLift 4800576
  have htrace : WordTrace (prefixWord ++ tailWord_4800576) baseStart_4800576 baseEnd_4800576 := by
    simpa [prefixWord, tailWord_4800576, baseEnd_4800576] using wordTrace_append hprefix tailTrace_4800576
  have hstable : (prefixWord ++ tailWord_4800576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800576).length < 2 ^ (prefixWord ++ tailWord_4800576).sum := by decide
  have hdescent : baseEnd_4800576 < baseStart_4800576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800599 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 6, 1, 3]
def baseStart_4800599 : Nat := 118140960795 + 4800599 * 2 ^ 59
def prefixEnd_4800599 : Nat := 4983230072969 + 3 ^ 40 * 4800599 * 2
def baseEnd_4800599 : Nat := 2465014716493368368034953

theorem tailTrace_4800599 : CollatzResearch.WordTrace tailWord_4800599 prefixEnd_4800599 2465014716493368368034953 := by
  unfold tailWord_4800599
  simp only [CollatzResearch.WordTrace]
  refine ⟨175092229935257174880564851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116728153290171449920376567 175092229935257174880564851)
  ·
    refine ⟨262638344902885762320847277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175092229935257174880564851 262638344902885762320847277)
    ·
      refine ⟨98489379338582160870317729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262638344902885762320847277 98489379338582160870317729)
      ·
        refine ⟨73867034503936620652738297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98489379338582160870317729 73867034503936620652738297)
        ·
          refine ⟨55400275877952465489553723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73867034503936620652738297 55400275877952465489553723)
          ·
            refine ⟨83100413816928698234330585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55400275877952465489553723 83100413816928698234330585)
            ·
              refine ⟨62325310362696523675747939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83100413816928698234330585 62325310362696523675747939)
              ·
                refine ⟨93487965544044785513621909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62325310362696523675747939 93487965544044785513621909)
                ·
                  refine ⟨4382248384877099320951027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93487965544044785513621909 4382248384877099320951027)
                  ·
                    refine ⟨6573372577315648981426541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4382248384877099320951027 6573372577315648981426541)
                    ·
                      refine ⟨2465014716493368368034953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6573372577315648981426541 2465014716493368368034953)
                      ·
                        rfl

theorem cell23_4800599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_4800599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800599 prefixEnd_4800599 := by exact prefixLift 4800599
  have htrace : WordTrace (prefixWord ++ tailWord_4800599) baseStart_4800599 baseEnd_4800599 := by
    simpa [prefixWord, tailWord_4800599, baseEnd_4800599] using wordTrace_append hprefix tailTrace_4800599
  have hstable : (prefixWord ++ tailWord_4800599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800599).length < 2 ^ (prefixWord ++ tailWord_4800599).sum := by decide
  have hdescent : baseEnd_4800599 < baseStart_4800599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800606 : List Nat := [4, 4, 1, 1, 2, 11]
def baseStart_4800606 : Nat := 118140960795 + 4800606 * 2 ^ 59
def prefixEnd_4800606 : Nat := 4983230072969 + 3 ^ 40 * 4800606 * 2
def baseEnd_4800606 : Nat := 10144108275135596052047

theorem tailTrace_4800606 : CollatzResearch.WordTrace tailWord_4800606 prefixEnd_4800606 10144108275135596052047 := by
  unfold tailWord_4800606
  simp only [CollatzResearch.WordTrace]
  refine ⟨21886560655778976884508709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116728323497487876717379781 21886560655778976884508709)
  ·
    refine ⟨4103730122958558165845383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21886560655778976884508709 4103730122958558165845383)
    ·
      refine ⟨6155595184437837248768075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4103730122958558165845383 6155595184437837248768075)
      ·
        refine ⟨9233392776656755873152113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6155595184437837248768075 9233392776656755873152113)
        ·
          refine ⟨6925044582492566904864085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9233392776656755873152113 6925044582492566904864085)
          ·
            refine ⟨10144108275135596052047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6925044582492566904864085 10144108275135596052047)
            ·
              rfl

theorem cell23_4800606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 11].length) (baseStart_4800606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800606 prefixEnd_4800606 := by exact prefixLift 4800606
  have htrace : WordTrace (prefixWord ++ tailWord_4800606) baseStart_4800606 baseEnd_4800606 := by
    simpa [prefixWord, tailWord_4800606, baseEnd_4800606] using wordTrace_append hprefix tailTrace_4800606
  have hstable : (prefixWord ++ tailWord_4800606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800606).length < 2 ^ (prefixWord ++ tailWord_4800606).sum := by decide
  have hdescent : baseEnd_4800606 < baseStart_4800606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800612 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_4800612 : Nat := 118140960795 + 4800612 * 2 ^ 59
def prefixEnd_4800612 : Nat := 4983230072969 + 3 ^ 40 * 4800612 * 2
def baseEnd_4800612 : Nat := 2465021391741876817172393

theorem tailTrace_4800612 : CollatzResearch.WordTrace tailWord_4800612 prefixEnd_4800612 2465021391741876817172393 := by
  unfold tailWord_4800612
  simp only [CollatzResearch.WordTrace]
  refine ⟨87546352042105039050394045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116728469389473385400525393 87546352042105039050394045)
  ·
    refine ⟨32829882015789389643897767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87546352042105039050394045 32829882015789389643897767)
    ·
      refine ⟨49244823023684084465846651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32829882015789389643897767 49244823023684084465846651)
      ·
        refine ⟨73867234535526126698769977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49244823023684084465846651 73867234535526126698769977)
        ·
          refine ⟨55400425901644595024077483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73867234535526126698769977 55400425901644595024077483)
          ·
            refine ⟨83100638852466892536116225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55400425901644595024077483 83100638852466892536116225)
            ·
              refine ⟨62325479139350169402087169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83100638852466892536116225 62325479139350169402087169)
              ·
                refine ⟨46744109354512627051565377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62325479139350169402087169 46744109354512627051565377)
                ·
                  refine ⟨35058082015884470288674033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46744109354512627051565377 35058082015884470288674033)
                  ·
                    refine ⟨26293561511913352716505525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35058082015884470288674033 26293561511913352716505525)
                    ·
                      refine ⟨2465021391741876817172393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26293561511913352716505525 2465021391741876817172393)
                      ·
                        rfl

theorem cell23_4800612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_4800612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800612 prefixEnd_4800612 := by exact prefixLift 4800612
  have htrace : WordTrace (prefixWord ++ tailWord_4800612) baseStart_4800612 baseEnd_4800612 := by
    simpa [prefixWord, tailWord_4800612, baseEnd_4800612] using wordTrace_append hprefix tailTrace_4800612
  have hstable : (prefixWord ++ tailWord_4800612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800612).length < 2 ^ (prefixWord ++ tailWord_4800612).sum := by decide
  have hdescent : baseEnd_4800612 < baseStart_4800612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800626 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 3, 3, 2]
def baseStart_4800626 : Nat := 118140960795 + 4800626 * 2 ^ 59
def prefixEnd_4800626 : Nat := 4983230072969 + 3 ^ 40 * 4800626 * 2
def baseEnd_4800626 : Nat := 2465028580471039762397329

theorem tailTrace_4800626 : CollatzResearch.WordTrace tailWord_4800626 prefixEnd_4800626 2465028580471039762397329 := by
  unfold tailWord_4800626
  simp only [CollatzResearch.WordTrace]
  refine ⟨43773303676539839622949433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116728809804106238994531821 43773303676539839622949433)
  ·
    refine ⟨32829977757404879717212075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43773303676539839622949433 32829977757404879717212075)
    ·
      refine ⟨49244966636107319575818113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32829977757404879717212075 49244966636107319575818113)
      ·
        refine ⟨36933724977080489681863585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49244966636107319575818113 36933724977080489681863585)
        ·
          refine ⟨27700293732810367261397689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36933724977080489681863585 27700293732810367261397689)
          ·
            refine ⟨20775220299607775446048267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27700293732810367261397689 20775220299607775446048267)
            ·
              refine ⟨31162830449411663169072401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20775220299607775446048267 31162830449411663169072401)
              ·
                refine ⟨23372122837058747376804301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31162830449411663169072401 23372122837058747376804301)
                ·
                  refine ⟨8764546063897030266301613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23372122837058747376804301 8764546063897030266301613)
                  ·
                    refine ⟨3286704773961386349863105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8764546063897030266301613 3286704773961386349863105)
                    ·
                      refine ⟨2465028580471039762397329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286704773961386349863105 2465028580471039762397329)
                      ·
                        rfl

theorem cell23_4800626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_4800626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800626 prefixEnd_4800626 := by exact prefixLift 4800626
  have htrace : WordTrace (prefixWord ++ tailWord_4800626) baseStart_4800626 baseEnd_4800626 := by
    simpa [prefixWord, tailWord_4800626, baseEnd_4800626] using wordTrace_append hprefix tailTrace_4800626
  have hstable : (prefixWord ++ tailWord_4800626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800626).length < 2 ^ (prefixWord ++ tailWord_4800626).sum := by decide
  have hdescent : baseEnd_4800626 < baseStart_4800626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800656 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 4, 2, 2]
def baseStart_4800656 : Nat := 118140960795 + 4800656 * 2 ^ 59
def prefixEnd_4800656 : Nat := 4983230072969 + 3 ^ 40 * 4800656 * 2
def baseEnd_4800656 : Nat := 2465043984890674645022191

theorem tailTrace_4800656 : CollatzResearch.WordTrace tailWord_4800656 prefixEnd_4800656 2465043984890674645022191 := by
  unfold tailWord_4800656
  simp only [CollatzResearch.WordTrace]
  refine ⟨87547154448025336807694911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116729539264033782410259881 87547154448025336807694911)
  ·
    refine ⟨131320731672038005211542367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87547154448025336807694911 131320731672038005211542367)
    ·
      refine ⟨196981097508057007817313551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131320731672038005211542367 196981097508057007817313551)
      ·
        refine ⟨295471646262085511725970327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196981097508057007817313551 295471646262085511725970327)
        ·
          refine ⟨443207469393128267588955491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295471646262085511725970327 443207469393128267588955491)
          ·
            refine ⟨664811204089692401383433237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443207469393128267588955491 664811204089692401383433237)
            ·
              refine ⟨31163025191704331314848433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 664811204089692401383433237 31163025191704331314848433)
              ·
                refine ⟨23372268893778248486136325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31163025191704331314848433 23372268893778248486136325)
                ·
                  refine ⟨4382300417583421591150561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23372268893778248486136325 4382300417583421591150561)
                  ·
                    refine ⟨3286725313187566193362921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4382300417583421591150561 3286725313187566193362921)
                    ·
                      refine ⟨2465043984890674645022191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286725313187566193362921 2465043984890674645022191)
                      ·
                        rfl

theorem cell23_4800656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4, 2, 2].length) (baseStart_4800656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800656 prefixEnd_4800656 := by exact prefixLift 4800656
  have htrace : WordTrace (prefixWord ++ tailWord_4800656) baseStart_4800656 baseEnd_4800656 := by
    simpa [prefixWord, tailWord_4800656, baseEnd_4800656] using wordTrace_append hprefix tailTrace_4800656
  have hstable : (prefixWord ++ tailWord_4800656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800656).length < 2 ^ (prefixWord ++ tailWord_4800656).sum := by decide
  have hdescent : baseEnd_4800656 < baseStart_4800656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800669 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_4800669 : Nat := 118140960795 + 4800669 * 2 ^ 59
def prefixEnd_4800669 : Nat := 4983230072969 + 3 ^ 40 * 4800669 * 2
def baseEnd_4800669 : Nat := 2465050660139183094159631

theorem tailTrace_4800669 : CollatzResearch.WordTrace tailWord_4800669 prefixEnd_4800669 2465050660139183094159631 := by
  unfold tailWord_4800669
  simp only [CollatzResearch.WordTrace]
  refine ⟨175094783045003576835613061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116729855363335717890408707 175094783045003576835613061)
  ·
    refine ⟨32830271820938170656677449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175094783045003576835613061 32830271820938170656677449)
    ·
      refine ⟨24622703865703627992508087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32830271820938170656677449 24622703865703627992508087)
      ·
        refine ⟨36934055798555441988762131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24622703865703627992508087 36934055798555441988762131)
        ·
          refine ⟨55401083697833162983143197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36934055798555441988762131 55401083697833162983143197)
          ·
            refine ⟨20775406386687436118678699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55401083697833162983143197 20775406386687436118678699)
            ·
              refine ⟨31163109580031154178018049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20775406386687436118678699 31163109580031154178018049)
              ·
                refine ⟨23372332185023365633513537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31163109580031154178018049 23372332185023365633513537)
                ·
                  refine ⟨17529249138767524225135153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23372332185023365633513537 17529249138767524225135153)
                  ·
                    refine ⟨13146936854075643168851365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17529249138767524225135153 13146936854075643168851365)
                    ·
                      refine ⟨2465050660139183094159631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13146936854075643168851365 2465050660139183094159631)
                      ·
                        rfl

theorem cell23_4800669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_4800669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800669 prefixEnd_4800669 := by exact prefixLift 4800669
  have htrace : WordTrace (prefixWord ++ tailWord_4800669) baseStart_4800669 baseEnd_4800669 := by
    simpa [prefixWord, tailWord_4800669, baseEnd_4800669] using wordTrace_append hprefix tailTrace_4800669
  have hstable : (prefixWord ++ tailWord_4800669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800669).length < 2 ^ (prefixWord ++ tailWord_4800669).sum := by decide
  have hdescent : baseEnd_4800669 < baseStart_4800669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800673 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 4, 2, 2]
def baseStart_4800673 : Nat := 118140960795 + 4800673 * 2 ^ 59
def prefixEnd_4800673 : Nat := 4983230072969 + 3 ^ 40 * 4800673 * 2
def baseEnd_4800673 : Nat := 2465052714061801078509613

theorem tailTrace_4800673 : CollatzResearch.WordTrace tailWord_4800673 prefixEnd_4800673 2465052714061801078509613 := by
  unfold tailWord_4800673
  simp only [CollatzResearch.WordTrace]
  refine ⟨175094928936989085518758673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116729952624659390345839115 175094928936989085518758673)
  ·
    refine ⟨131321196702741814139069005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175094928936989085518758673 131321196702741814139069005)
    ·
      refine ⟨49245448763528180302150877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131321196702741814139069005 49245448763528180302150877)
      ·
        refine ⟨18467043286323067613306579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49245448763528180302150877 18467043286323067613306579)
        ·
          refine ⟨27700564929484601419959869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18467043286323067613306579 27700564929484601419959869)
          ·
            refine ⟨10387711848556725532484951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27700564929484601419959869 10387711848556725532484951)
            ·
              refine ⟨15581567772835088298727427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10387711848556725532484951 15581567772835088298727427)
              ·
                refine ⟨23372351659252632448091141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15581567772835088298727427 23372351659252632448091141)
                ·
                  refine ⟨4382315936109868584017089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23372351659252632448091141 4382315936109868584017089)
                  ·
                    refine ⟨3286736952082401438012817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4382315936109868584017089 3286736952082401438012817)
                    ·
                      refine ⟨2465052714061801078509613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286736952082401438012817 2465052714061801078509613)
                      ·
                        rfl

theorem cell23_4800673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_4800673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800673 prefixEnd_4800673 := by exact prefixLift 4800673
  have htrace : WordTrace (prefixWord ++ tailWord_4800673) baseStart_4800673 baseEnd_4800673 := by
    simpa [prefixWord, tailWord_4800673, baseEnd_4800673] using wordTrace_append hprefix tailTrace_4800673
  have hstable : (prefixWord ++ tailWord_4800673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800673).length < 2 ^ (prefixWord ++ tailWord_4800673).sum := by decide
  have hdescent : baseEnd_4800673 < baseStart_4800673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800690 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2]
def baseStart_4800690 : Nat := 118140960795 + 4800690 * 2 ^ 59
def prefixEnd_4800690 : Nat := 4983230072969 + 3 ^ 40 * 4800690 * 2
def baseEnd_4800690 : Nat := 2465061443232927511997035

theorem tailTrace_4800690 : CollatzResearch.WordTrace tailWord_4800690 prefixEnd_4800690 2465061443232927511997035 := by
  unfold tailWord_4800690
  simp only [CollatzResearch.WordTrace]
  refine ⟨43773887244481874355531881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116730365985284998281418349 43773887244481874355531881)
  ·
    refine ⟨32830415433361405766648911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43773887244481874355531881 32830415433361405766648911)
    ·
      refine ⟨49245623150042108649973367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32830415433361405766648911 49245623150042108649973367)
      ·
        refine ⟨73868434725063162974960051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49245623150042108649973367 73868434725063162974960051)
        ·
          refine ⟨110802652087594744462440077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73868434725063162974960051 110802652087594744462440077)
          ·
            refine ⟨41550994532848029173415029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110802652087594744462440077 41550994532848029173415029)
            ·
              refine ⟨3895405737454502735007659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41550994532848029173415029 3895405737454502735007659)
              ·
                refine ⟨5843108606181754102511489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3895405737454502735007659 5843108606181754102511489)
                ·
                  refine ⟨4382331454636315576883617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5843108606181754102511489 4382331454636315576883617)
                  ·
                    refine ⟨3286748590977236682662713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4382331454636315576883617 3286748590977236682662713)
                    ·
                      refine ⟨2465061443232927511997035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286748590977236682662713 2465061443232927511997035)
                      ·
                        rfl

theorem cell23_4800690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_4800690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800690 prefixEnd_4800690 := by exact prefixLift 4800690
  have htrace : WordTrace (prefixWord ++ tailWord_4800690) baseStart_4800690 baseEnd_4800690 := by
    simpa [prefixWord, tailWord_4800690, baseEnd_4800690] using wordTrace_append hprefix tailTrace_4800690
  have hstable : (prefixWord ++ tailWord_4800690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800690).length < 2 ^ (prefixWord ++ tailWord_4800690).sum := by decide
  have hdescent : baseEnd_4800690 < baseStart_4800690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800729 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 4]
def baseStart_4800729 : Nat := 118140960795 + 4800729 * 2 ^ 59
def prefixEnd_4800729 : Nat := 4983230072969 + 3 ^ 40 * 4800729 * 2
def baseEnd_4800729 : Nat := 2465081468978452859409355

theorem tailTrace_4800729 : CollatzResearch.WordTrace tailWord_4800729 prefixEnd_4800729 2465081468978452859409355 := by
  unfold tailWord_4800729
  simp only [CollatzResearch.WordTrace]
  refine ⟨175096971424786207082797241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116731314283190804721864827 175096971424786207082797241)
  ·
    refine ⟨131322728568589655312097931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175096971424786207082797241 131322728568589655312097931)
    ·
      refine ⟨196984092852884482968146897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131322728568589655312097931 196984092852884482968146897)
      ·
        refine ⟨147738069639663362226110173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196984092852884482968146897 147738069639663362226110173)
        ·
          refine ⟨55401776114873760834791315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147738069639663362226110173 55401776114873760834791315)
          ·
            refine ⟨83102664172310641252186973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55401776114873760834791315 83102664172310641252186973)
            ·
              refine ⟨31163499064616490469570115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83102664172310641252186973 31163499064616490469570115)
              ·
                refine ⟨46745248596924735704355173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31163499064616490469570115 46745248596924735704355173)
                ·
                  refine ⟨8764734111923387944566595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46745248596924735704355173 8764734111923387944566595)
                  ·
                    refine ⟨13147101167885081916849893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8764734111923387944566595 13147101167885081916849893)
                    ·
                      refine ⟨2465081468978452859409355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13147101167885081916849893 2465081468978452859409355)
                      ·
                        rfl

theorem cell23_4800729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_4800729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800729 prefixEnd_4800729 := by exact prefixLift 4800729
  have htrace : WordTrace (prefixWord ++ tailWord_4800729) baseStart_4800729 baseEnd_4800729 := by
    simpa [prefixWord, tailWord_4800729, baseEnd_4800729] using wordTrace_append hprefix tailTrace_4800729
  have hstable : (prefixWord ++ tailWord_4800729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800729).length < 2 ^ (prefixWord ++ tailWord_4800729).sum := by decide
  have hdescent : baseEnd_4800729 < baseStart_4800729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800746 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_4800746 : Nat := 118140960795 + 4800746 * 2 ^ 59
def prefixEnd_4800746 : Nat := 4983230072969 + 3 ^ 40 * 4800746 * 2
def baseEnd_4800746 : Nat := 2465090198149579292896777

theorem tailTrace_4800746 : CollatzResearch.WordTrace tailWord_4800746 prefixEnd_4800746 2465090198149579292896777 := by
  unfold tailWord_4800746
  simp only [CollatzResearch.WordTrace]
  refine ⟨43774397866431154746541523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116731727643816412657444061 43774397866431154746541523)
  ·
    refine ⟨65661596799646732119812285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43774397866431154746541523 65661596799646732119812285)
    ·
      refine ⟨24623098799867524544929607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65661596799646732119812285 24623098799867524544929607)
      ·
        refine ⟨36934648199801286817394411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24623098799867524544929607 36934648199801286817394411)
        ·
          refine ⟨55401972299701930226091617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36934648199801286817394411 55401972299701930226091617)
          ·
            refine ⟨41551479224776447669568713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55401972299701930226091617 41551479224776447669568713)
            ·
              refine ⟨31163609418582335752176535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41551479224776447669568713 31163609418582335752176535)
              ·
                refine ⟨46745414127873503628264803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31163609418582335752176535 46745414127873503628264803)
                ·
                  refine ⟨70118121191810255442397205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46745414127873503628264803 70118121191810255442397205)
                  ·
                    refine ⟨3286786930866105723862369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70118121191810255442397205 3286786930866105723862369)
                    ·
                      refine ⟨2465090198149579292896777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286786930866105723862369 2465090198149579292896777)
                      ·
                        rfl

theorem cell23_4800746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_4800746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800746 prefixEnd_4800746 := by exact prefixLift 4800746
  have htrace : WordTrace (prefixWord ++ tailWord_4800746) baseStart_4800746 baseEnd_4800746 := by
    simpa [prefixWord, tailWord_4800746, baseEnd_4800746] using wordTrace_append hprefix tailTrace_4800746
  have hstable : (prefixWord ++ tailWord_4800746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800746).length < 2 ^ (prefixWord ++ tailWord_4800746).sum := by decide
  have hdescent : baseEnd_4800746 < baseStart_4800746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800807 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4800807 : Nat := 118140960795 + 4800807 * 2 ^ 59
def prefixEnd_4800807 : Nat := 4983230072969 + 3 ^ 40 * 4800807 * 2
def baseEnd_4800807 : Nat := 821707173489834518077999

theorem tailTrace_4800807 : CollatzResearch.WordTrace tailWord_4800807 prefixEnd_4800807 821707173489834518077999 := by
  unfold tailWord_4800807
  simp only [CollatzResearch.WordTrace]
  refine ⟨175099816318503626404136675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116733210879002417602757783 175099816318503626404136675)
  ·
    refine ⟨262649724477755439606205013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175099816318503626404136675 262649724477755439606205013)
    ·
      refine ⟨3077926458723696557885215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 262649724477755439606205013 3077926458723696557885215)
      ·
        refine ⟨4616889688085544836827823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3077926458723696557885215 4616889688085544836827823)
        ·
          refine ⟨6925334532128317255241735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4616889688085544836827823 6925334532128317255241735)
          ·
            refine ⟨10388001798192475882862603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6925334532128317255241735 10388001798192475882862603)
            ·
              refine ⟨15582002697288713824293905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10388001798192475882862603 15582002697288713824293905)
              ·
                refine ⟨11686502022966535368220429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15582002697288713824293905 11686502022966535368220429)
                ·
                  refine ⟨4382438258612450763082661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11686502022966535368220429 4382438258612450763082661)
                  ·
                    refine ⟨821707173489834518077999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382438258612450763082661 821707173489834518077999)
                    ·
                      rfl

theorem cell23_4800807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4800807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800807 prefixEnd_4800807 := by exact prefixLift 4800807
  have htrace : WordTrace (prefixWord ++ tailWord_4800807) baseStart_4800807 baseEnd_4800807 := by
    simpa [prefixWord, tailWord_4800807, baseEnd_4800807] using wordTrace_append hprefix tailTrace_4800807
  have hstable : (prefixWord ++ tailWord_4800807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800807).length < 2 ^ (prefixWord ++ tailWord_4800807).sum := by decide
  have hdescent : baseEnd_4800807 < baseStart_4800807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800856 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 3, 2, 3]
def baseStart_4800856 : Nat := 118140960795 + 4800856 * 2 ^ 59
def prefixEnd_4800856 : Nat := 4983230072969 + 3 ^ 40 * 4800856 * 2
def baseEnd_4800856 : Nat := 2465146681021573862521271

theorem tailTrace_4800856 : CollatzResearch.WordTrace tailWord_4800856 prefixEnd_4800856 2465146681021573862521271 := by
  unfold tailWord_4800856
  simp only [CollatzResearch.WordTrace]
  refine ⟨87550801747663053886335211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116734402330217405181780281 87550801747663053886335211)
  ·
    refine ⟨131326202621494580829502817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87550801747663053886335211 131326202621494580829502817)
    ·
      refine ⟨98494651966120935622127113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131326202621494580829502817 98494651966120935622127113)
      ·
        refine ⟨73870988974590701716595335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98494651966120935622127113 73870988974590701716595335)
        ·
          refine ⟨110806483461886052574893003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73870988974590701716595335 110806483461886052574893003)
          ·
            refine ⟨166209725192829078862339505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110806483461886052574893003 166209725192829078862339505)
            ·
              refine ⟨124657293894621809146754629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166209725192829078862339505 124657293894621809146754629)
              ·
                refine ⟨23373242605241589215016493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124657293894621809146754629 23373242605241589215016493)
                ·
                  refine ⟨8764965976965595955631185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23373242605241589215016493 8764965976965595955631185)
                  ·
                    refine ⟨6573724482724196966723389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8764965976965595955631185 6573724482724196966723389)
                    ·
                      refine ⟨2465146681021573862521271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6573724482724196966723389 2465146681021573862521271)
                      ·
                        rfl

theorem cell23_4800856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_4800856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800856 prefixEnd_4800856 := by exact prefixLift 4800856
  have htrace : WordTrace (prefixWord ++ tailWord_4800856) baseStart_4800856 baseEnd_4800856 := by
    simpa [prefixWord, tailWord_4800856, baseEnd_4800856] using wordTrace_append hprefix tailTrace_4800856
  have hstable : (prefixWord ++ tailWord_4800856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800856).length < 2 ^ (prefixWord ++ tailWord_4800856).sum := by decide
  have hdescent : baseEnd_4800856 < baseStart_4800856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800873 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 1, 2, 3]
def baseStart_4800873 : Nat := 118140960795 + 4800873 * 2 ^ 59
def prefixEnd_4800873 : Nat := 4983230072969 + 3 ^ 40 * 4800873 * 2
def baseEnd_4800873 : Nat := 2465155410192700296008693

theorem tailTrace_4800873 : CollatzResearch.WordTrace tailWord_4800873 prefixEnd_4800873 2465155410192700296008693 := by
  unfold tailWord_4800873
  simp only [CollatzResearch.WordTrace]
  refine ⟨175102223536264519676039273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116734815690843013117359515 175102223536264519676039273)
  ·
    refine ⟨131326667652198389757029455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175102223536264519676039273 131326667652198389757029455)
    ·
      refine ⟨196990001478297584635544183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131326667652198389757029455 196990001478297584635544183)
      ·
        refine ⟨295485002217446376953316275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196990001478297584635544183 295485002217446376953316275)
        ·
          refine ⟨443227503326169565429974413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295485002217446376953316275 443227503326169565429974413)
          ·
            refine ⟨166210313747313587036240405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 443227503326169565429974413 166210313747313587036240405)
            ·
              refine ⟨7791108456905324392323769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166210313747313587036240405 7791108456905324392323769)
              ·
                refine ⟨5843331342678993294242827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7791108456905324392323769 5843331342678993294242827)
                ·
                  refine ⟨8764997014018489941364241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5843331342678993294242827 8764997014018489941364241)
                  ·
                    refine ⟨6573747760513867456023181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8764997014018489941364241 6573747760513867456023181)
                    ·
                      refine ⟨2465155410192700296008693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6573747760513867456023181 2465155410192700296008693)
                      ·
                        rfl

theorem cell23_4800873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 2, 3].length) (baseStart_4800873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800873 prefixEnd_4800873 := by exact prefixLift 4800873
  have htrace : WordTrace (prefixWord ++ tailWord_4800873) baseStart_4800873 baseEnd_4800873 := by
    simpa [prefixWord, tailWord_4800873, baseEnd_4800873] using wordTrace_append hprefix tailTrace_4800873
  have hstable : (prefixWord ++ tailWord_4800873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800873).length < 2 ^ (prefixWord ++ tailWord_4800873).sum := by decide
  have hdescent : baseEnd_4800873 < baseStart_4800873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800876 : List Nat := [2, 2, 1, 1, 6, 1, 1, 9]
def baseStart_4800876 : Nat := 118140960795 + 4800876 * 2 ^ 59
def prefixEnd_4800876 : Nat := 4983230072969 + 3 ^ 40 * 4800876 * 2
def baseEnd_4800876 : Nat := 91302109282765325343377

theorem tailTrace_4800876 : CollatzResearch.WordTrace tailWord_4800876 prefixEnd_4800876 91302109282765325343377 := by
  unfold tailWord_4800876
  simp only [CollatzResearch.WordTrace]
  refine ⟨87551166477626825594199241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116734888636835767458932321 87551166477626825594199241)
  ·
    refine ⟨65663374858220119195649431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87551166477626825594199241 65663374858220119195649431)
    ·
      refine ⟨98495062287330178793474147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65663374858220119195649431 98495062287330178793474147)
      ·
        refine ⟨147742593430995268190211221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98495062287330178793474147 147742593430995268190211221)
        ·
          refine ⟨6925434067077903196416151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 147742593430995268190211221 6925434067077903196416151)
          ·
            refine ⟨10388151100616854794624227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6925434067077903196416151 10388151100616854794624227)
            ·
              refine ⟨15582226650925282191936341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10388151100616854794624227 15582226650925282191936341)
              ·
                refine ⟨91302109282765325343377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15582226650925282191936341 91302109282765325343377)
                ·
                  rfl

theorem cell23_4800876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 9].length) (baseStart_4800876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800876 prefixEnd_4800876 := by exact prefixLift 4800876
  have htrace : WordTrace (prefixWord ++ tailWord_4800876) baseStart_4800876 baseEnd_4800876 := by
    simpa [prefixWord, tailWord_4800876, baseEnd_4800876] using wordTrace_append hprefix tailTrace_4800876
  have hstable : (prefixWord ++ tailWord_4800876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800876).length < 2 ^ (prefixWord ++ tailWord_4800876).sum := by decide
  have hdescent : baseEnd_4800876 < baseStart_4800876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800889 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 1, 9]
def baseStart_4800889 : Nat := 118140960795 + 4800889 * 2 ^ 59
def prefixEnd_4800889 : Nat := 4983230072969 + 3 ^ 40 * 4800889 * 2
def baseEnd_4800889 : Nat := 821721208627724077802873

theorem tailTrace_4800889 : CollatzResearch.WordTrace tailWord_4800889 prefixEnd_4800889 821721208627724077802873 := by
  unfold tailWord_4800889
  simp only [CollatzResearch.WordTrace]
  refine ⟨175102807104206554408621721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116735204736137702939081147 175102807104206554408621721)
  ·
    refine ⟨131327105328154915806466291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175102807104206554408621721 131327105328154915806466291)
    ·
      refine ⟨196990657992232373709699437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131327105328154915806466291 196990657992232373709699437)
      ·
        refine ⟨73871496747087140141137289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196990657992232373709699437 73871496747087140141137289)
        ·
          refine ⟨55403622560315355105852967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73871496747087140141137289 55403622560315355105852967)
          ·
            refine ⟨83105433840473032658779451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55403622560315355105852967 83105433840473032658779451)
            ·
              refine ⟨124658150760709548988169177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83105433840473032658779451 124658150760709548988169177)
              ·
                refine ⟨93493613070532161741126883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124658150760709548988169177 93493613070532161741126883)
                ·
                  refine ⟨140240419605798242611690325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93493613070532161741126883 140240419605798242611690325)
                  ·
                    refine ⟨821721208627724077802873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 140240419605798242611690325 821721208627724077802873)
                    ·
                      rfl

theorem cell23_4800889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_4800889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800889 prefixEnd_4800889 := by exact prefixLift 4800889
  have htrace : WordTrace (prefixWord ++ tailWord_4800889) baseStart_4800889 baseEnd_4800889 := by
    simpa [prefixWord, tailWord_4800889, baseEnd_4800889] using wordTrace_append hprefix tailTrace_4800889
  have hstable : (prefixWord ++ tailWord_4800889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800889).length < 2 ^ (prefixWord ++ tailWord_4800889).sum := by decide
  have hdescent : baseEnd_4800889 < baseStart_4800889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800903 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_4800903 : Nat := 118140960795 + 4800903 * 2 ^ 59
def prefixEnd_4800903 : Nat := 4983230072969 + 3 ^ 40 * 4800903 * 2
def baseEnd_4800903 : Nat := 2465170814612335178633555

theorem tailTrace_4800903 : CollatzResearch.WordTrace tailWord_4800903 prefixEnd_4800903 2465170814612335178633555 := by
  unfold tailWord_4800903
  simp only [CollatzResearch.WordTrace]
  refine ⟨175103317726155834799631363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116735545150770556533087575 175103317726155834799631363)
  ·
    refine ⟨262654976589233752199447045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175103317726155834799631363 262654976589233752199447045)
    ·
      refine ⟨49247808110481328537396321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262654976589233752199447045 49247808110481328537396321)
      ·
        refine ⟨36935856082860996403047241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49247808110481328537396321 36935856082860996403047241)
        ·
          refine ⟨27701892062145747302285431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36935856082860996403047241 27701892062145747302285431)
          ·
            refine ⟨41552838093218620953428147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27701892062145747302285431 41552838093218620953428147)
            ·
              refine ⟨62329257139827931430142221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41552838093218620953428147 62329257139827931430142221)
              ·
                refine ⟨23373471427435474286303333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62329257139827931430142221 23373471427435474286303333)
                ·
                  refine ⟨4382525892644151428681875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23373471427435474286303333 4382525892644151428681875)
                  ·
                    refine ⟨6573788838966227143022813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4382525892644151428681875 6573788838966227143022813)
                    ·
                      refine ⟨2465170814612335178633555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6573788838966227143022813 2465170814612335178633555)
                      ·
                        rfl

theorem cell23_4800903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_4800903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800903 prefixEnd_4800903 := by exact prefixLift 4800903
  have htrace : WordTrace (prefixWord ++ tailWord_4800903) baseStart_4800903 baseEnd_4800903 := by
    simpa [prefixWord, tailWord_4800903, baseEnd_4800903] using wordTrace_append hprefix tailTrace_4800903
  have hstable : (prefixWord ++ tailWord_4800903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800903).length < 2 ^ (prefixWord ++ tailWord_4800903).sum := by decide
  have hdescent : baseEnd_4800903 < baseStart_4800903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800904 : List Nat := [2, 1, 3, 3, 1, 1, 5, 2, 1, 2, 2]
def baseStart_4800904 : Nat := 118140960795 + 4800904 * 2 ^ 59
def prefixEnd_4800904 : Nat := 4983230072969 + 3 ^ 40 * 4800904 * 2
def baseEnd_4800904 : Nat := 2465171328092989674721051

theorem tailTrace_4800904 : CollatzResearch.WordTrace tailWord_4800904 prefixEnd_4800904 2465171328092989674721051 := by
  unfold tailWord_4800904
  simp only [CollatzResearch.WordTrace]
  refine ⟨87551677099576105985208883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116735569466101474646945177 87551677099576105985208883)
  ·
    refine ⟨131327515649364158977813325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87551677099576105985208883 131327515649364158977813325)
    ·
      refine ⟨49247818368511559616679997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131327515649364158977813325 49247818368511559616679997)
      ·
        refine ⟨18467931888191834856254999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49247818368511559616679997 18467931888191834856254999)
        ·
          refine ⟨27701897832287752284382499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18467931888191834856254999 27701897832287752284382499)
          ·
            refine ⟨41552846748431628426573749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27701897832287752284382499 41552846748431628426573749)
            ·
              refine ⟨3895579382665465164991289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41552846748431628426573749 3895579382665465164991289)
              ·
                refine ⟨2921684536999098873743467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3895579382665465164991289 2921684536999098873743467)
                ·
                  refine ⟨4382526805498648310615201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921684536999098873743467 4382526805498648310615201)
                  ·
                    refine ⟨3286895104123986232961401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4382526805498648310615201 3286895104123986232961401)
                    ·
                      refine ⟨2465171328092989674721051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286895104123986232961401 2465171328092989674721051)
                      ·
                        rfl

theorem cell23_4800904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_4800904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800904 prefixEnd_4800904 := by exact prefixLift 4800904
  have htrace : WordTrace (prefixWord ++ tailWord_4800904) baseStart_4800904 baseEnd_4800904 := by
    simpa [prefixWord, tailWord_4800904, baseEnd_4800904] using wordTrace_append hprefix tailTrace_4800904
  have hstable : (prefixWord ++ tailWord_4800904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800904).length < 2 ^ (prefixWord ++ tailWord_4800904).sum := by decide
  have hdescent : baseEnd_4800904 < baseStart_4800904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800930 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_4800930 : Nat := 118140960795 + 4800930 * 2 ^ 59
def prefixEnd_4800930 : Nat := 4983230072969 + 3 ^ 40 * 4800930 * 2
def baseEnd_4800930 : Nat := 2465184678590006572995931

theorem tailTrace_4800930 : CollatzResearch.WordTrace tailWord_4800930 prefixEnd_4800930 2465184678590006572995931 := by
  unfold tailWord_4800930
  simp only [CollatzResearch.WordTrace]
  refine ⟨43776075624264504602716061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116736201664705345607242829 43776075624264504602716061)
  ·
    refine ⟨16416028359099189226018523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43776075624264504602716061 16416028359099189226018523)
    ·
      refine ⟨24624042538648783839027785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16416028359099189226018523 24624042538648783839027785)
      ·
        refine ⟨18468031903986587879270839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24624042538648783839027785 18468031903986587879270839)
        ·
          refine ⟨27702047855979881818906259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18468031903986587879270839 27702047855979881818906259)
          ·
            refine ⟨41553071783969822728359389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27702047855979881818906259 41553071783969822728359389)
            ·
              refine ⟨15582401918988683523134771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41553071783969822728359389 15582401918988683523134771)
              ·
                refine ⟨23373602878483025284702157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15582401918988683523134771 23373602878483025284702157)
                ·
                  refine ⟨8765101079431134481763309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23373602878483025284702157 8765101079431134481763309)
                  ·
                    refine ⟨3286912904786675430661241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8765101079431134481763309 3286912904786675430661241)
                    ·
                      refine ⟨2465184678590006572995931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286912904786675430661241 2465184678590006572995931)
                      ·
                        rfl

theorem cell23_4800930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_4800930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800930 prefixEnd_4800930 := by exact prefixLift 4800930
  have htrace : WordTrace (prefixWord ++ tailWord_4800930) baseStart_4800930 baseEnd_4800930 := by
    simpa [prefixWord, tailWord_4800930, baseEnd_4800930] using wordTrace_append hprefix tailTrace_4800930
  have hstable : (prefixWord ++ tailWord_4800930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800930).length < 2 ^ (prefixWord ++ tailWord_4800930).sum := by decide
  have hdescent : baseEnd_4800930 < baseStart_4800930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800939 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 10]
def baseStart_4800939 : Nat := 118140960795 + 4800939 * 2 ^ 59
def prefixEnd_4800939 : Nat := 4983230072969 + 3 ^ 40 * 4800939 * 2
def baseEnd_4800939 : Nat := 2465189299915897037783389

theorem tailTrace_4800939 : CollatzResearch.WordTrace tailWord_4800939 prefixEnd_4800939 2465189299915897037783389 := by
  unfold tailWord_4800939
  simp only [CollatzResearch.WordTrace]
  refine ⟨175104630754025412947941871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116736420502683608631961247 175104630754025412947941871)
  ·
    refine ⟨262656946131038119421912807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175104630754025412947941871 262656946131038119421912807)
    ·
      refine ⟨393985419196557179132869211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262656946131038119421912807 393985419196557179132869211)
      ·
        refine ⟨590978128794835768699303817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393985419196557179132869211 590978128794835768699303817)
        ·
          refine ⟨443233596596126826524477863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 590978128794835768699303817 443233596596126826524477863)
          ·
            refine ⟨664850394894190239786716795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443233596596126826524477863 664850394894190239786716795)
            ·
              refine ⟨997275592341285359680075193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664850394894190239786716795 997275592341285359680075193)
              ·
                refine ⟨747956694255964019760056395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997275592341285359680075193 747956694255964019760056395)
                ·
                  refine ⟨1121935041383946029640084593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747956694255964019760056395 1121935041383946029640084593)
                  ·
                    refine ⟨841451281037959522230063445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1121935041383946029640084593 841451281037959522230063445)
                    ·
                      refine ⟨2465189299915897037783389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 841451281037959522230063445 2465189299915897037783389)
                      ·
                        rfl

theorem cell23_4800939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_4800939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800939 prefixEnd_4800939 := by exact prefixLift 4800939
  have htrace : WordTrace (prefixWord ++ tailWord_4800939) baseStart_4800939 baseEnd_4800939 := by
    simpa [prefixWord, tailWord_4800939, baseEnd_4800939] using wordTrace_append hprefix tailTrace_4800939
  have hstable : (prefixWord ++ tailWord_4800939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800939).length < 2 ^ (prefixWord ++ tailWord_4800939).sum := by decide
  have hdescent : baseEnd_4800939 < baseStart_4800939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4800946 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_4800946 : Nat := 118140960795 + 4800946 * 2 ^ 59
def prefixEnd_4800946 : Nat := 4983230072969 + 3 ^ 40 * 4800946 * 2
def baseEnd_4800946 : Nat := 2465192894280478510395857

theorem tailTrace_4800946 : CollatzResearch.WordTrace tailWord_4800946 prefixEnd_4800946 2465192894280478510395857 := by
  unfold tailWord_4800946
  simp only [CollatzResearch.WordTrace]
  refine ⟨43776221516250013285861673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116736590710000035428964461 43776221516250013285861673)
  ·
    refine ⟨32832166137187509964396255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43776221516250013285861673 32832166137187509964396255)
    ·
      refine ⟨49248249205781264946594383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32832166137187509964396255 49248249205781264946594383)
      ·
        refine ⟨73872373808671897419891575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49248249205781264946594383 73872373808671897419891575)
        ·
          refine ⟨110808560713007846129837363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73872373808671897419891575 110808560713007846129837363)
          ·
            refine ⟨166212841069511769194756045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110808560713007846129837363 166212841069511769194756045)
            ·
              refine ⟨62329815401066913448033517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166212841069511769194756045 62329815401066913448033517)
              ·
                refine ⟨23373680775400092543012569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62329815401066913448033517 23373680775400092543012569)
                ·
                  refine ⟨17530260581550069407259427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23373680775400092543012569 17530260581550069407259427)
                  ·
                    refine ⟨26295390872325104110889141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17530260581550069407259427 26295390872325104110889141)
                    ·
                      refine ⟨2465192894280478510395857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26295390872325104110889141 2465192894280478510395857)
                      ·
                        rfl

theorem cell23_4800946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_4800946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4800946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4800946 prefixEnd_4800946 := by exact prefixLift 4800946
  have htrace : WordTrace (prefixWord ++ tailWord_4800946) baseStart_4800946 baseEnd_4800946 := by
    simpa [prefixWord, tailWord_4800946, baseEnd_4800946] using wordTrace_append hprefix tailTrace_4800946
  have hstable : (prefixWord ++ tailWord_4800946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4800946).length < 2 ^ (prefixWord ++ tailWord_4800946).sum := by decide
  have hdescent : baseEnd_4800946 < baseStart_4800946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4800946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801000 : List Nat := [2, 1, 4, 1, 1, 4, 2, 3, 5]
def baseStart_4801000 : Nat := 118140960795 + 4801000 * 2 ^ 59
def prefixEnd_4801000 : Nat := 4983230072969 + 3 ^ 40 * 4801000 * 2
def baseEnd_4801000 : Nat := 273913402470646811013401

theorem tailTrace_4801000 : CollatzResearch.WordTrace tailWord_4801000 prefixEnd_4801000 273913402470646811013401 := by
  unfold tailWord_4801000
  simp only [CollatzResearch.WordTrace]
  refine ⟨87553427803402210182956227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116737903737869613577274969 87553427803402210182956227)
  ·
    refine ⟨131330141705103315274434341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87553427803402210182956227 131330141705103315274434341)
    ·
      refine ⟨24624401569706871613956439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131330141705103315274434341 24624401569706871613956439)
      ·
        refine ⟨36936602354560307420934659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24624401569706871613956439 36936602354560307420934659)
        ·
          refine ⟨55404903531840461131401989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36936602354560307420934659 55404903531840461131401989)
          ·
            refine ⟨10388419412220086462137873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55404903531840461131401989 10388419412220086462137873)
            ·
              refine ⟨7791314559165064846603405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10388419412220086462137873 7791314559165064846603405)
              ·
                refine ⟨2921742959686899317476277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7791314559165064846603405 2921742959686899317476277)
                ·
                  refine ⟨273913402470646811013401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2921742959686899317476277 273913402470646811013401)
                  ·
                    rfl

theorem cell23_4801000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 5].length) (baseStart_4801000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801000 prefixEnd_4801000 := by exact prefixLift 4801000
  have htrace : WordTrace (prefixWord ++ tailWord_4801000) baseStart_4801000 baseEnd_4801000 := by
    simpa [prefixWord, tailWord_4801000, baseEnd_4801000] using wordTrace_append hprefix tailTrace_4801000
  have hstable : (prefixWord ++ tailWord_4801000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801000).length < 2 ^ (prefixWord ++ tailWord_4801000).sum := by decide
  have hdescent : baseEnd_4801000 < baseStart_4801000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801033 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 1, 6, 2]
def baseStart_4801033 : Nat := 118140960795 + 4801033 * 2 ^ 59
def prefixEnd_4801033 : Nat := 4983230072969 + 3 ^ 40 * 4801033 * 2
def baseEnd_4801033 : Nat := 2465237567097419670007957

theorem tailTrace_4801033 : CollatzResearch.WordTrace tailWord_4801033 prefixEnd_4801033 2465237567097419670007957 := by
  unfold tailWord_4801033
  simp only [CollatzResearch.WordTrace]
  refine ⟨175108059215684867001863753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116738706143789911334575835 175108059215684867001863753)
  ·
    refine ⟨131331044411763650251397815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175108059215684867001863753 131331044411763650251397815)
    ·
      refine ⟨196996566617645475377096723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131331044411763650251397815 196996566617645475377096723)
      ·
        refine ⟨295494849926468213065645085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196996566617645475377096723 295494849926468213065645085)
        ·
          refine ⟨110810568722425579899616907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295494849926468213065645085 110810568722425579899616907)
          ·
            refine ⟨166215853083638369849425361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110810568722425579899616907 166215853083638369849425361)
            ·
              refine ⟨124661889812728777387069021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166215853083638369849425361 124661889812728777387069021)
              ·
                refine ⟨46748208679773291520150883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124661889812728777387069021 46748208679773291520150883)
                ·
                  refine ⟨70122313019659937280226325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46748208679773291520150883 70122313019659937280226325)
                  ·
                    refine ⟨3286983422796559560010609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70122313019659937280226325 3286983422796559560010609)
                    ·
                      refine ⟨2465237567097419670007957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3286983422796559560010609 2465237567097419670007957)
                      ·
                        rfl

theorem cell23_4801033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 6, 2].length) (baseStart_4801033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801033 prefixEnd_4801033 := by exact prefixLift 4801033
  have htrace : WordTrace (prefixWord ++ tailWord_4801033) baseStart_4801033 baseEnd_4801033 := by
    simpa [prefixWord, tailWord_4801033, baseEnd_4801033] using wordTrace_append hprefix tailTrace_4801033
  have hstable : (prefixWord ++ tailWord_4801033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801033).length < 2 ^ (prefixWord ++ tailWord_4801033).sum := by decide
  have hdescent : baseEnd_4801033 < baseStart_4801033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801043 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 3, 4]
def baseStart_4801043 : Nat := 118140960795 + 4801043 * 2 ^ 59
def prefixEnd_4801043 : Nat := 4983230072969 + 3 ^ 40 * 4801043 * 2
def baseEnd_4801043 : Nat := 821747567301321543627637

theorem tailTrace_4801043 : CollatzResearch.WordTrace tailWord_4801043 prefixEnd_4801043 821747567301321543627637 := by
  unfold tailWord_4801043
  simp only [CollatzResearch.WordTrace]
  refine ⟨175108423945648638709727783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116738949297099092473151855 175108423945648638709727783)
  ·
    refine ⟨262662635918472958064591675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175108423945648638709727783 262662635918472958064591675)
    ·
      refine ⟨393993953877709437096887513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262662635918472958064591675 393993953877709437096887513)
      ·
        refine ⟨295495465408282077822665635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393993953877709437096887513 295495465408282077822665635)
        ·
          refine ⟨443243198112423116733998453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295495465408282077822665635 443243198112423116733998453)
          ·
            refine ⟨41554049823039667193812355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 443243198112423116733998453 41554049823039667193812355)
            ·
              refine ⟨62331074734559500790718533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41554049823039667193812355 62331074734559500790718533)
              ·
                refine ⟨11687076512729906398259725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62331074734559500790718533 11687076512729906398259725)
                ·
                  refine ⟨4382653692273714899347397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11687076512729906398259725 4382653692273714899347397)
                  ·
                    refine ⟨821747567301321543627637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382653692273714899347397 821747567301321543627637)
                    ·
                      rfl

theorem cell23_4801043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 4].length) (baseStart_4801043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801043 prefixEnd_4801043 := by exact prefixLift 4801043
  have htrace : WordTrace (prefixWord ++ tailWord_4801043) baseStart_4801043 baseEnd_4801043 := by
    simpa [prefixWord, tailWord_4801043, baseEnd_4801043] using wordTrace_append hprefix tailTrace_4801043
  have hstable : (prefixWord ++ tailWord_4801043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801043).length < 2 ^ (prefixWord ++ tailWord_4801043).sum := by decide
  have hdescent : baseEnd_4801043 < baseStart_4801043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801100 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 5, 1, 3]
def baseStart_4801100 : Nat := 118140960795 + 4801100 * 2 ^ 59
def prefixEnd_4801100 : Nat := 4983230072969 + 3 ^ 40 * 4801100 * 2
def baseEnd_4801100 : Nat := 2465271970301270907870149

theorem tailTrace_4801100 : CollatzResearch.WordTrace tailWord_4801100 prefixEnd_4801100 2465271970301270907870149 := by
  unfold tailWord_4801100
  simp only [CollatzResearch.WordTrace]
  refine ⟨87555251453221068722276377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116740335270961424963035169 87555251453221068722276377)
  ·
    refine ⟨65666438589915801541707283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87555251453221068722276377 65666438589915801541707283)
    ·
      refine ⟨98499657884873702312560925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65666438589915801541707283 98499657884873702312560925)
      ·
        refine ⟨36937371706827638367210347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98499657884873702312560925 36937371706827638367210347)
        ·
          refine ⟨55406057560241457550815521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36937371706827638367210347 55406057560241457550815521)
          ·
            refine ⟨41554543170181093163111641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55406057560241457550815521 41554543170181093163111641)
            ·
              refine ⟨31165907377635819872333731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41554543170181093163111641 31165907377635819872333731)
              ·
                refine ⟨46748861066453729808500597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31165907377635819872333731 46748861066453729808500597)
                ·
                  refine ⟨4382705724980037169546931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46748861066453729808500597 4382705724980037169546931)
                  ·
                    refine ⟨6574058587470055754320397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4382705724980037169546931 6574058587470055754320397)
                    ·
                      refine ⟨2465271970301270907870149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6574058587470055754320397 2465271970301270907870149)
                      ·
                        rfl

theorem cell23_4801100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_4801100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801100 prefixEnd_4801100 := by exact prefixLift 4801100
  have htrace : WordTrace (prefixWord ++ tailWord_4801100) baseStart_4801100 baseEnd_4801100 := by
    simpa [prefixWord, tailWord_4801100, baseEnd_4801100] using wordTrace_append hprefix tailTrace_4801100
  have hstable : (prefixWord ++ tailWord_4801100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801100).length < 2 ^ (prefixWord ++ tailWord_4801100).sum := by decide
  have hdescent : baseEnd_4801100 < baseStart_4801100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801128 : List Nat := [2, 1, 4, 3, 3, 1, 2, 2, 1, 4]
def baseStart_4801128 : Nat := 118140960795 + 4801128 * 2 ^ 59
def prefixEnd_4801128 : Nat := 4983230072969 + 3 ^ 40 * 4801128 * 2
def baseEnd_4801128 : Nat := 821762115919865599440007

theorem tailTrace_4801128 : CollatzResearch.WordTrace tailWord_4801128 prefixEnd_4801128 821762115919865599440007 := by
  unfold tailWord_4801128
  simp only [CollatzResearch.WordTrace]
  refine ⟨87555762075170349113286019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116741016100227132151048025 87555762075170349113286019)
  ·
    refine ⟨131333643112755523669929029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87555762075170349113286019 131333643112755523669929029)
    ·
      refine ⟨24625058083641660688111693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131333643112755523669929029 24625058083641660688111693)
      ·
        refine ⟨9234396781365622758041885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24625058083641660688111693 9234396781365622758041885)
        ·
          refine ⟨3462898793012108534265707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9234396781365622758041885 3462898793012108534265707)
          ·
            refine ⟨5194348189518162801398561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3462898793012108534265707 5194348189518162801398561)
            ·
              refine ⟨3895761142138622101048921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5194348189518162801398561 3895761142138622101048921)
              ·
                refine ⟨2921820856603966575786691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3895761142138622101048921 2921820856603966575786691)
                ·
                  refine ⟨4382731284905949863680037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921820856603966575786691 4382731284905949863680037)
                  ·
                    refine ⟨821762115919865599440007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382731284905949863680037 821762115919865599440007)
                    ·
                      rfl

theorem cell23_4801128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_4801128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801128 prefixEnd_4801128 := by exact prefixLift 4801128
  have htrace : WordTrace (prefixWord ++ tailWord_4801128) baseStart_4801128 baseEnd_4801128 := by
    simpa [prefixWord, tailWord_4801128, baseEnd_4801128] using wordTrace_append hprefix tailTrace_4801128
  have hstable : (prefixWord ++ tailWord_4801128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801128).length < 2 ^ (prefixWord ++ tailWord_4801128).sum := by decide
  have hdescent : baseEnd_4801128 < baseStart_4801128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801143 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_4801143 : Nat := 118140960795 + 4801143 * 2 ^ 59
def prefixEnd_4801143 : Nat := 4983230072969 + 3 ^ 40 * 4801143 * 2
def baseEnd_4801143 : Nat := 2465294049969414239632451

theorem tailTrace_4801143 : CollatzResearch.WordTrace tailWord_4801143 prefixEnd_4801143 2465294049969414239632451 := by
  unfold tailWord_4801143
  simp only [CollatzResearch.WordTrace]
  refine ⟨175112071245286355788368083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116741380830190903858912055 175112071245286355788368083)
  ·
    refine ⟨262668106867929533682552125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175112071245286355788368083 262668106867929533682552125)
    ·
      refine ⟨98500540075473575130957047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262668106867929533682552125 98500540075473575130957047)
      ·
        refine ⟨147750810113210362696435571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98500540075473575130957047 147750810113210362696435571)
        ·
          refine ⟨221626215169815544044653357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147750810113210362696435571 221626215169815544044653357)
          ·
            refine ⟨83109830688680829016745009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221626215169815544044653357 83109830688680829016745009)
            ·
              refine ⟨62332373016510621762558757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83109830688680829016745009 62332373016510621762558757)
              ·
                refine ⟨11687319940595741580479767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62332373016510621762558757 11687319940595741580479767)
                ·
                  refine ⟨17530979910893612370719651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11687319940595741580479767 17530979910893612370719651)
                  ·
                    refine ⟨26296469866340418556079477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17530979910893612370719651 26296469866340418556079477)
                    ·
                      refine ⟨2465294049969414239632451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26296469866340418556079477 2465294049969414239632451)
                      ·
                        rfl

theorem cell23_4801143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_4801143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801143 prefixEnd_4801143 := by exact prefixLift 4801143
  have htrace : WordTrace (prefixWord ++ tailWord_4801143) baseStart_4801143 baseEnd_4801143 := by
    simpa [prefixWord, tailWord_4801143, baseEnd_4801143] using wordTrace_append hprefix tailTrace_4801143
  have hstable : (prefixWord ++ tailWord_4801143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801143).length < 2 ^ (prefixWord ++ tailWord_4801143).sum := by decide
  have hdescent : baseEnd_4801143 < baseStart_4801143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801157 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 5, 2, 2]
def baseStart_4801157 : Nat := 118140960795 + 4801157 * 2 ^ 59
def prefixEnd_4801157 : Nat := 4983230072969 + 3 ^ 40 * 4801157 * 2
def baseEnd_4801157 : Nat := 2465301238698577184857387

theorem tailTrace_4801157 : CollatzResearch.WordTrace tailWord_4801157 prefixEnd_4801157 2465301238698577184857387 := by
  unfold tailWord_4801157
  simp only [CollatzResearch.WordTrace]
  refine ⟨175112581867235636179377725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116741721244823757452918483 175112581867235636179377725)
  ·
    refine ⟨65667218200213363567266647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175112581867235636179377725 65667218200213363567266647)
    ·
      refine ⟨98500827300320045350899971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65667218200213363567266647 98500827300320045350899971)
      ·
        refine ⟨147751240950480068026349957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98500827300320045350899971 147751240950480068026349957)
        ·
          refine ⟨27703357678215012754940617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147751240950480068026349957 27703357678215012754940617)
          ·
            refine ⟨20777518258661259566205463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27703357678215012754940617 20777518258661259566205463)
            ·
              refine ⟨31166277387991889349308195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20777518258661259566205463 31166277387991889349308195)
              ·
                refine ⟨46749416081987834023962293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31166277387991889349308195 46749416081987834023962293)
                ·
                  refine ⟨4382757757686359439746465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46749416081987834023962293 4382757757686359439746465)
                  ·
                    refine ⟨3287068318264769579809849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4382757757686359439746465 3287068318264769579809849)
                    ·
                      refine ⟨2465301238698577184857387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3287068318264769579809849 2465301238698577184857387)
                      ·
                        rfl

theorem cell23_4801157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 2, 2].length) (baseStart_4801157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801157 prefixEnd_4801157 := by exact prefixLift 4801157
  have htrace : WordTrace (prefixWord ++ tailWord_4801157) baseStart_4801157 baseEnd_4801157 := by
    simpa [prefixWord, tailWord_4801157, baseEnd_4801157] using wordTrace_append hprefix tailTrace_4801157
  have hstable : (prefixWord ++ tailWord_4801157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801157).length < 2 ^ (prefixWord ++ tailWord_4801157).sum := by decide
  have hdescent : baseEnd_4801157 < baseStart_4801157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801184 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 2, 4]
def baseStart_4801184 : Nat := 118140960795 + 4801184 * 2 ^ 59
def prefixEnd_4801184 : Nat := 4983230072969 + 3 ^ 40 * 4801184 * 2
def baseEnd_4801184 : Nat := 821771700892082859739921

theorem tailTrace_4801184 : CollatzResearch.WordTrace tailWord_4801184 prefixEnd_4801184 821771700892082859739921 := by
  unfold tailWord_4801184
  simp only [CollatzResearch.WordTrace]
  refine ⟨87556783319068909895305303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116742377758758546527073737 87556783319068909895305303)
  ·
    refine ⟨131335174978603364842957955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87556783319068909895305303 131335174978603364842957955)
    ·
      refine ⟨197002762467905047264436933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131335174978603364842957955 197002762467905047264436933)
      ·
        refine ⟨36938017962732196362081925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197002762467905047264436933 36938017962732196362081925)
        ·
          refine ⟨6925878368012286817890361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36938017962732196362081925 6925878368012286817890361)
          ·
            refine ⟨5194408776009215113417771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6925878368012286817890361 5194408776009215113417771)
            ·
              refine ⟨7791613164013822670126657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5194408776009215113417771 7791613164013822670126657)
              ·
                refine ⟨5843709873010367002594993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7791613164013822670126657 5843709873010367002594993)
                ·
                  refine ⟨4382782404757775251946245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5843709873010367002594993 4382782404757775251946245)
                  ·
                    refine ⟨821771700892082859739921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382782404757775251946245 821771700892082859739921)
                    ·
                      rfl

theorem cell23_4801184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2, 4].length) (baseStart_4801184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801184 prefixEnd_4801184 := by exact prefixLift 4801184
  have htrace : WordTrace (prefixWord ++ tailWord_4801184) baseStart_4801184 baseEnd_4801184 := by
    simpa [prefixWord, tailWord_4801184, baseEnd_4801184] using wordTrace_append hprefix tailTrace_4801184
  have hstable : (prefixWord ++ tailWord_4801184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801184).length < 2 ^ (prefixWord ++ tailWord_4801184).sum := by decide
  have hdescent : baseEnd_4801184 < baseStart_4801184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801194 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4801194 : Nat := 118140960795 + 4801194 * 2 ^ 59
def prefixEnd_4801194 : Nat := 4983230072969 + 3 ^ 40 * 4801194 * 2
def baseEnd_4801194 : Nat := 2465320237482793540094717

theorem tailTrace_4801194 : CollatzResearch.WordTrace tailWord_4801194 prefixEnd_4801194 2465320237482793540094717 := by
  unfold tailWord_4801194
  simp only [CollatzResearch.WordTrace]
  refine ⟨43778482842025397874618659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116742620912067727665649757 43778482842025397874618659)
  ·
    refine ⟨65667724263038096811927989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43778482842025397874618659 65667724263038096811927989)
    ·
      refine ⟨6156349149659821576118249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65667724263038096811927989 6156349149659821576118249)
      ·
        refine ⟨4617261862244866182088687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6156349149659821576118249 4617261862244866182088687)
        ·
          refine ⟨6925892793367299273133031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4617261862244866182088687 6925892793367299273133031)
          ·
            refine ⟨10388839190050948909699547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6925892793367299273133031 10388839190050948909699547)
            ·
              refine ⟨15583258785076423364549321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10388839190050948909699547 15583258785076423364549321)
              ·
                refine ⟨11687444088807317523411991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15583258785076423364549321 11687444088807317523411991)
                ·
                  refine ⟨17531166133210976285117987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11687444088807317523411991 17531166133210976285117987)
                  ·
                    refine ⟨26296749199816464427676981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17531166133210976285117987 26296749199816464427676981)
                    ·
                      refine ⟨2465320237482793540094717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26296749199816464427676981 2465320237482793540094717)
                      ·
                        rfl

theorem cell23_4801194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4801194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801194 prefixEnd_4801194 := by exact prefixLift 4801194
  have htrace : WordTrace (prefixWord ++ tailWord_4801194) baseStart_4801194 baseEnd_4801194 := by
    simpa [prefixWord, tailWord_4801194, baseEnd_4801194] using wordTrace_append hprefix tailTrace_4801194
  have hstable : (prefixWord ++ tailWord_4801194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801194).length < 2 ^ (prefixWord ++ tailWord_4801194).sum := by decide
  have hdescent : baseEnd_4801194 < baseStart_4801194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801201 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 2, 4]
def baseStart_4801201 : Nat := 118140960795 + 4801201 * 2 ^ 59
def prefixEnd_4801201 : Nat := 4983230072969 + 3 ^ 40 * 4801201 * 2
def baseEnd_4801201 : Nat := 821774610615791670902395

theorem tailTrace_4801201 : CollatzResearch.WordTrace tailWord_4801201 prefixEnd_4801201 821774610615791670902395 := by
  unfold tailWord_4801201
  simp only [CollatzResearch.WordTrace]
  refine ⟨175114186679076231693979457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116742791119384154462652971 175114186679076231693979457)
  ·
    refine ⟨131335640009307173770484593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175114186679076231693979457 131335640009307173770484593)
    ·
      refine ⟨98501730006980380327863445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131335640009307173770484593 98501730006980380327863445)
      ·
        refine ⟨4617268594077205327868599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98501730006980380327863445 4617268594077205327868599)
        ·
          refine ⟨6925902891115807991802899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4617268594077205327868599 6925902891115807991802899)
          ·
            refine ⟨10388854336673711987704349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6925902891115807991802899 10388854336673711987704349)
            ·
              refine ⟨3895820376252641995389131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10388854336673711987704349 3895820376252641995389131)
              ·
                refine ⟨5843730564378962993083697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3895820376252641995389131 5843730564378962993083697)
                ·
                  refine ⟨4382797923284222244812773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5843730564378962993083697 4382797923284222244812773)
                  ·
                    refine ⟨821774610615791670902395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382797923284222244812773 821774610615791670902395)
                    ·
                      rfl

theorem cell23_4801201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_4801201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801201 prefixEnd_4801201 := by exact prefixLift 4801201
  have htrace : WordTrace (prefixWord ++ tailWord_4801201) baseStart_4801201 baseEnd_4801201 := by
    simpa [prefixWord, tailWord_4801201, baseEnd_4801201] using wordTrace_append hprefix tailTrace_4801201
  have hstable : (prefixWord ++ tailWord_4801201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801201).length < 2 ^ (prefixWord ++ tailWord_4801201).sum := by decide
  have hdescent : baseEnd_4801201 < baseStart_4801201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801220 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_4801220 : Nat := 118140960795 + 4801220 * 2 ^ 59
def prefixEnd_4801220 : Nat := 4983230072969 + 3 ^ 40 * 4801220 * 2
def baseEnd_4801220 : Nat := 2465333587979810438369597

theorem tailTrace_4801220 : CollatzResearch.WordTrace tailWord_4801220 prefixEnd_4801220 2465333587979810438369597 := by
  unfold tailWord_4801220
  simp only [CollatzResearch.WordTrace]
  refine ⟨87557439833003698969460557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116743253110671598625947409 87557439833003698969460557)
  ·
    refine ⟨32834039937376387113547709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87557439833003698969460557 32834039937376387113547709)
    ·
      refine ⟨12312764976516145167580391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32834039937376387113547709 12312764976516145167580391)
      ·
        refine ⟨18469147464774217751370587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12312764976516145167580391 18469147464774217751370587)
        ·
          refine ⟨27703721197161326627055881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18469147464774217751370587 27703721197161326627055881)
          ·
            refine ⟨20777790897870994970291911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27703721197161326627055881 20777790897870994970291911)
            ·
              refine ⟨31166686346806492455437867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20777790897870994970291911 31166686346806492455437867)
              ·
                refine ⟨46750029520209738683156801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31166686346806492455437867 46750029520209738683156801)
                ·
                  refine ⟨35062522140157304012367601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46750029520209738683156801 35062522140157304012367601)
                  ·
                    refine ⟨26296891605117978009275701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35062522140157304012367601 26296891605117978009275701)
                    ·
                      refine ⟨2465333587979810438369597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26296891605117978009275701 2465333587979810438369597)
                      ·
                        rfl

theorem cell23_4801220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_4801220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801220 prefixEnd_4801220 := by exact prefixLift 4801220
  have htrace : WordTrace (prefixWord ++ tailWord_4801220) baseStart_4801220 baseEnd_4801220 := by
    simpa [prefixWord, tailWord_4801220, baseEnd_4801220] using wordTrace_append hprefix tailTrace_4801220
  have hstable : (prefixWord ++ tailWord_4801220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801220).length < 2 ^ (prefixWord ++ tailWord_4801220).sum := by decide
  have hdescent : baseEnd_4801220 < baseStart_4801220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801223 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 4, 6]
def baseStart_4801223 : Nat := 118140960795 + 4801223 * 2 ^ 59
def prefixEnd_4801223 : Nat := 4983230072969 + 3 ^ 40 * 4801223 * 2
def baseEnd_4801223 : Nat := 821778376140591308877361

theorem tailTrace_4801223 : CollatzResearch.WordTrace tailWord_4801223 prefixEnd_4801223 821778376140591308877361 := by
  unfold tailWord_4801223
  simp only [CollatzResearch.WordTrace]
  refine ⟨175114989084996529451280323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116743326056664352967520215 175114989084996529451280323)
  ·
    refine ⟨262672483627494794176920485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175114989084996529451280323 262672483627494794176920485)
    ·
      refine ⟨49251090680155273908172591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262672483627494794176920485 49251090680155273908172591)
      ·
        refine ⟨73876636020232910862258887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49251090680155273908172591 73876636020232910862258887)
        ·
          refine ⟨110814954030349366293388331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73876636020232910862258887 110814954030349366293388331)
          ·
            refine ⟨166222431045524049440082497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110814954030349366293388331 166222431045524049440082497)
            ·
              refine ⟨124666823284143037080061873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166222431045524049440082497 124666823284143037080061873)
              ·
                refine ⟨93500117463107277810046405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124666823284143037080061873 93500117463107277810046405)
                ·
                  refine ⟨17531272024332614589383701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93500117463107277810046405 17531272024332614589383701)
                  ·
                    refine ⟨821778376140591308877361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17531272024332614589383701 821778376140591308877361)
                    ·
                      rfl

theorem cell23_4801223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_4801223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801223 prefixEnd_4801223 := by exact prefixLift 4801223
  have htrace : WordTrace (prefixWord ++ tailWord_4801223) baseStart_4801223 baseEnd_4801223 := by
    simpa [prefixWord, tailWord_4801223, baseEnd_4801223] using wordTrace_append hprefix tailTrace_4801223
  have hstable : (prefixWord ++ tailWord_4801223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801223).length < 2 ^ (prefixWord ++ tailWord_4801223).sum := by decide
  have hdescent : baseEnd_4801223 < baseStart_4801223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801243 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 4]
def baseStart_4801243 : Nat := 118140960795 + 4801243 * 2 ^ 59
def prefixEnd_4801243 : Nat := 4983230072969 + 3 ^ 40 * 4801243 * 2
def baseEnd_4801243 : Nat := 2465345398034863848381991

theorem tailTrace_4801243 : CollatzResearch.WordTrace tailWord_4801243 prefixEnd_4801243 2465345398034863848381991 := by
  unfold tailWord_4801243
  simp only [CollatzResearch.WordTrace]
  refine ⟨175115718544924072867008383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116743812363282715244672255 175115718544924072867008383)
  ·
    refine ⟨262673577817386109300512575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175115718544924072867008383 262673577817386109300512575)
    ·
      refine ⟨394010366726079163950768863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262673577817386109300512575 394010366726079163950768863)
      ·
        refine ⟨591015550089118745926153295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394010366726079163950768863 591015550089118745926153295)
        ·
          refine ⟨886523325133678118889229943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591015550089118745926153295 886523325133678118889229943)
          ·
            refine ⟨1329784987700517178333844915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886523325133678118889229943 1329784987700517178333844915)
            ·
              refine ⟨1994677481550775767500767373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329784987700517178333844915 1994677481550775767500767373)
              ·
                refine ⟨748004055581540912812787765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1994677481550775767500767373 748004055581540912812787765)
                ·
                  refine ⟨70125380210769460576198853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 748004055581540912812787765 70125380210769460576198853)
                  ·
                    refine ⟨13148508789519273858037285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70125380210769460576198853 13148508789519273858037285)
                    ·
                      refine ⟨2465345398034863848381991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13148508789519273858037285 2465345398034863848381991)
                      ·
                        rfl

theorem cell23_4801243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 4].length) (baseStart_4801243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801243 prefixEnd_4801243 := by exact prefixLift 4801243
  have htrace : WordTrace (prefixWord ++ tailWord_4801243) baseStart_4801243 baseEnd_4801243 := by
    simpa [prefixWord, tailWord_4801243, baseEnd_4801243] using wordTrace_append hprefix tailTrace_4801243
  have hstable : (prefixWord ++ tailWord_4801243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801243).length < 2 ^ (prefixWord ++ tailWord_4801243).sum := by decide
  have hdescent : baseEnd_4801243 < baseStart_4801243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801264 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 2, 2, 2]
def baseStart_4801264 : Nat := 118140960795 + 4801264 * 2 ^ 59
def prefixEnd_4801264 : Nat := 4983230072969 + 3 ^ 40 * 4801264 * 2
def baseEnd_4801264 : Nat := 2465356181128608266219395

theorem tailTrace_4801264 : CollatzResearch.WordTrace tailWord_4801264 prefixEnd_4801264 2465356181128608266219395 := by
  unfold tailWord_4801264
  simp only [CollatzResearch.WordTrace]
  refine ⟨87558242238923996726761423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116744322985231995635681897 87558242238923996726761423)
  ·
    refine ⟨131337363358385995090142135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87558242238923996726761423 131337363358385995090142135)
    ·
      refine ⟨197006045037578992635213203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131337363358385995090142135 197006045037578992635213203)
      ·
        refine ⟨295509067556368488952819805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197006045037578992635213203 295509067556368488952819805)
        ·
          refine ⟨110815900333638183357307427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295509067556368488952819805 110815900333638183357307427)
          ·
            refine ⟨166223850500457275035961141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110815900333638183357307427 166223850500457275035961141)
            ·
              refine ⟨15583485984417869534621357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166223850500457275035961141 15583485984417869534621357)
              ·
                refine ⟨5843807244156701075483009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15583485984417869534621357 5843807244156701075483009)
                ·
                  refine ⟨4382855433117525806612257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5843807244156701075483009 4382855433117525806612257)
                  ·
                    refine ⟨3287141574838144354959193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4382855433117525806612257 3287141574838144354959193)
                    ·
                      refine ⟨2465356181128608266219395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3287141574838144354959193 2465356181128608266219395)
                      ·
                        rfl

theorem cell23_4801264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2, 2, 2].length) (baseStart_4801264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801264 prefixEnd_4801264 := by exact prefixLift 4801264
  have htrace : WordTrace (prefixWord ++ tailWord_4801264) baseStart_4801264 baseEnd_4801264 := by
    simpa [prefixWord, tailWord_4801264, baseEnd_4801264] using wordTrace_append hprefix tailTrace_4801264
  have hstable : (prefixWord ++ tailWord_4801264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801264).length < 2 ^ (prefixWord ++ tailWord_4801264).sum := by decide
  have hdescent : baseEnd_4801264 < baseStart_4801264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801268 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4801268 : Nat := 118140960795 + 4801268 * 2 ^ 59
def prefixEnd_4801268 : Nat := 4983230072969 + 3 ^ 40 * 4801268 * 2
def baseEnd_4801268 : Nat := 2465358235051226250569377

theorem tailTrace_4801268 : CollatzResearch.WordTrace tailWord_4801268 prefixEnd_4801268 2465358235051226250569377 := by
  unfold tailWord_4801268
  simp only [CollatzResearch.WordTrace]
  refine ⟨87558315184916751068334229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116744420246555668091112305 87558315184916751068334229)
  ·
    refine ⟨4104296024292972706328167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87558315184916751068334229 4104296024292972706328167)
    ·
      refine ⟨6156444036439459059492251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4104296024292972706328167 6156444036439459059492251)
      ·
        refine ⟨9234666054659188589238377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6156444036439459059492251 9234666054659188589238377)
        ·
          refine ⟨6925999540994391441928783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9234666054659188589238377 6925999540994391441928783)
          ·
            refine ⟨10388999311491587162893175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6925999540994391441928783 10388999311491587162893175)
            ·
              refine ⟨15583498967237380744339763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10388999311491587162893175 15583498967237380744339763)
              ·
                refine ⟨23375248450856071116509645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15583498967237380744339763 23375248450856071116509645)
                ·
                  refine ⟨8765718169071026668691117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23375248450856071116509645 8765718169071026668691117)
                  ·
                    refine ⟨3287144313401635000759169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8765718169071026668691117 3287144313401635000759169)
                    ·
                      refine ⟨2465358235051226250569377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3287144313401635000759169 2465358235051226250569377)
                      ·
                        rfl

theorem cell23_4801268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4801268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801268 prefixEnd_4801268 := by exact prefixLift 4801268
  have htrace : WordTrace (prefixWord ++ tailWord_4801268) baseStart_4801268 baseEnd_4801268 := by
    simpa [prefixWord, tailWord_4801268, baseEnd_4801268] using wordTrace_append hprefix tailTrace_4801268
  have hstable : (prefixWord ++ tailWord_4801268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801268).length < 2 ^ (prefixWord ++ tailWord_4801268).sum := by decide
  have hdescent : baseEnd_4801268 < baseStart_4801268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801270 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_4801270 : Nat := 118140960795 + 4801270 * 2 ^ 59
def prefixEnd_4801270 : Nat := 4983230072969 + 3 ^ 40 * 4801270 * 2
def baseEnd_4801270 : Nat := 273928806890281693638263

theorem tailTrace_4801270 : CollatzResearch.WordTrace tailWord_4801270 prefixEnd_4801270 273928806890281693638263 := by
  unfold tailWord_4801270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10944793957239141029890079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116744468877217504318827509 10944793957239141029890079)
  ·
    refine ⟨16417190935858711544835119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10944793957239141029890079 16417190935858711544835119)
    ·
      refine ⟨24625786403788067317252679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16417190935858711544835119 24625786403788067317252679)
      ·
        refine ⟨36938679605682100975879019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24625786403788067317252679 36938679605682100975879019)
        ·
          refine ⟨55408019408523151463818529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36938679605682100975879019 55408019408523151463818529)
          ·
            refine ⟨41556014556392363597863897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55408019408523151463818529 41556014556392363597863897)
            ·
              refine ⟨31167010917294272698397923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41556014556392363597863897 31167010917294272698397923)
              ·
                refine ⟨46750516375941409047596885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31167010917294272698397923 46750516375941409047596885)
                ·
                  refine ⟨273928806890281693638263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46750516375941409047596885 273928806890281693638263)
                  ·
                    rfl

theorem cell23_4801270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_4801270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801270 prefixEnd_4801270 := by exact prefixLift 4801270
  have htrace : WordTrace (prefixWord ++ tailWord_4801270) baseStart_4801270 baseEnd_4801270 := by
    simpa [prefixWord, tailWord_4801270, baseEnd_4801270] using wordTrace_append hprefix tailTrace_4801270
  have hstable : (prefixWord ++ tailWord_4801270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801270).length < 2 ^ (prefixWord ++ tailWord_4801270).sum := by decide
  have hdescent : baseEnd_4801270 < baseStart_4801270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801273 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_4801273 : Nat := 118140960795 + 4801273 * 2 ^ 59
def prefixEnd_4801273 : Nat := 4983230072969 + 3 ^ 40 * 4801273 * 2
def baseEnd_4801273 : Nat := 2465360802454498731006853

theorem tailTrace_4801273 : CollatzResearch.WordTrace tailWord_4801273 prefixEnd_4801273 2465360802454498731006853 := by
  unfold tailWord_4801273
  simp only [CollatzResearch.WordTrace]
  refine ⟨175116812734815387990600473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116744541823210258660400315 175116812734815387990600473)
  ·
    refine ⟨131337609551111540992950355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175116812734815387990600473 131337609551111540992950355)
    ·
      refine ⟨197006414326667311489425533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131337609551111540992950355 197006414326667311489425533)
      ·
        refine ⟨73877405372500241808534575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197006414326667311489425533 73877405372500241808534575)
        ·
          refine ⟨110816108058750362712801863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73877405372500241808534575 110816108058750362712801863)
          ·
            refine ⟨166224162088125544069202795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110816108058750362712801863 166224162088125544069202795)
            ·
              refine ⟨249336243132188316103804193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166224162088125544069202795 249336243132188316103804193)
              ·
                refine ⟨187002182349141237077853145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249336243132188316103804193 187002182349141237077853145)
                ·
                  refine ⟨140251636761855927808389859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187002182349141237077853145 140251636761855927808389859)
                  ·
                    refine ⟨210377455142783891712584789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140251636761855927808389859 210377455142783891712584789)
                    ·
                      refine ⟨2465360802454498731006853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 210377455142783891712584789 2465360802454498731006853)
                      ·
                        rfl

theorem cell23_4801273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_4801273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801273 prefixEnd_4801273 := by exact prefixLift 4801273
  have htrace : WordTrace (prefixWord ++ tailWord_4801273) baseStart_4801273 baseEnd_4801273 := by
    simpa [prefixWord, tailWord_4801273, baseEnd_4801273] using wordTrace_append hprefix tailTrace_4801273
  have hstable : (prefixWord ++ tailWord_4801273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801273).length < 2 ^ (prefixWord ++ tailWord_4801273).sum := by decide
  have hdescent : baseEnd_4801273 < baseStart_4801273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801334 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_4801334 : Nat := 118140960795 + 4801334 * 2 ^ 59
def prefixEnd_4801334 : Nat := 4983230072969 + 3 ^ 40 * 4801334 * 2
def baseEnd_4801334 : Nat := 821797374924807664114691

theorem tailTrace_4801334 : CollatzResearch.WordTrace tailWord_4801334 prefixEnd_4801334 821797374924807664114691 := by
  unfold tailWord_4801334
  simp only [CollatzResearch.WordTrace]
  refine ⟨10944939849224649713035691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116746025058396263605714037 10944939849224649713035691)
  ·
    refine ⟨16417409773836974569553537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10944939849224649713035691 16417409773836974569553537)
    ·
      refine ⟨12313057330377730927165153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16417409773836974569553537 12313057330377730927165153)
      ·
        refine ⟨9234792997783298195373865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12313057330377730927165153 9234792997783298195373865)
        ·
          refine ⟨6926094748337473646530399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9234792997783298195373865 6926094748337473646530399)
          ·
            refine ⟨10389142122506210469795599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6926094748337473646530399 10389142122506210469795599)
            ·
              refine ⟨15583713183759315704693399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10389142122506210469795599 15583713183759315704693399)
              ·
                refine ⟨23375569775638973557040099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15583713183759315704693399 23375569775638973557040099)
                ·
                  refine ⟨35063354663458460335560149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23375569775638973557040099 35063354663458460335560149)
                  ·
                    refine ⟨821797374924807664114691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35063354663458460335560149 821797374924807664114691)
                    ·
                      rfl

theorem cell23_4801334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_4801334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801334 prefixEnd_4801334 := by exact prefixLift 4801334
  have htrace : WordTrace (prefixWord ++ tailWord_4801334) baseStart_4801334 baseEnd_4801334 := by
    simpa [prefixWord, tailWord_4801334, baseEnd_4801334] using wordTrace_append hprefix tailTrace_4801334
  have hstable : (prefixWord ++ tailWord_4801334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801334).length < 2 ^ (prefixWord ++ tailWord_4801334).sum := by decide
  have hdescent : baseEnd_4801334 < baseStart_4801334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801398 : List Nat := [5, 1, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_4801398 : Nat := 118140960795 + 4801398 * 2 ^ 59
def prefixEnd_4801398 : Nat := 4983230072969 + 3 ^ 40 * 4801398 * 2
def baseEnd_4801398 : Nat := 821808329178770247314593

theorem tailTrace_4801398 : CollatzResearch.WordTrace tailWord_4801398 prefixEnd_4801398 821808329178770247314593 := by
  unfold tailWord_4801398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10945085741210158396181303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116747581239575022892600565 10945085741210158396181303)
  ·
    refine ⟨16417628611815237594271955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10945085741210158396181303 16417628611815237594271955)
    ·
      refine ⟨24626442917722856391407933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16417628611815237594271955 24626442917722856391407933)
      ·
        refine ⟨9234916094146071146777975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24626442917722856391407933 9234916094146071146777975)
        ·
          refine ⟨13852374141219106720166963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9234916094146071146777975 13852374141219106720166963)
          ·
            refine ⟨20778561211828660080250445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13852374141219106720166963 20778561211828660080250445)
            ·
              refine ⟨7791960454435747530093917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20778561211828660080250445 7791960454435747530093917)
              ·
                refine ⟨2921985170413405323785219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7791960454435747530093917 2921985170413405323785219)
                ·
                  refine ⟨4382977755620107985677829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921985170413405323785219 4382977755620107985677829)
                  ·
                    refine ⟨821808329178770247314593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382977755620107985677829 821808329178770247314593)
                    ·
                      rfl

theorem cell23_4801398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_4801398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801398 prefixEnd_4801398 := by exact prefixLift 4801398
  have htrace : WordTrace (prefixWord ++ tailWord_4801398) baseStart_4801398 baseEnd_4801398 := by
    simpa [prefixWord, tailWord_4801398, baseEnd_4801398] using wordTrace_append hprefix tailTrace_4801398
  have hstable : (prefixWord ++ tailWord_4801398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801398).length < 2 ^ (prefixWord ++ tailWord_4801398).sum := by decide
  have hdescent : baseEnd_4801398 < baseStart_4801398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801407 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 1, 5]
def baseStart_4801407 : Nat := 118140960795 + 4801407 * 2 ^ 59
def prefixEnd_4801407 : Nat := 4983230072969 + 3 ^ 40 * 4801407 * 2
def baseEnd_4801407 : Nat := 821809869620733735577079

theorem tailTrace_4801407 : CollatzResearch.WordTrace tailWord_4801407 prefixEnd_4801407 821809869620733735577079 := by
  unfold tailWord_4801407
  simp only [CollatzResearch.WordTrace]
  refine ⟨175121700116329928875978475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116747800077553285917318983 175121700116329928875978475)
  ·
    refine ⟨262682550174494893313967713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175121700116329928875978475 262682550174494893313967713)
    ·
      refine ⟨197011912630871169985475785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262682550174494893313967713 197011912630871169985475785)
      ·
        refine ⟨147758934473153377489106839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197011912630871169985475785 147758934473153377489106839)
        ·
          refine ⟨221638401709730066233660259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147758934473153377489106839 221638401709730066233660259)
          ·
            refine ⟨332457602564595099350490389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221638401709730066233660259 332457602564595099350490389)
            ·
              refine ⟨15583950120215395282054237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 332457602564595099350490389 15583950120215395282054237)
              ·
                refine ⟨5843981295080773230770339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15583950120215395282054237 5843981295080773230770339)
                ·
                  refine ⟨8765971942621159846155509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5843981295080773230770339 8765971942621159846155509)
                  ·
                    refine ⟨821809869620733735577079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8765971942621159846155509 821809869620733735577079)
                    ·
                      rfl

theorem cell23_4801407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 5].length) (baseStart_4801407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801407 prefixEnd_4801407 := by exact prefixLift 4801407
  have htrace : WordTrace (prefixWord ++ tailWord_4801407) baseStart_4801407 baseEnd_4801407 := by
    simpa [prefixWord, tailWord_4801407, baseEnd_4801407] using wordTrace_append hprefix tailTrace_4801407
  have hstable : (prefixWord ++ tailWord_4801407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801407).length < 2 ^ (prefixWord ++ tailWord_4801407).sum := by decide
  have hdescent : baseEnd_4801407 < baseStart_4801407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801427 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 2, 6, 2]
def baseStart_4801427 : Nat := 118140960795 + 4801427 * 2 ^ 59
def prefixEnd_4801427 : Nat := 4983230072969 + 3 ^ 40 * 4801427 * 2
def baseEnd_4801427 : Nat := 2465439878475291128481145

theorem tailTrace_4801427 : CollatzResearch.WordTrace tailWord_4801427 prefixEnd_4801427 2465439878475291128481145 := by
  unfold tailWord_4801427
  simp only [CollatzResearch.WordTrace]
  refine ⟨175122429576257472291706535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116748286384171648194471023 175122429576257472291706535)
  ·
    refine ⟨262683644364386208437559803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175122429576257472291706535 262683644364386208437559803)
    ·
      refine ⟨394025466546579312656339705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262683644364386208437559803 394025466546579312656339705)
      ·
        refine ⟨295519099909934484492254779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394025466546579312656339705 295519099909934484492254779)
        ·
          refine ⟨443278649864901726738382169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295519099909934484492254779 443278649864901726738382169)
          ·
            refine ⟨332458987398676295053786627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443278649864901726738382169 332458987398676295053786627)
            ·
              refine ⟨498688481098014442580679941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332458987398676295053786627 498688481098014442580679941)
              ·
                refine ⟨93504090205877707983877489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498688481098014442580679941 93504090205877707983877489)
                ·
                  refine ⟨70128067654408280987908117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93504090205877707983877489 70128067654408280987908117)
                  ·
                    refine ⟨3287253171300388171308193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70128067654408280987908117 3287253171300388171308193)
                    ·
                      refine ⟨2465439878475291128481145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3287253171300388171308193 2465439878475291128481145)
                      ·
                        rfl

theorem cell23_4801427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 6, 2].length) (baseStart_4801427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801427 prefixEnd_4801427 := by exact prefixLift 4801427
  have htrace : WordTrace (prefixWord ++ tailWord_4801427) baseStart_4801427 baseEnd_4801427 := by
    simpa [prefixWord, tailWord_4801427, baseEnd_4801427] using wordTrace_append hprefix tailTrace_4801427
  have hstable : (prefixWord ++ tailWord_4801427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801427).length < 2 ^ (prefixWord ++ tailWord_4801427).sum := by decide
  have hdescent : baseEnd_4801427 < baseStart_4801427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801437 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_4801437 : Nat := 118140960795 + 4801437 * 2 ^ 59
def prefixEnd_4801437 : Nat := 4983230072969 + 3 ^ 40 * 4801437 * 2
def baseEnd_4801437 : Nat := 821815004427278696452033

theorem tailTrace_4801437 : CollatzResearch.WordTrace tailWord_4801437 prefixEnd_4801437 821815004427278696452033 := by
  unfold tailWord_4801437
  simp only [CollatzResearch.WordTrace]
  refine ⟨175122794306221243999570565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116748529537480829333047043 175122794306221243999570565)
  ·
    refine ⟨32835523932416483249919481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175122794306221243999570565 32835523932416483249919481)
    ·
      refine ⟨24626642949312362437439611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32835523932416483249919481 24626642949312362437439611)
      ·
        refine ⟨36939964423968543656159417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24626642949312362437439611 36939964423968543656159417)
        ·
          refine ⟨27704973317976407742119563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36939964423968543656159417 27704973317976407742119563)
          ·
            refine ⟨41557459976964611613179345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27704973317976407742119563 41557459976964611613179345)
            ·
              refine ⟨31168094982723458709884509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41557459976964611613179345 31168094982723458709884509)
              ·
                refine ⟨11688035618521297016206691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31168094982723458709884509 11688035618521297016206691)
                ·
                  refine ⟨17532053427781945524310037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11688035618521297016206691 17532053427781945524310037)
                  ·
                    refine ⟨821815004427278696452033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17532053427781945524310037 821815004427278696452033)
                    ·
                      rfl

theorem cell23_4801437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_4801437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801437 prefixEnd_4801437 := by exact prefixLift 4801437
  have htrace : WordTrace (prefixWord ++ tailWord_4801437) baseStart_4801437 baseEnd_4801437 := by
    simpa [prefixWord, tailWord_4801437, baseEnd_4801437] using wordTrace_append hprefix tailTrace_4801437
  have hstable : (prefixWord ++ tailWord_4801437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801437).length < 2 ^ (prefixWord ++ tailWord_4801437).sum := by decide
  have hdescent : baseEnd_4801437 < baseStart_4801437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801441 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 1, 5]
def baseStart_4801441 : Nat := 118140960795 + 4801441 * 2 ^ 59
def prefixEnd_4801441 : Nat := 4983230072969 + 3 ^ 40 * 4801441 * 2
def baseEnd_4801441 : Nat := 821815689068151357902027

theorem tailTrace_4801441 : CollatzResearch.WordTrace tailWord_4801441 prefixEnd_4801441 821815689068151357902027 := by
  unfold tailWord_4801441
  simp only [CollatzResearch.WordTrace]
  refine ⟨175122940198206752682716177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116748626798804501788477451 175122940198206752682716177)
  ·
    refine ⟨131342205148655064512037133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175122940198206752682716177 131342205148655064512037133)
    ·
      refine ⟨49253326930745649192013925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131342205148655064512037133 49253326930745649192013925)
      ·
        refine ⟨9234998799514809223502611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49253326930745649192013925 9234998799514809223502611)
        ·
          refine ⟨13852498199272213835253917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9234998799514809223502611 13852498199272213835253917)
          ·
            refine ⟨5194686824727080188220219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13852498199272213835253917 5194686824727080188220219)
            ·
              refine ⟨7792030237090620282330329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5194686824727080188220219 7792030237090620282330329)
              ·
                refine ⟨5844022677817965211747747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7792030237090620282330329 5844022677817965211747747)
                ·
                  refine ⟨8766034016726947817621621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5844022677817965211747747 8766034016726947817621621)
                  ·
                    refine ⟨821815689068151357902027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8766034016726947817621621 821815689068151357902027)
                    ·
                      rfl

theorem cell23_4801441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_4801441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801441 prefixEnd_4801441 := by exact prefixLift 4801441
  have htrace : WordTrace (prefixWord ++ tailWord_4801441) baseStart_4801441 baseEnd_4801441 := by
    simpa [prefixWord, tailWord_4801441, baseEnd_4801441] using wordTrace_append hprefix tailTrace_4801441
  have hstable : (prefixWord ++ tailWord_4801441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801441).length < 2 ^ (prefixWord ++ tailWord_4801441).sum := by decide
  have hdescent : baseEnd_4801441 < baseStart_4801441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801461 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_4801461 : Nat := 118140960795 + 4801461 * 2 ^ 59
def prefixEnd_4801461 : Nat := 4983230072969 + 3 ^ 40 * 4801461 * 2
def baseEnd_4801461 : Nat := 2465457336817543995455989

theorem tailTrace_4801461 : CollatzResearch.WordTrace tailWord_4801461 prefixEnd_4801461 2465457336817543995455989 := by
  unfold tailWord_4801461
  simp only [CollatzResearch.WordTrace]
  refine ⟨175123669658134296098444237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116749113105422864065629491 175123669658134296098444237)
  ·
    refine ⟨65671376121800361036916589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175123669658134296098444237 65671376121800361036916589)
    ·
      refine ⟨24626766045675135388843721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65671376121800361036916589 24626766045675135388843721)
      ·
        refine ⟨18470074534256351541632791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24626766045675135388843721 18470074534256351541632791)
        ·
          refine ⟨27705111801384527312449187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18470074534256351541632791 27705111801384527312449187)
          ·
            refine ⟨41557667702076790968673781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27705111801384527312449187 41557667702076790968673781)
            ·
              refine ⟨3896031347069699153313167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41557667702076790968673781 3896031347069699153313167)
              ·
                refine ⟨5844047020604548729969751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3896031347069699153313167 5844047020604548729969751)
                ·
                  refine ⟨8766070530906823094954627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5844047020604548729969751 8766070530906823094954627)
                  ·
                    refine ⟨13149105796360234642431941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8766070530906823094954627 13149105796360234642431941)
                    ·
                      refine ⟨2465457336817543995455989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13149105796360234642431941 2465457336817543995455989)
                      ·
                        rfl

theorem cell23_4801461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_4801461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801461 prefixEnd_4801461 := by exact prefixLift 4801461
  have htrace : WordTrace (prefixWord ++ tailWord_4801461) baseStart_4801461 baseEnd_4801461 := by
    simpa [prefixWord, tailWord_4801461, baseEnd_4801461] using wordTrace_append hprefix tailTrace_4801461
  have hstable : (prefixWord ++ tailWord_4801461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801461).length < 2 ^ (prefixWord ++ tailWord_4801461).sum := by decide
  have hdescent : baseEnd_4801461 < baseStart_4801461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801464 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 1, 1, 5]
def baseStart_4801464 : Nat := 118140960795 + 4801464 * 2 ^ 59
def prefixEnd_4801464 : Nat := 4983230072969 + 3 ^ 40 * 4801464 * 2
def baseEnd_4801464 : Nat := 2465458877259507483718475

theorem tailTrace_4801464 : CollatzResearch.WordTrace tailWord_4801464 prefixEnd_4801464 2465458877259507483718475 := by
  unfold tailWord_4801464
  simp only [CollatzResearch.WordTrace]
  refine ⟨87561889538561713805401723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116749186051415618407202297 87561889538561713805401723)
  ·
    refine ⟨131342834307842570708102585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87561889538561713805401723 131342834307842570708102585)
    ·
      refine ⟨98507125730881928031076939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131342834307842570708102585 98507125730881928031076939)
      ·
        refine ⟨147760688596322892046615409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98507125730881928031076939 147760688596322892046615409)
        ·
          refine ⟨110820516447242169034961557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147760688596322892046615409 110820516447242169034961557)
          ·
            refine ⟨5194711708464476673513823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110820516447242169034961557 5194711708464476673513823)
            ·
              refine ⟨7792067562696715010270735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5194711708464476673513823 7792067562696715010270735)
              ·
                refine ⟨11688101344045072515406103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7792067562696715010270735 11688101344045072515406103)
                ·
                  refine ⟨17532152016067608773109155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11688101344045072515406103 17532152016067608773109155)
                  ·
                    refine ⟨26298228024101413159663733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17532152016067608773109155 26298228024101413159663733)
                    ·
                      refine ⟨2465458877259507483718475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26298228024101413159663733 2465458877259507483718475)
                      ·
                        rfl

theorem cell23_4801464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_4801464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801464 prefixEnd_4801464 := by exact prefixLift 4801464
  have htrace : WordTrace (prefixWord ++ tailWord_4801464) baseStart_4801464 baseEnd_4801464 := by
    simpa [prefixWord, tailWord_4801464, baseEnd_4801464] using wordTrace_append hprefix tailTrace_4801464
  have hstable : (prefixWord ++ tailWord_4801464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801464).length < 2 ^ (prefixWord ++ tailWord_4801464).sum := by decide
  have hdescent : baseEnd_4801464 < baseStart_4801464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801507 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4801507 : Nat := 118140960795 + 4801507 * 2 ^ 59
def prefixEnd_4801507 : Nat := 4983230072969 + 3 ^ 40 * 4801507 * 2
def baseEnd_4801507 : Nat := 2465480956927650815480777

theorem tailTrace_4801507 : CollatzResearch.WordTrace tailWord_4801507 prefixEnd_4801507 2465480956927650815480777 := by
  unfold tailWord_4801507
  simp only [CollatzResearch.WordTrace]
  refine ⟨175125347415967645954618775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116750231610645097303079183 175125347415967645954618775)
  ·
    refine ⟨262688021123951468931928163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175125347415967645954618775 262688021123951468931928163)
    ·
      refine ⟨394032031685927203397892245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262688021123951468931928163 394032031685927203397892245)
      ·
        refine ⟨18470251485277837659276199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 394032031685927203397892245 18470251485277837659276199)
        ·
          refine ⟨27705377227916756488914299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18470251485277837659276199 27705377227916756488914299)
          ·
            refine ⟨41558065841875134733371449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27705377227916756488914299 41558065841875134733371449)
            ·
              refine ⟨31168549381406351050028587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41558065841875134733371449 31168549381406351050028587)
              ·
                refine ⟨46752824072109526575042881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31168549381406351050028587 46752824072109526575042881)
                ·
                  refine ⟨35064618054082144931282161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46752824072109526575042881 35064618054082144931282161)
                  ·
                    refine ⟨26298463540561608698461621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35064618054082144931282161 26298463540561608698461621)
                    ·
                      refine ⟨2465480956927650815480777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26298463540561608698461621 2465480956927650815480777)
                      ·
                        rfl

theorem cell23_4801507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4801507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801507 prefixEnd_4801507 := by exact prefixLift 4801507
  have htrace : WordTrace (prefixWord ++ tailWord_4801507) baseStart_4801507 baseEnd_4801507 := by
    simpa [prefixWord, tailWord_4801507, baseEnd_4801507] using wordTrace_append hprefix tailTrace_4801507
  have hstable : (prefixWord ++ tailWord_4801507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801507).length < 2 ^ (prefixWord ++ tailWord_4801507).sum := by decide
  have hdescent : baseEnd_4801507 < baseStart_4801507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801617 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 2, 8]
def baseStart_4801617 : Nat := 118140960795 + 4801617 * 2 ^ 59
def prefixEnd_4801617 : Nat := 4983230072969 + 3 ^ 40 * 4801617 * 2
def baseEnd_4801617 : Nat := 821845813266548461701757

theorem tailTrace_4801617 : CollatzResearch.WordTrace tailWord_4801617 prefixEnd_4801617 821845813266548461701757 := by
  unfold tailWord_4801617
  simp only [CollatzResearch.WordTrace]
  refine ⟨175129359445569134741123105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116752906297046089827415403 175129359445569134741123105)
  ·
    refine ⟨131347019584176851055842329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175129359445569134741123105 131347019584176851055842329)
    ·
      refine ⟨98510264688132638291881747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131347019584176851055842329 98510264688132638291881747)
      ·
        refine ⟨147765397032198957437822621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98510264688132638291881747 147765397032198957437822621)
        ·
          refine ⟨55412023887074609039183483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147765397032198957437822621 55412023887074609039183483)
          ·
            refine ⟨83118035830611913558775225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55412023887074609039183483 83118035830611913558775225)
            ·
              refine ⟨62338526872958935169081419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83118035830611913558775225 62338526872958935169081419)
              ·
                refine ⟨93507790309438402753622129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62338526872958935169081419 93507790309438402753622129)
                ·
                  refine ⟨70130842732078802065216597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93507790309438402753622129 70130842732078802065216597)
                  ·
                    refine ⟨821845813266548461701757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70130842732078802065216597 821845813266548461701757)
                    ·
                      rfl

theorem cell23_4801617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_4801617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801617 prefixEnd_4801617 := by exact prefixLift 4801617
  have htrace : WordTrace (prefixWord ++ tailWord_4801617) baseStart_4801617 baseEnd_4801617 := by
    simpa [prefixWord, tailWord_4801617, baseEnd_4801617] using wordTrace_append hprefix tailTrace_4801617
  have hstable : (prefixWord ++ tailWord_4801617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801617).length < 2 ^ (prefixWord ++ tailWord_4801617).sum := by decide
  have hdescent : baseEnd_4801617 < baseStart_4801617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801664 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 6]
def baseStart_4801664 : Nat := 118140960795 + 4801664 * 2 ^ 59
def prefixEnd_4801664 : Nat := 4983230072969 + 3 ^ 40 * 4801664 * 2
def baseEnd_4801664 : Nat := 273951285932267411246395

theorem tailTrace_4801664 : CollatzResearch.WordTrace tailWord_4801664 prefixEnd_4801664 273951285932267411246395 := by
  unfold tailWord_4801664
  simp only [CollatzResearch.WordTrace]
  refine ⟨87565536838199430884042023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116754049117599241178722697 87565536838199430884042023)
  ·
    refine ⟨131348305257299146326063035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87565536838199430884042023 131348305257299146326063035)
    ·
      refine ⟨197022457885948719489094553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131348305257299146326063035 197022457885948719489094553)
      ·
        refine ⟨147766843414461539616820915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197022457885948719489094553 147766843414461539616820915)
        ·
          refine ⟨221650265121692309425231373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147766843414461539616820915 221650265121692309425231373)
          ·
            refine ⟨83118849420634616034461765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221650265121692309425231373 83118849420634616034461765)
            ·
              refine ⟨15584784266368990506461581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83118849420634616034461765 15584784266368990506461581)
              ·
                refine ⟨5844294099888371439923093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15584784266368990506461581 5844294099888371439923093)
                ·
                  refine ⟨273951285932267411246395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5844294099888371439923093 273951285932267411246395)
                  ·
                    rfl

theorem cell23_4801664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 6].length) (baseStart_4801664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801664 prefixEnd_4801664 := by exact prefixLift 4801664
  have htrace : WordTrace (prefixWord ++ tailWord_4801664) baseStart_4801664 baseEnd_4801664 := by
    simpa [prefixWord, tailWord_4801664, baseEnd_4801664] using wordTrace_append hprefix tailTrace_4801664
  have hstable : (prefixWord ++ tailWord_4801664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801664).length < 2 ^ (prefixWord ++ tailWord_4801664).sum := by decide
  have hdescent : baseEnd_4801664 < baseStart_4801664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801678 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_4801678 : Nat := 118140960795 + 4801678 * 2 ^ 59
def prefixEnd_4801678 : Nat := 4983230072969 + 3 ^ 40 * 4801678 * 2
def baseEnd_4801678 : Nat := 2465568762119569646442491

theorem tailTrace_4801678 : CollatzResearch.WordTrace tailWord_4801678 prefixEnd_4801678 2465568762119569646442491 := by
  unfold tailWord_4801678
  simp only [CollatzResearch.WordTrace]
  refine ⟨21891448037293517769886711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116754389532232094772729125 21891448037293517769886711)
  ·
    refine ⟨32837172055940276654830067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21891448037293517769886711 32837172055940276654830067)
    ·
      refine ⟨49255758083910414982245101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32837172055940276654830067 49255758083910414982245101)
      ·
        refine ⟨18470909281466405618341913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49255758083910414982245101 18470909281466405618341913)
        ·
          refine ⟨13853181961099804213756435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18470909281466405618341913 13853181961099804213756435)
          ·
            refine ⟨20779772941649706320634653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13853181961099804213756435 20779772941649706320634653)
            ·
              refine ⟨7792414853118639870237995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20779772941649706320634653 7792414853118639870237995)
              ·
                refine ⟨11688622279677959805356993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7792414853118639870237995 11688622279677959805356993)
                ·
                  refine ⟨8766466709758469854017745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11688622279677959805356993 8766466709758469854017745)
                  ·
                    refine ⟨6574850032318852390513309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8766466709758469854017745 6574850032318852390513309)
                    ·
                      refine ⟨2465568762119569646442491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6574850032318852390513309 2465568762119569646442491)
                      ·
                        rfl

theorem cell23_4801678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_4801678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801678 prefixEnd_4801678 := by exact prefixLift 4801678
  have htrace : WordTrace (prefixWord ++ tailWord_4801678) baseStart_4801678 baseEnd_4801678 := by
    simpa [prefixWord, tailWord_4801678, baseEnd_4801678] using wordTrace_append hprefix tailTrace_4801678
  have hstable : (prefixWord ++ tailWord_4801678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801678).length < 2 ^ (prefixWord ++ tailWord_4801678).sum := by decide
  have hdescent : baseEnd_4801678 < baseStart_4801678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801728 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 1, 5]
def baseStart_4801728 : Nat := 118140960795 + 4801728 * 2 ^ 59
def prefixEnd_4801728 : Nat := 4983230072969 + 3 ^ 40 * 4801728 * 2
def baseEnd_4801728 : Nat := 821864812050764816939087

theorem tailTrace_4801728 : CollatzResearch.WordTrace tailWord_4801728 prefixEnd_4801728 821864812050764816939087 := by
  unfold tailWord_4801728
  simp only [CollatzResearch.WordTrace]
  refine ⟨87566703974083500349206919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116755605298778000465609225 87566703974083500349206919)
  ·
    refine ⟨131350055961125250523810379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87566703974083500349206919 131350055961125250523810379)
    ·
      refine ⟨197025083941687875785715569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131350055961125250523810379 197025083941687875785715569)
      ·
        refine ⟨147768812956265906839286677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197025083941687875785715569 147768812956265906839286677)
        ·
          refine ⟨6926663107324964383091563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 147768812956265906839286677 6926663107324964383091563)
          ·
            refine ⟨10389994660987446574637345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6926663107324964383091563 10389994660987446574637345)
            ·
              refine ⟨7792495995740584930978009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10389994660987446574637345 7792495995740584930978009)
              ·
                refine ⟨5844371996805438698233507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7792495995740584930978009 5844371996805438698233507)
                ·
                  refine ⟨8766557995208158047350261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5844371996805438698233507 8766557995208158047350261)
                  ·
                    refine ⟨821864812050764816939087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8766557995208158047350261 821864812050764816939087)
                    ·
                      rfl

theorem cell23_4801728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 5].length) (baseStart_4801728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801728 prefixEnd_4801728 := by exact prefixLift 4801728
  have htrace : WordTrace (prefixWord ++ tailWord_4801728) baseStart_4801728 baseEnd_4801728 := by
    simpa [prefixWord, tailWord_4801728, baseEnd_4801728] using wordTrace_append hprefix tailTrace_4801728
  have hstable : (prefixWord ++ tailWord_4801728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801728).length < 2 ^ (prefixWord ++ tailWord_4801728).sum := by decide
  have hdescent : baseEnd_4801728 < baseStart_4801728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801815 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 2, 1, 3]
def baseStart_4801815 : Nat := 118140960795 + 4801815 * 2 ^ 59
def prefixEnd_4801815 : Nat := 4983230072969 + 3 ^ 40 * 4801815 * 2
def baseEnd_4801815 : Nat := 2465639108969235610429361

theorem tailTrace_4801815 : CollatzResearch.WordTrace tailWord_4801815 prefixEnd_4801815 2465639108969235610429361 := by
  unfold tailWord_4801815
  simp only [CollatzResearch.WordTrace]
  refine ⟨175136581098851814556830899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116757720732567876371220599 175136581098851814556830899)
  ·
    refine ⟨262704871648277721835246349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175136581098851814556830899 262704871648277721835246349)
    ·
      refine ⟨98514326868104145688217381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262704871648277721835246349 98514326868104145688217381)
      ·
        refine ⟨18471436287769527316540759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98514326868104145688217381 18471436287769527316540759)
        ·
          refine ⟨27707154431654290974811139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18471436287769527316540759 27707154431654290974811139)
          ·
            refine ⟨41560731647481436462216709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27707154431654290974811139 41560731647481436462216709)
            ·
              refine ⟨7792637183902769336665633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41560731647481436462216709 7792637183902769336665633)
              ·
                refine ⟨5844477887927077002499225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7792637183902769336665633 5844477887927077002499225)
                ·
                  refine ⟨4383358415945307751874419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5844477887927077002499225 4383358415945307751874419)
                  ·
                    refine ⟨6575037623917961627811629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4383358415945307751874419 6575037623917961627811629)
                    ·
                      refine ⟨2465639108969235610429361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6575037623917961627811629 2465639108969235610429361)
                      ·
                        rfl

theorem cell23_4801815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_4801815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801815 prefixEnd_4801815 := by exact prefixLift 4801815
  have htrace : WordTrace (prefixWord ++ tailWord_4801815) baseStart_4801815 baseEnd_4801815 := by
    simpa [prefixWord, tailWord_4801815, baseEnd_4801815] using wordTrace_append hprefix tailTrace_4801815
  have hstable : (prefixWord ++ tailWord_4801815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801815).length < 2 ^ (prefixWord ++ tailWord_4801815).sum := by decide
  have hdescent : baseEnd_4801815 < baseStart_4801815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801822 : List Nat := [4, 3, 2, 1, 3, 1, 1, 8]
def baseStart_4801822 : Nat := 118140960795 + 4801822 * 2 ^ 59
def prefixEnd_4801822 : Nat := 4983230072969 + 3 ^ 40 * 4801822 * 2
def baseEnd_4801822 : Nat := 91320100123474706779327

theorem tailTrace_4801822 : CollatzResearch.WordTrace tailWord_4801822 prefixEnd_4801822 91320100123474706779327 := by
  unfold tailWord_4801822
  simp only [CollatzResearch.WordTrace]
  refine ⟨21892104551228306844041965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116757890939884303168223813 21892104551228306844041965)
  ·
    refine ⟨8209539206710615066515737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21892104551228306844041965 8209539206710615066515737)
    ·
      refine ⟨6157154405032961299886803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8209539206710615066515737 6157154405032961299886803)
      ·
        refine ⟨9235731607549441949830205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6157154405032961299886803 9235731607549441949830205)
        ·
          refine ⟨3463399352831040731186327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9235731607549441949830205 3463399352831040731186327)
          ·
            refine ⟨5195099029246561096779491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3463399352831040731186327 5195099029246561096779491)
            ·
              refine ⟨7792648543869841645169237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5195099029246561096779491 7792648543869841645169237)
              ·
                refine ⟨91320100123474706779327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7792648543869841645169237 91320100123474706779327)
                ·
                  rfl

theorem cell23_4801822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_4801822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801822 prefixEnd_4801822 := by exact prefixLift 4801822
  have htrace : WordTrace (prefixWord ++ tailWord_4801822) baseStart_4801822 baseEnd_4801822 := by
    simpa [prefixWord, tailWord_4801822, baseEnd_4801822] using wordTrace_append hprefix tailTrace_4801822
  have hstable : (prefixWord ++ tailWord_4801822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801822).length < 2 ^ (prefixWord ++ tailWord_4801822).sum := by decide
  have hdescent : baseEnd_4801822 < baseStart_4801822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801888 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 3]
def baseStart_4801888 : Nat := 118140960795 + 4801888 * 2 ^ 59
def prefixEnd_4801888 : Nat := 4983230072969 + 3 ^ 40 * 4801888 * 2
def baseEnd_4801888 : Nat := 2465676593057013824816525

theorem tailTrace_4801888 : CollatzResearch.WordTrace tailWord_4801888 prefixEnd_4801888 2465676593057013824816525 := by
  unfold tailWord_4801888
  simp only [CollatzResearch.WordTrace]
  refine ⟨87569621813793674012119159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116759495751724898682825545 87569621813793674012119159)
  ·
    refine ⟨131354432720690511018178739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87569621813793674012119159 131354432720690511018178739)
    ·
      refine ⟨197031649081035766527268109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131354432720690511018178739 197031649081035766527268109)
      ·
        refine ⟨73886868405388412447725541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197031649081035766527268109 73886868405388412447725541)
        ·
          refine ⟨13853787826010327333948539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73886868405388412447725541 13853787826010327333948539)
          ·
            refine ⟨20780681739015491000922809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13853787826010327333948539 20780681739015491000922809)
            ·
              refine ⟨15585511304261618250692107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20780681739015491000922809 15585511304261618250692107)
              ·
                refine ⟨23378266956392427376038161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15585511304261618250692107 23378266956392427376038161)
                ·
                  refine ⟨17533700217294320532028621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23378266956392427376038161 17533700217294320532028621)
                  ·
                    refine ⟨6575137581485370199510733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17533700217294320532028621 6575137581485370199510733)
                    ·
                      refine ⟨2465676593057013824816525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6575137581485370199510733 2465676593057013824816525)
                      ·
                        rfl

theorem cell23_4801888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_4801888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801888 prefixEnd_4801888 := by exact prefixLift 4801888
  have htrace : WordTrace (prefixWord ++ tailWord_4801888) baseStart_4801888 baseEnd_4801888 := by
    simpa [prefixWord, tailWord_4801888, baseEnd_4801888] using wordTrace_append hprefix tailTrace_4801888
  have hstable : (prefixWord ++ tailWord_4801888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801888).length < 2 ^ (prefixWord ++ tailWord_4801888).sum := by decide
  have hdescent : baseEnd_4801888 < baseStart_4801888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801891 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 1, 7]
def baseStart_4801891 : Nat := 118140960795 + 4801891 * 2 ^ 59
def prefixEnd_4801891 : Nat := 4983230072969 + 3 ^ 40 * 4801891 * 2
def baseEnd_4801891 : Nat := 821892711166325771026337

theorem tailTrace_4801891 : CollatzResearch.WordTrace tailWord_4801891 prefixEnd_4801891 821892711166325771026337 := by
  unfold tailWord_4801891
  simp only [CollatzResearch.WordTrace]
  refine ⟨175139353046576479536597527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116759568697717653024398351 175139353046576479536597527)
  ·
    refine ⟨262709029569864719304896291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175139353046576479536597527 262709029569864719304896291)
    ·
      refine ⟨394063544354797078957344437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262709029569864719304896291 394063544354797078957344437)
      ·
        refine ⟨36943457283262226152251041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 394063544354797078957344437 36943457283262226152251041)
        ·
          refine ⟨27707592962446669614188281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36943457283262226152251041 27707592962446669614188281)
          ·
            refine ⟨20780694721835002210641211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27707592962446669614188281 20780694721835002210641211)
            ·
              refine ⟨31171042082752503315961817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20780694721835002210641211 31171042082752503315961817)
              ·
                refine ⟨23378281562064377486971363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31171042082752503315961817 23378281562064377486971363)
                ·
                  refine ⟨35067422343096566230457045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23378281562064377486971363 35067422343096566230457045)
                  ·
                    refine ⟨821892711166325771026337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35067422343096566230457045 821892711166325771026337)
                    ·
                      rfl

theorem cell23_4801891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 7].length) (baseStart_4801891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801891 prefixEnd_4801891 := by exact prefixLift 4801891
  have htrace : WordTrace (prefixWord ++ tailWord_4801891) baseStart_4801891 baseEnd_4801891 := by
    simpa [prefixWord, tailWord_4801891, baseEnd_4801891] using wordTrace_append hprefix tailTrace_4801891
  have hstable : (prefixWord ++ tailWord_4801891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801891).length < 2 ^ (prefixWord ++ tailWord_4801891).sum := by decide
  have hdescent : baseEnd_4801891 < baseStart_4801891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801911 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_4801911 : Nat := 118140960795 + 4801911 * 2 ^ 59
def prefixEnd_4801911 : Nat := 4983230072969 + 3 ^ 40 * 4801911 * 2
def baseEnd_4801911 : Nat := 2465688403112067234828919

theorem tailTrace_4801911 : CollatzResearch.WordTrace tailWord_4801911 prefixEnd_4801911 2465688403112067234828919 := by
  unfold tailWord_4801911
  simp only [CollatzResearch.WordTrace]
  refine ⟨175140082506504022952325587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116760055004336015301550391 175140082506504022952325587)
  ·
    refine ⟨262710123759756034428488381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175140082506504022952325587 262710123759756034428488381)
    ·
      refine ⟨98516296409908512910683143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262710123759756034428488381 98516296409908512910683143)
      ·
        refine ⟨147774444614862769366024715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98516296409908512910683143 147774444614862769366024715)
        ·
          refine ⟨221661666922294154049037073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147774444614862769366024715 221661666922294154049037073)
          ·
            refine ⟨166246250191720615536777805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221661666922294154049037073 166246250191720615536777805)
            ·
              refine ⟨62342343821895230826291677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166246250191720615536777805 62342343821895230826291677)
              ·
                refine ⟨23378378933210711559859379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62342343821895230826291677 23378378933210711559859379)
                ·
                  refine ⟨35067568399816067339789069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23378378933210711559859379 35067568399816067339789069)
                  ·
                    refine ⟨13150338149931025252420901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35067568399816067339789069 13150338149931025252420901)
                    ·
                      refine ⟨2465688403112067234828919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13150338149931025252420901 2465688403112067234828919)
                      ·
                        rfl

theorem cell23_4801911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_4801911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801911 prefixEnd_4801911 := by exact prefixLift 4801911
  have htrace : WordTrace (prefixWord ++ tailWord_4801911) baseStart_4801911 baseEnd_4801911 := by
    simpa [prefixWord, tailWord_4801911, baseEnd_4801911] using wordTrace_append hprefix tailTrace_4801911
  have hstable : (prefixWord ++ tailWord_4801911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801911).length < 2 ^ (prefixWord ++ tailWord_4801911).sum := by decide
  have hdescent : baseEnd_4801911 < baseStart_4801911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801928 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_4801928 : Nat := 118140960795 + 4801928 * 2 ^ 59
def prefixEnd_4801928 : Nat := 4983230072969 + 3 ^ 40 * 4801928 * 2
def baseEnd_4801928 : Nat := 2465697132283193668316341

theorem tailTrace_4801928 : CollatzResearch.WordTrace tailWord_4801928 prefixEnd_4801928 2465697132283193668316341 := by
  unfold tailWord_4801928
  simp only [CollatzResearch.WordTrace]
  refine ⟨87570351273721217427847219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116760468364961623237129625 87570351273721217427847219)
  ·
    refine ⟨131355526910581826141770829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87570351273721217427847219 131355526910581826141770829)
    ·
      refine ⟨49258322591468184803164061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131355526910581826141770829 49258322591468184803164061)
      ·
        refine ⟨18471870971800569301186523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49258322591468184803164061 18471870971800569301186523)
        ·
          refine ⟨27707806457700853951779785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18471870971800569301186523 27707806457700853951779785)
          ·
            refine ⟨20780854843275640463834839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27707806457700853951779785 20780854843275640463834839)
            ·
              refine ⟨31171282264913460695752259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20780854843275640463834839 31171282264913460695752259)
              ·
                refine ⟨46756923397370191043628389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31171282264913460695752259 46756923397370191043628389)
                ·
                  refine ⟨8766923137006910820680323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46756923397370191043628389 8766923137006910820680323)
                  ·
                    refine ⟨13150384705510366231020485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8766923137006910820680323 13150384705510366231020485)
                    ·
                      refine ⟨2465697132283193668316341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13150384705510366231020485 2465697132283193668316341)
                      ·
                        rfl

theorem cell23_4801928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_4801928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801928 prefixEnd_4801928 := by exact prefixLift 4801928
  have htrace : WordTrace (prefixWord ++ tailWord_4801928) baseStart_4801928 baseEnd_4801928 := by
    simpa [prefixWord, tailWord_4801928, baseEnd_4801928] using wordTrace_append hprefix tailTrace_4801928
  have hstable : (prefixWord ++ tailWord_4801928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801928).length < 2 ^ (prefixWord ++ tailWord_4801928).sum := by decide
  have hdescent : baseEnd_4801928 < baseStart_4801928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801941 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_4801941 : Nat := 118140960795 + 4801941 * 2 ^ 59
def prefixEnd_4801941 : Nat := 4983230072969 + 3 ^ 40 * 4801941 * 2
def baseEnd_4801941 : Nat := 2465703807531702117453781

theorem tailTrace_4801941 : CollatzResearch.WordTrace tailWord_4801941 prefixEnd_4801941 2465703807531702117453781 := by
  unfold tailWord_4801941
  simp only [CollatzResearch.WordTrace]
  refine ⟨175141176696395338075917677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116760784464263558717278451 175141176696395338075917677)
  ·
    refine ⟨65677941261148251778469129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175141176696395338075917677 65677941261148251778469129)
    ·
      refine ⟨49258455945861188833851847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65677941261148251778469129 49258455945861188833851847)
      ·
        refine ⟨73887683918791783250777771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49258455945861188833851847 73887683918791783250777771)
        ·
          refine ⟨110831525878187674876166657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73887683918791783250777771 110831525878187674876166657)
          ·
            refine ⟨83123644408640756157124993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110831525878187674876166657 83123644408640756157124993)
            ·
              refine ⟨62342733306480567117843745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83123644408640756157124993 62342733306480567117843745)
              ·
                refine ⟨46757049979860425338382809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62342733306480567117843745 46757049979860425338382809)
                ·
                  refine ⟨35067787484895319003787107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46757049979860425338382809 35067787484895319003787107)
                  ·
                    refine ⟨52601681227342978505680661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35067787484895319003787107 52601681227342978505680661)
                    ·
                      refine ⟨2465703807531702117453781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52601681227342978505680661 2465703807531702117453781)
                      ·
                        rfl

theorem cell23_4801941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_4801941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801941 prefixEnd_4801941 := by exact prefixLift 4801941
  have htrace : WordTrace (prefixWord ++ tailWord_4801941) baseStart_4801941 baseEnd_4801941 := by
    simpa [prefixWord, tailWord_4801941, baseEnd_4801941] using wordTrace_append hprefix tailTrace_4801941
  have hstable : (prefixWord ++ tailWord_4801941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801941).length < 2 ^ (prefixWord ++ tailWord_4801941).sum := by decide
  have hdescent : baseEnd_4801941 < baseStart_4801941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4801998 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_4801998 : Nat := 118140960795 + 4801998 * 2 ^ 59
def prefixEnd_4801998 : Nat := 4983230072969 + 3 ^ 40 * 4801998 * 2
def baseEnd_4801998 : Nat := 821911025309669464813673

theorem tailTrace_4801998 : CollatzResearch.WordTrace tailWord_4801998 prefixEnd_4801998 821911025309669464813673 := by
  unfold tailWord_4801998
  simp only [CollatzResearch.WordTrace]
  refine ⟨21892906957148604601342831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116762170438125891207161765 21892906957148604601342831)
  ·
    refine ⟨32839360435722906902014247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21892906957148604601342831 32839360435722906902014247)
    ·
      refine ⟨49259040653584360353021371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32839360435722906902014247 49259040653584360353021371)
      ·
        refine ⟨73888560980376540529532057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49259040653584360353021371 73888560980376540529532057)
        ·
          refine ⟨55416420735282405397149043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73888560980376540529532057 55416420735282405397149043)
          ·
            refine ⟨83124631102923608095723565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55416420735282405397149043 83124631102923608095723565)
            ·
              refine ⟨31171736663596353035896337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83124631102923608095723565 31171736663596353035896337)
              ·
                refine ⟨23378802497697264776922253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31171736663596353035896337 23378802497697264776922253)
                ·
                  refine ⟨8767050936636474291345845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23378802497697264776922253 8767050936636474291345845)
                  ·
                    refine ⟨821911025309669464813673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8767050936636474291345845 821911025309669464813673)
                    ·
                      rfl

theorem cell23_4801998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_4801998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4801998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4801998 prefixEnd_4801998 := by exact prefixLift 4801998
  have htrace : WordTrace (prefixWord ++ tailWord_4801998) baseStart_4801998 baseEnd_4801998 := by
    simpa [prefixWord, tailWord_4801998, baseEnd_4801998] using wordTrace_append hprefix tailTrace_4801998
  have hstable : (prefixWord ++ tailWord_4801998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4801998).length < 2 ^ (prefixWord ++ tailWord_4801998).sum := by decide
  have hdescent : baseEnd_4801998 < baseStart_4801998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4801998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802005 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 1, 5, 2]
def baseStart_4802005 : Nat := 118140960795 + 4802005 * 2 ^ 59
def prefixEnd_4802005 : Nat := 4983230072969 + 3 ^ 40 * 4802005 * 2
def baseEnd_4802005 : Nat := 2465736670293589867053487

theorem tailTrace_4802005 : CollatzResearch.WordTrace tailWord_4802005 prefixEnd_4802005 2465736670293589867053487 := by
  unfold tailWord_4802005
  simp only [CollatzResearch.WordTrace]
  refine ⟨175143510968163477006247469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116762340645442318004164979 175143510968163477006247469)
  ·
    refine ⟨65678816613061303877342801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175143510968163477006247469 65678816613061303877342801)
    ·
      refine ⟨49259112459795977908007101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65678816613061303877342801 49259112459795977908007101)
      ·
        refine ⟨18472167172423491715502663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49259112459795977908007101 18472167172423491715502663)
        ·
          refine ⟨27708250758635237573253995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18472167172423491715502663 27708250758635237573253995)
          ·
            refine ⟨41562376137952856359880993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27708250758635237573253995 41562376137952856359880993)
            ·
              refine ⟨31171782103464642269910745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41562376137952856359880993 31171782103464642269910745)
              ·
                refine ⟨23378836577598481702433059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31171782103464642269910745 23378836577598481702433059)
                ·
                  refine ⟨35068254866397722553649589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23378836577598481702433059 35068254866397722553649589)
                  ·
                    refine ⟨3287648893724786489404649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35068254866397722553649589 3287648893724786489404649)
                    ·
                      refine ⟨2465736670293589867053487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3287648893724786489404649 2465736670293589867053487)
                      ·
                        rfl

theorem cell23_4802005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_4802005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802005 prefixEnd_4802005 := by exact prefixLift 4802005
  have htrace : WordTrace (prefixWord ++ tailWord_4802005) baseStart_4802005 baseEnd_4802005 := by
    simpa [prefixWord, tailWord_4802005, baseEnd_4802005] using wordTrace_append hprefix tailTrace_4802005
  have hstable : (prefixWord ++ tailWord_4802005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802005).length < 2 ^ (prefixWord ++ tailWord_4802005).sum := by decide
  have hdescent : baseEnd_4802005 < baseStart_4802005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802032 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 1, 5]
def baseStart_4802032 : Nat := 118140960795 + 4802032 * 2 ^ 59
def prefixEnd_4802032 : Nat := 4983230072969 + 3 ^ 40 * 4802032 * 2
def baseEnd_4802032 : Nat := 821916844757087087138621

theorem tailTrace_4802032 : CollatzResearch.WordTrace tailWord_4802032 prefixEnd_4802032 821916844757087087138621 := by
  unfold tailWord_4802032
  simp only [CollatzResearch.WordTrace]
  refine ⟨87572247869532830308740175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116762997159377107078320233 87572247869532830308740175)
  ·
    refine ⟨131358371804299245463110263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87572247869532830308740175 131358371804299245463110263)
    ·
      refine ⟨197037557706448868194665395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131358371804299245463110263 197037557706448868194665395)
      ·
        refine ⟨295556336559673302291998093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197037557706448868194665395 295556336559673302291998093)
        ·
          refine ⟨110833626209877488359499285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295556336559673302291998093 110833626209877488359499285)
          ·
            refine ⟨5195326228588007266851529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110833626209877488359499285 5195326228588007266851529)
            ·
              refine ⟨3896494671441005450138647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5195326228588007266851529 3896494671441005450138647)
              ·
                refine ⟨5844742007161508175207971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3896494671441005450138647 5844742007161508175207971)
                ·
                  refine ⟨8767113010742262262811957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5844742007161508175207971 8767113010742262262811957)
                  ·
                    refine ⟨821916844757087087138621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8767113010742262262811957 821916844757087087138621)
                    ·
                      rfl

theorem cell23_4802032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 5].length) (baseStart_4802032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802032 prefixEnd_4802032 := by exact prefixLift 4802032
  have htrace : WordTrace (prefixWord ++ tailWord_4802032) baseStart_4802032 baseEnd_4802032 := by
    simpa [prefixWord, tailWord_4802032, baseEnd_4802032] using wordTrace_append hprefix tailTrace_4802032
  have hstable : (prefixWord ++ tailWord_4802032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802032).length < 2 ^ (prefixWord ++ tailWord_4802032).sum := by decide
  have hdescent : baseEnd_4802032 < baseStart_4802032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802045 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_4802045 : Nat := 118140960795 + 4802045 * 2 ^ 59
def prefixEnd_4802045 : Nat := 4983230072969 + 3 ^ 40 * 4802045 * 2
def baseEnd_4802045 : Nat := 821919069839923236851101

theorem tailTrace_4802045 : CollatzResearch.WordTrace tailWord_4802045 prefixEnd_4802045 821919069839923236851101 := by
  unfold tailWord_4802045
  simp only [CollatzResearch.WordTrace]
  refine ⟨175144969888018563837703589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116763313258679042558469059 175144969888018563837703589)
  ·
    refine ⟨32839681854003480719569423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175144969888018563837703589 32839681854003480719569423)
    ·
      refine ⟨49259522781005221079354135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32839681854003480719569423 49259522781005221079354135)
      ·
        refine ⟨73889284171507831619031203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49259522781005221079354135 73889284171507831619031203)
        ·
          refine ⟨110833926257261747428546805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73889284171507831619031203 110833926257261747428546805)
          ·
            refine ⟨10390680586618288821426263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110833926257261747428546805 10390680586618288821426263)
            ·
              refine ⟨15586020879927433232139395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10390680586618288821426263 15586020879927433232139395)
              ·
                refine ⟨23379031319891149848209093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15586020879927433232139395 23379031319891149848209093)
                ·
                  refine ⟨4383568372479590596539205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23379031319891149848209093 4383568372479590596539205)
                  ·
                    refine ⟨821919069839923236851101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4383568372479590596539205 821919069839923236851101)
                    ·
                      rfl

theorem cell23_4802045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_4802045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802045 prefixEnd_4802045 := by exact prefixLift 4802045
  have htrace : WordTrace (prefixWord ++ tailWord_4802045) baseStart_4802045 baseEnd_4802045 := by
    simpa [prefixWord, tailWord_4802045, baseEnd_4802045] using wordTrace_append hprefix tailTrace_4802045
  have hstable : (prefixWord ++ tailWord_4802045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802045).length < 2 ^ (prefixWord ++ tailWord_4802045).sum := by decide
  have hdescent : baseEnd_4802045 < baseStart_4802045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802046 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4802046 : Nat := 118140960795 + 4802046 * 2 ^ 59
def prefixEnd_4802046 : Nat := 4983230072969 + 3 ^ 40 * 4802046 * 2
def baseEnd_4802046 : Nat := 2465757723000424206640799

theorem tailTrace_4802046 : CollatzResearch.WordTrace tailWord_4802046 prefixEnd_4802046 2465757723000424206640799 := by
  unfold tailWord_4802046
  simp only [CollatzResearch.WordTrace]
  refine ⟨21893125795126867626061249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116763337574009960672326661 21893125795126867626061249)
  ·
    refine ⟨16419844346345150719545937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21893125795126867626061249 16419844346345150719545937)
    ·
      refine ⟨12314883259758863039659453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16419844346345150719545937 12314883259758863039659453)
      ·
        refine ⟨4618081222409573639872295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12314883259758863039659453 4618081222409573639872295)
        ·
          refine ⟨6927121833614360459808443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4618081222409573639872295 6927121833614360459808443)
          ·
            refine ⟨10390682750421540689712665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6927121833614360459808443 10390682750421540689712665)
            ·
              refine ⟨7793012062816155517284499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10390682750421540689712665 7793012062816155517284499)
              ·
                refine ⟨11689518094224233275926749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7793012062816155517284499 11689518094224233275926749)
                ·
                  refine ⟨4383569285334087478472531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11689518094224233275926749 4383569285334087478472531)
                  ·
                    refine ⟨6575353928001131217708797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4383569285334087478472531 6575353928001131217708797)
                    ·
                      refine ⟨2465757723000424206640799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6575353928001131217708797 2465757723000424206640799)
                      ·
                        rfl

theorem cell23_4802046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4802046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802046 prefixEnd_4802046 := by exact prefixLift 4802046
  have htrace : WordTrace (prefixWord ++ tailWord_4802046) baseStart_4802046 baseEnd_4802046 := by
    simpa [prefixWord, tailWord_4802046, baseEnd_4802046] using wordTrace_append hprefix tailTrace_4802046
  have hstable : (prefixWord ++ tailWord_4802046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802046).length < 2 ^ (prefixWord ++ tailWord_4802046).sum := by decide
  have hdescent : baseEnd_4802046 < baseStart_4802046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802055 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_4802055 : Nat := 118140960795 + 4802055 * 2 ^ 59
def prefixEnd_4802055 : Nat := 4983230072969 + 3 ^ 40 * 4802055 * 2
def baseEnd_4802055 : Nat := 2465762344326314671428257

theorem tailTrace_4802055 : CollatzResearch.WordTrace tailWord_4802055 prefixEnd_4802055 2465762344326314671428257 := by
  unfold tailWord_4802055
  simp only [CollatzResearch.WordTrace]
  refine ⟨175145334617982335545567619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116763556411988223697045079 175145334617982335545567619)
  ·
    refine ⟨262718001926973503318351429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175145334617982335545567619 262718001926973503318351429)
    ·
      refine ⟨49259625361307531872190893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262718001926973503318351429 49259625361307531872190893)
      ·
        refine ⟨18472359510490324452071585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49259625361307531872190893 18472359510490324452071585)
        ·
          refine ⟨13854269632867743339053689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18472359510490324452071585 13854269632867743339053689)
          ·
            refine ⟨10390702224650807504290267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13854269632867743339053689 10390702224650807504290267)
            ·
              refine ⟨15586053336976211256435401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10390702224650807504290267 15586053336976211256435401)
              ·
                refine ⟨11689540002732158442326551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15586053336976211256435401 11689540002732158442326551)
                ·
                  refine ⟨17534310004098237663489827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11689540002732158442326551 17534310004098237663489827)
                  ·
                    refine ⟨26301465006147356495234741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17534310004098237663489827 26301465006147356495234741)
                    ·
                      refine ⟨2465762344326314671428257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26301465006147356495234741 2465762344326314671428257)
                      ·
                        rfl

theorem cell23_4802055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_4802055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802055 prefixEnd_4802055 := by exact prefixLift 4802055
  have htrace : WordTrace (prefixWord ++ tailWord_4802055) baseStart_4802055 baseEnd_4802055 := by
    simpa [prefixWord, tailWord_4802055, baseEnd_4802055] using wordTrace_append hprefix tailTrace_4802055
  have hstable : (prefixWord ++ tailWord_4802055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802055).length < 2 ^ (prefixWord ++ tailWord_4802055).sum := by decide
  have hdescent : baseEnd_4802055 < baseStart_4802055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802062 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_4802062 : Nat := 118140960795 + 4802062 * 2 ^ 59
def prefixEnd_4802062 : Nat := 4983230072969 + 3 ^ 40 * 4802062 * 2
def baseEnd_4802062 : Nat := 821921979563632048013575

theorem tailTrace_4802062 : CollatzResearch.WordTrace tailWord_4802062 prefixEnd_4802062 821921979563632048013575 := by
  unfold tailWord_4802062
  simp only [CollatzResearch.WordTrace]
  refine ⟨21893198741119621967634055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116763726619304650494048293 21893198741119621967634055)
  ·
    refine ⟨32839798111679432951451083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21893198741119621967634055 32839798111679432951451083)
    ·
      refine ⟨49259697167519149427176625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32839798111679432951451083 49259697167519149427176625)
      ·
        refine ⟨36944772875639362070382469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49259697167519149427176625 36944772875639362070382469)
        ·
          refine ⟨6927144914182380388196713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36944772875639362070382469 6927144914182380388196713)
          ·
            refine ⟨5195358685636785291147535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6927144914182380388196713 5195358685636785291147535)
            ·
              refine ⟨7793038028455177936721303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5195358685636785291147535 7793038028455177936721303)
              ·
                refine ⟨11689557042682766905081955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7793038028455177936721303 11689557042682766905081955)
                ·
                  refine ⟨17534335564024150357622933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11689557042682766905081955 17534335564024150357622933)
                  ·
                    refine ⟨821921979563632048013575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17534335564024150357622933 821921979563632048013575)
                    ·
                      rfl

theorem cell23_4802062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_4802062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802062 prefixEnd_4802062 := by exact prefixLift 4802062
  have htrace : WordTrace (prefixWord ++ tailWord_4802062) baseStart_4802062 baseEnd_4802062 := by
    simpa [prefixWord, tailWord_4802062, baseEnd_4802062] using wordTrace_append hprefix tailTrace_4802062
  have hstable : (prefixWord ++ tailWord_4802062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802062).length < 2 ^ (prefixWord ++ tailWord_4802062).sum := by decide
  have hdescent : baseEnd_4802062 < baseStart_4802062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802098 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_4802098 : Nat := 118140960795 + 4802098 * 2 ^ 59
def prefixEnd_4802098 : Nat := 4983230072969 + 3 ^ 40 * 4802098 * 2
def baseEnd_4802098 : Nat := 2465784423994458003190559

theorem tailTrace_4802098 : CollatzResearch.WordTrace tailWord_4802098 prefixEnd_4802098 2465784423994458003190559 := by
  unfold tailWord_4802098
  simp only [CollatzResearch.WordTrace]
  refine ⟨43786725739206638472345737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116764601971217702592921965 43786725739206638472345737)
  ·
    refine ⟨32840044304404978854259303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43786725739206638472345737 32840044304404978854259303)
    ·
      refine ⟨49260066456607468281388955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32840044304404978854259303 49260066456607468281388955)
      ·
        refine ⟨73890099684911202422083433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49260066456607468281388955 73890099684911202422083433)
        ·
          refine ⟨55417574763683401816562575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73890099684911202422083433 55417574763683401816562575)
          ·
            refine ⟨83126362145525102724843863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55417574763683401816562575 83126362145525102724843863)
            ·
              refine ⟨124689543218287654087265795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83126362145525102724843863 124689543218287654087265795)
              ·
                refine ⟨187034314827431481130898693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124689543218287654087265795 187034314827431481130898693)
                ·
                  refine ⟨35068934030143402712043505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187034314827431481130898693 35068934030143402712043505)
                  ·
                    refine ⟨26301700522607552034032629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35068934030143402712043505 26301700522607552034032629)
                    ·
                      refine ⟨2465784423994458003190559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26301700522607552034032629 2465784423994458003190559)
                      ·
                        rfl

theorem cell23_4802098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_4802098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802098 prefixEnd_4802098 := by exact prefixLift 4802098
  have htrace : WordTrace (prefixWord ++ tailWord_4802098) baseStart_4802098 baseEnd_4802098 := by
    simpa [prefixWord, tailWord_4802098, baseEnd_4802098] using wordTrace_append hprefix tailTrace_4802098
  have hstable : (prefixWord ++ tailWord_4802098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802098).length < 2 ^ (prefixWord ++ tailWord_4802098).sum := by decide
  have hdescent : baseEnd_4802098 < baseStart_4802098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802119 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_4802119 : Nat := 118140960795 + 4802119 * 2 ^ 59
def prefixEnd_4802119 : Nat := 4983230072969 + 3 ^ 40 * 4802119 * 2
def baseEnd_4802119 : Nat := 2465795207088202421027963

theorem tailTrace_4802119 : CollatzResearch.WordTrace tailWord_4802119 prefixEnd_4802119 2465795207088202421027963 := by
  unfold tailWord_4802119
  simp only [CollatzResearch.WordTrace]
  refine ⟨175147668889750474475897411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116765112593166982983931607 175147668889750474475897411)
  ·
    refine ⟨262721503334625711713846117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175147668889750474475897411 262721503334625711713846117)
    ·
      refine ⟨49260281875242320946346147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262721503334625711713846117 49260281875242320946346147)
      ·
        refine ⟨73890422812863481419519221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49260281875242320946346147 73890422812863481419519221)
        ·
          refine ⟨6927227138705951383079927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73890422812863481419519221 6927227138705951383079927)
          ·
            refine ⟨10390840708058927074619891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6927227138705951383079927 10390840708058927074619891)
            ·
              refine ⟨15586261062088390611929837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10390840708058927074619891 15586261062088390611929837)
              ·
                refine ⟨5844847898283146479473689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15586261062088390611929837 5844847898283146479473689)
                ·
                  refine ⟨4383635923712359859605267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5844847898283146479473689 4383635923712359859605267)
                  ·
                    refine ⟨6575453885568539789407901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4383635923712359859605267 6575453885568539789407901)
                    ·
                      refine ⟨2465795207088202421027963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6575453885568539789407901 2465795207088202421027963)
                      ·
                        rfl

theorem cell23_4802119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_4802119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802119 prefixEnd_4802119 := by exact prefixLift 4802119
  have htrace : WordTrace (prefixWord ++ tailWord_4802119) baseStart_4802119 baseEnd_4802119 := by
    simpa [prefixWord, tailWord_4802119, baseEnd_4802119] using wordTrace_append hprefix tailTrace_4802119
  have hstable : (prefixWord ++ tailWord_4802119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802119).length < 2 ^ (prefixWord ++ tailWord_4802119).sum := by decide
  have hdescent : baseEnd_4802119 < baseStart_4802119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802128 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 5]
def baseStart_4802128 : Nat := 118140960795 + 4802128 * 2 ^ 59
def prefixEnd_4802128 : Nat := 4983230072969 + 3 ^ 40 * 4802128 * 2
def baseEnd_4802128 : Nat := 2465799828414092885815421

theorem tailTrace_4802128 : CollatzResearch.WordTrace tailWord_4802128 prefixEnd_4802128 2465799828414092885815421 := by
  unfold tailWord_4802128
  simp only [CollatzResearch.WordTrace]
  refine ⟨87573998573358934506487519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116765331431145246008650025 87573998573358934506487519)
  ·
    refine ⟨131360997860038401759731279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87573998573358934506487519 131360997860038401759731279)
    ·
      refine ⟨197041496790057602639596919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131360997860038401759731279 197041496790057602639596919)
      ·
        refine ⟨295562245185086403959395379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197041496790057602639596919 295562245185086403959395379)
        ·
          refine ⟨443343367777629605939093069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295562245185086403959395379 443343367777629605939093069)
          ·
            refine ⟨166253762916611102227159901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 443343367777629605939093069 166253762916611102227159901)
            ·
              refine ⟨62345161093729163335184963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166253762916611102227159901 62345161093729163335184963)
              ·
                refine ⟨93517741640593745002777445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62345161093729163335184963 93517741640593745002777445)
                ·
                  refine ⟨17534576557611327188020771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93517741640593745002777445 17534576557611327188020771)
                  ·
                    refine ⟨26301864836416990782031157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17534576557611327188020771 26301864836416990782031157)
                    ·
                      refine ⟨2465799828414092885815421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26301864836416990782031157 2465799828414092885815421)
                      ·
                        rfl

theorem cell23_4802128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_4802128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802128 prefixEnd_4802128 := by exact prefixLift 4802128
  have htrace : WordTrace (prefixWord ++ tailWord_4802128) baseStart_4802128 baseEnd_4802128 := by
    simpa [prefixWord, tailWord_4802128, baseEnd_4802128] using wordTrace_append hprefix tailTrace_4802128
  have hstable : (prefixWord ++ tailWord_4802128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802128).length < 2 ^ (prefixWord ++ tailWord_4802128).sum := by decide
  have hdescent : baseEnd_4802128 < baseStart_4802128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802210 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_4802210 : Nat := 118140960795 + 4802210 * 2 ^ 59
def prefixEnd_4802210 : Nat := 4983230072969 + 3 ^ 40 * 4802210 * 2
def baseEnd_4802210 : Nat := 2465841933827761564990045

theorem tailTrace_4802210 : CollatzResearch.WordTrace tailWord_4802210 prefixEnd_4802210 2465841933827761564990045 := by
  unfold tailWord_4802210
  simp only [CollatzResearch.WordTrace]
  refine ⟨43787746983105199254365021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116767325288280531344973389 43787746983105199254365021)
  ·
    refine ⟨16420405118664449720386883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43787746983105199254365021 16420405118664449720386883)
    ·
      refine ⟨24630607677996674580580325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16420405118664449720386883 24630607677996674580580325)
      ·
        refine ⟨4618238939624376483858811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24630607677996674580580325 4618238939624376483858811)
        ·
          refine ⟨6927358409436564725788217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4618238939624376483858811 6927358409436564725788217)
          ·
            refine ⟨5195518807077423544341163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6927358409436564725788217 5195518807077423544341163)
            ·
              refine ⟨7793278210616135316511745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5195518807077423544341163 7793278210616135316511745)
              ·
                refine ⟨5844958657962101487383809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7793278210616135316511745 5844958657962101487383809)
                ·
                  refine ⟨4383718993471576115537857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5844958657962101487383809 4383718993471576115537857)
                  ·
                    refine ⟨3287789245103682086653393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4383718993471576115537857 3287789245103682086653393)
                    ·
                      refine ⟨2465841933827761564990045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3287789245103682086653393 2465841933827761564990045)
                      ·
                        rfl

theorem cell23_4802210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_4802210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802210 prefixEnd_4802210 := by exact prefixLift 4802210
  have htrace : WordTrace (prefixWord ++ tailWord_4802210) baseStart_4802210 baseEnd_4802210 := by
    simpa [prefixWord, tailWord_4802210, baseEnd_4802210] using wordTrace_append hprefix tailTrace_4802210
  have hstable : (prefixWord ++ tailWord_4802210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802210).length < 2 ^ (prefixWord ++ tailWord_4802210).sum := by decide
  have hdescent : baseEnd_4802210 < baseStart_4802210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802216 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 7]
def baseStart_4802216 : Nat := 118140960795 + 4802216 * 2 ^ 59
def prefixEnd_4802216 : Nat := 4983230072969 + 3 ^ 40 * 4802216 * 2
def baseEnd_4802216 : Nat := 273982779412409837946113

theorem tailTrace_4802216 : CollatzResearch.WordTrace tailWord_4802216 prefixEnd_4802216 273982779412409837946113 := by
  unfold tailWord_4802216
  simp only [CollatzResearch.WordTrace]
  refine ⟨87575603385199530021089251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116767471180266040028119001 87575603385199530021089251)
  ·
    refine ⟨131363405077799295031633877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87575603385199530021089251 131363405077799295031633877)
    ·
      refine ⟨3078829806510920977303919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 131363405077799295031633877 3078829806510920977303919)
      ·
        refine ⟨4618244709766381465955879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3078829806510920977303919 4618244709766381465955879)
        ·
          refine ⟨6927367064649572198933819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4618244709766381465955879 6927367064649572198933819)
          ·
            refine ⟨10391050596974358298400729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6927367064649572198933819 10391050596974358298400729)
            ·
              refine ⟨7793287947730768723800547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10391050596974358298400729 7793287947730768723800547)
              ·
                refine ⟨11689931921596153085700821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7793287947730768723800547 11689931921596153085700821)
                ·
                  refine ⟨273982779412409837946113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11689931921596153085700821 273982779412409837946113)
                  ·
                    rfl

theorem cell23_4802216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 7].length) (baseStart_4802216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802216 prefixEnd_4802216 := by exact prefixLift 4802216
  have htrace : WordTrace (prefixWord ++ tailWord_4802216) baseStart_4802216 baseEnd_4802216 := by
    simpa [prefixWord, tailWord_4802216, baseEnd_4802216] using wordTrace_append hprefix tailTrace_4802216
  have hstable : (prefixWord ++ tailWord_4802216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802216).length < 2 ^ (prefixWord ++ tailWord_4802216).sum := by decide
  have hdescent : baseEnd_4802216 < baseStart_4802216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802276 : List Nat := [2, 3, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_4802276 : Nat := 118140960795 + 4802276 * 2 ^ 59
def prefixEnd_4802276 : Nat := 4983230072969 + 3 ^ 40 * 4802276 * 2
def baseEnd_4802276 : Nat := 821958607850319435588247

theorem tailTrace_4802276 : CollatzResearch.WordTrace tailWord_4802276 prefixEnd_4802276 821958607850319435588247 := by
  unfold tailWord_4802276
  simp only [CollatzResearch.WordTrace]
  refine ⟨87576697575090845144681341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116768930100121126859575121 87576697575090845144681341)
  ·
    refine ⟨32841261590659066929255503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87576697575090845144681341 32841261590659066929255503)
    ·
      refine ⟨49261892385988600393883255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32841261590659066929255503 49261892385988600393883255)
      ·
        refine ⟨73892838578982900590824883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49261892385988600393883255 73892838578982900590824883)
        ·
          refine ⟨110839257868474350886237325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73892838578982900590824883 110839257868474350886237325)
          ·
            refine ⟨41564721700677881582338997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110839257868474350886237325 41564721700677881582338997)
            ·
              refine ⟨3896692659438551398344281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41564721700677881582338997 3896692659438551398344281)
              ·
                refine ⟨2922519494578913548758211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3896692659438551398344281 2922519494578913548758211)
                ·
                  refine ⟨4383779241868370323137317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2922519494578913548758211 4383779241868370323137317)
                  ·
                    refine ⟨821958607850319435588247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4383779241868370323137317 821958607850319435588247)
                    ·
                      rfl

theorem cell23_4802276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_4802276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802276 prefixEnd_4802276 := by exact prefixLift 4802276
  have htrace : WordTrace (prefixWord ++ tailWord_4802276) baseStart_4802276 baseEnd_4802276 := by
    simpa [prefixWord, tailWord_4802276, baseEnd_4802276] using wordTrace_append hprefix tailTrace_4802276
  have hstable : (prefixWord ++ tailWord_4802276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802276).length < 2 ^ (prefixWord ++ tailWord_4802276).sum := by decide
  have hdescent : baseEnd_4802276 < baseStart_4802276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802289 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 6]
def baseStart_4802289 : Nat := 118140960795 + 4802289 * 2 ^ 59
def prefixEnd_4802289 : Nat := 4983230072969 + 3 ^ 40 * 4802289 * 2
def baseEnd_4802289 : Nat := 273986944311051861766909

theorem tailTrace_4802289 : CollatzResearch.WordTrace tailWord_4802289 prefixEnd_4802289 273986944311051861766909 := by
  unfold tailWord_4802289
  simp only [CollatzResearch.WordTrace]
  refine ⟨175153869299134593509585921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116769246199423062339723947 175153869299134593509585921)
  ·
    refine ⟨131365401974350945132189441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175153869299134593509585921 131365401974350945132189441)
    ·
      refine ⟨98524051480763208849142081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131365401974350945132189441 98524051480763208849142081)
      ·
        refine ⟨73893038610572406636856561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98524051480763208849142081 73893038610572406636856561)
        ·
          refine ⟨55419778957929304977642421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73893038610572406636856561 55419778957929304977642421)
          ·
            refine ⟨5195604277305872341653977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55419778957929304977642421 5195604277305872341653977)
            ·
              refine ⟨3896703207979404256240483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5195604277305872341653977 3896703207979404256240483)
              ·
                refine ⟨5845054811969106384360725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3896703207979404256240483 5845054811969106384360725)
                ·
                  refine ⟨273986944311051861766909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5845054811969106384360725 273986944311051861766909)
                  ·
                    rfl

theorem cell23_4802289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 6].length) (baseStart_4802289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802289 prefixEnd_4802289 := by exact prefixLift 4802289
  have htrace : WordTrace (prefixWord ++ tailWord_4802289) baseStart_4802289 baseEnd_4802289 := by
    simpa [prefixWord, tailWord_4802289, baseEnd_4802289] using wordTrace_append hprefix tailTrace_4802289
  have hstable : (prefixWord ++ tailWord_4802289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802289).length < 2 ^ (prefixWord ++ tailWord_4802289).sum := by decide
  have hdescent : baseEnd_4802289 < baseStart_4802289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802315 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 3, 6]
def baseStart_4802315 : Nat := 118140960795 + 4802315 * 2 ^ 59
def prefixEnd_4802315 : Nat := 4983230072969 + 3 ^ 40 * 4802315 * 2
def baseEnd_4802315 : Nat := 821965283098827884725687

theorem tailTrace_4802315 : CollatzResearch.WordTrace tailWord_4802315 prefixEnd_4802315 821965283098827884725687 := by
  unfold tailWord_4802315
  simp only [CollatzResearch.WordTrace]
  refine ⟨175154817597040399950032399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116769878398026933300021599 175154817597040399950032399)
  ·
    refine ⟨262732226395560599925048599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175154817597040399950032399 262732226395560599925048599)
    ·
      refine ⟨394098339593340899887572899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262732226395560599925048599 394098339593340899887572899)
      ·
        refine ⟨591147509390011349831359349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394098339593340899887572899 591147509390011349831359349)
        ·
          refine ⟨55420079005313564046689939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 591147509390011349831359349 55420079005313564046689939)
          ·
            refine ⟨83130118507970346070034909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55420079005313564046689939 83130118507970346070034909)
            ·
              refine ⟨31173794440488879776263091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83130118507970346070034909 31173794440488879776263091)
              ·
                refine ⟨46760691660733319664394637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31173794440488879776263091 46760691660733319664394637)
                ·
                  refine ⟨17535259372774994874147989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46760691660733319664394637 17535259372774994874147989)
                  ·
                    refine ⟨821965283098827884725687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17535259372774994874147989 821965283098827884725687)
                    ·
                      rfl

theorem cell23_4802315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 6].length) (baseStart_4802315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802315 prefixEnd_4802315 := by exact prefixLift 4802315
  have htrace : WordTrace (prefixWord ++ tailWord_4802315) baseStart_4802315 baseEnd_4802315 := by
    simpa [prefixWord, tailWord_4802315, baseEnd_4802315] using wordTrace_append hprefix tailTrace_4802315
  have hstable : (prefixWord ++ tailWord_4802315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802315).length < 2 ^ (prefixWord ++ tailWord_4802315).sum := by decide
  have hdescent : baseEnd_4802315 < baseStart_4802315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802373 : List Nat := [1, 3, 1, 1, 1, 2, 6, 3, 1, 2, 2]
def baseStart_4802373 : Nat := 118140960795 + 4802373 * 2 ^ 59
def prefixEnd_4802373 : Nat := 4983230072969 + 3 ^ 40 * 4802373 * 2
def baseEnd_4802373 : Nat := 2465925631174444427251795

theorem tailTrace_4802373 : CollatzResearch.WordTrace tailWord_4802373 prefixEnd_4802373 2465925631174444427251795 := by
  unfold tailWord_4802373
  simp only [CollatzResearch.WordTrace]
  refine ⟨175156933030830275855643773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116771288687220183903762515 175156933030830275855643773)
  ·
    refine ⟨65683849886561353445866415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175156933030830275855643773 65683849886561353445866415)
    ·
      refine ⟨98525774829842030168799623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65683849886561353445866415 98525774829842030168799623)
      ·
        refine ⟨147788662244763045253199435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98525774829842030168799623 147788662244763045253199435)
        ·
          refine ⟨221682993367144567879799153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147788662244763045253199435 221682993367144567879799153)
          ·
            refine ⟨166262245025358425909849365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221682993367144567879799153 166262245025358425909849365)
            ·
              refine ⟨7793542735563676214524189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166262245025358425909849365 7793542735563676214524189)
              ·
                refine ⟨2922578525836378580446571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7793542735563676214524189 2922578525836378580446571)
                ·
                  refine ⟨4383867788754567870669857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2922578525836378580446571 4383867788754567870669857)
                  ·
                    refine ⟨3287900841565925903002393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4383867788754567870669857 3287900841565925903002393)
                    ·
                      refine ⟨2465925631174444427251795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3287900841565925903002393 2465925631174444427251795)
                      ·
                        rfl

theorem cell23_4802373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 1, 2, 2].length) (baseStart_4802373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802373 prefixEnd_4802373 := by exact prefixLift 4802373
  have htrace : WordTrace (prefixWord ++ tailWord_4802373) baseStart_4802373 baseEnd_4802373 := by
    simpa [prefixWord, tailWord_4802373, baseEnd_4802373] using wordTrace_append hprefix tailTrace_4802373
  have hstable : (prefixWord ++ tailWord_4802373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802373).length < 2 ^ (prefixWord ++ tailWord_4802373).sum := by decide
  have hdescent : baseEnd_4802373 < baseStart_4802373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802376 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 1, 2, 3]
def baseStart_4802376 : Nat := 118140960795 + 4802376 * 2 ^ 59
def prefixEnd_4802376 : Nat := 4983230072969 + 3 ^ 40 * 4802376 * 2
def baseEnd_4802376 : Nat := 2465927171616407915514281

theorem tailTrace_4802376 : CollatzResearch.WordTrace tailWord_4802376 prefixEnd_4802376 2465927171616407915514281 := by
  unfold tailWord_4802376
  simp only [CollatzResearch.WordTrace]
  refine ⟨87578521224909703684001491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116771361633212938245335321 87578521224909703684001491)
  ·
    refine ⟨131367781837364555526002237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87578521224909703684001491 131367781837364555526002237)
    ·
      refine ⟨49262918189011708322250839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131367781837364555526002237 49262918189011708322250839)
      ·
        refine ⟨73894377283517562483376259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49262918189011708322250839 73894377283517562483376259)
        ·
          refine ⟨110841565925276343725064389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73894377283517562483376259 110841565925276343725064389)
          ·
            refine ⟨20782793610989314448449573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110841565925276343725064389 20782793610989314448449573)
            ·
              refine ⟨3896773802060496459084295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20782793610989314448449573 3896773802060496459084295)
              ·
                refine ⟨5845160703090744688626443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3896773802060496459084295 5845160703090744688626443)
                ·
                  refine ⟨8767741054636117032939665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5845160703090744688626443 8767741054636117032939665)
                  ·
                    refine ⟨6575805790977087774704749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8767741054636117032939665 6575805790977087774704749)
                    ·
                      refine ⟨2465927171616407915514281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6575805790977087774704749 2465927171616407915514281)
                      ·
                        rfl

theorem cell23_4802376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_4802376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802376 prefixEnd_4802376 := by exact prefixLift 4802376
  have htrace : WordTrace (prefixWord ++ tailWord_4802376) baseStart_4802376 baseEnd_4802376 := by
    simpa [prefixWord, tailWord_4802376, baseEnd_4802376] using wordTrace_append hprefix tailTrace_4802376
  have hstable : (prefixWord ++ tailWord_4802376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802376).length < 2 ^ (prefixWord ++ tailWord_4802376).sum := by decide
  have hdescent : baseEnd_4802376 < baseStart_4802376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802429 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 3, 4, 2]
def baseStart_4802429 : Nat := 118140960795 + 4802429 * 2 ^ 59
def prefixEnd_4802429 : Nat := 4983230072969 + 3 ^ 40 * 4802429 * 2
def baseEnd_4802429 : Nat := 2465954386091096208151537

theorem tailTrace_4802429 : CollatzResearch.WordTrace tailWord_4802429 prefixEnd_4802429 2465954386091096208151537 := by
  unfold tailWord_4802429
  simp only [CollatzResearch.WordTrace]
  refine ⟨175158975518627397419682341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116772650345751598279788227 175158975518627397419682341)
  ·
    refine ⟨32842307909742637016190439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175158975518627397419682341 32842307909742637016190439)
    ·
      refine ⟨49263461864613955524285659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32842307909742637016190439 49263461864613955524285659)
      ·
        refine ⟨73895192796920933286428489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49263461864613955524285659 73895192796920933286428489)
        ·
          refine ⟨55421394597690699964821367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73895192796920933286428489 55421394597690699964821367)
          ·
            refine ⟨83132091896536049947232051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55421394597690699964821367 83132091896536049947232051)
            ·
              refine ⟨124698137844804074920848077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83132091896536049947232051 124698137844804074920848077)
              ·
                refine ⟨46761801691801528095318029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124698137844804074920848077 46761801691801528095318029)
                ·
                  refine ⟨17535675634425573035744261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46761801691801528095318029 17535675634425573035744261)
                  ·
                    refine ⟨3287939181454794944202049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17535675634425573035744261 3287939181454794944202049)
                    ·
                      refine ⟨2465954386091096208151537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3287939181454794944202049 2465954386091096208151537)
                      ·
                        rfl

theorem cell23_4802429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_4802429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802429 prefixEnd_4802429 := by exact prefixLift 4802429
  have htrace : WordTrace (prefixWord ++ tailWord_4802429) baseStart_4802429 baseEnd_4802429 := by
    simpa [prefixWord, tailWord_4802429, baseEnd_4802429] using wordTrace_append hprefix tailTrace_4802429
  have hstable : (prefixWord ++ tailWord_4802429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802429).length < 2 ^ (prefixWord ++ tailWord_4802429).sum := by decide
  have hdescent : baseEnd_4802429 < baseStart_4802429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802432 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 5]
def baseStart_4802432 : Nat := 118140960795 + 4802432 * 2 ^ 59
def prefixEnd_4802432 : Nat := 4983230072969 + 3 ^ 40 * 4802432 * 2
def baseEnd_4802432 : Nat := 2465955926533059696414023

theorem tailTrace_4802432 : CollatzResearch.WordTrace tailWord_4802432 prefixEnd_4802432 2465955926533059696414023 := by
  unfold tailWord_4802432
  simp only [CollatzResearch.WordTrace]
  refine ⟨87579542468808264466020775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116772723291744352621361033 87579542468808264466020775)
  ·
    refine ⟨131369313703212396699031163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87579542468808264466020775 131369313703212396699031163)
    ·
      refine ⟨197053970554818595048546745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131369313703212396699031163 197053970554818595048546745)
      ·
        refine ⟨147790477916113946286410059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197053970554818595048546745 147790477916113946286410059)
        ·
          refine ⟨221685716874170919429615089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147790477916113946286410059 221685716874170919429615089)
          ·
            refine ⟨166264287655628189572211317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221685716874170919429615089 166264287655628189572211317)
            ·
              refine ⟨15587276967715142772394811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166264287655628189572211317 15587276967715142772394811)
              ·
                refine ⟨23380915451572714158592217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15587276967715142772394811 23380915451572714158592217)
                ·
                  refine ⟨17535686588679535618944163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23380915451572714158592217 17535686588679535618944163)
                  ·
                    refine ⟨26303529883019303428416245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17535686588679535618944163 26303529883019303428416245)
                    ·
                      refine ⟨2465955926533059696414023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26303529883019303428416245 2465955926533059696414023)
                      ·
                        rfl

theorem cell23_4802432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_4802432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802432 prefixEnd_4802432 := by exact prefixLift 4802432
  have htrace : WordTrace (prefixWord ++ tailWord_4802432) baseStart_4802432 baseEnd_4802432 := by
    simpa [prefixWord, tailWord_4802432, baseEnd_4802432] using wordTrace_append hprefix tailTrace_4802432
  have hstable : (prefixWord ++ tailWord_4802432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802432).length < 2 ^ (prefixWord ++ tailWord_4802432).sum := by decide
  have hdescent : baseEnd_4802432 < baseStart_4802432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802482 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_4802482 : Nat := 118140960795 + 4802482 * 2 ^ 59
def prefixEnd_4802482 : Nat := 4983230072969 + 3 ^ 40 * 4802482 * 2
def baseEnd_4802482 : Nat := 821993866855261500262931

theorem tailTrace_4802482 : CollatzResearch.WordTrace tailWord_4802482 prefixEnd_4802482 821993866855261500262931 := by
  unfold tailWord_4802482
  simp only [CollatzResearch.WordTrace]
  refine ⟨43790227146858846867840425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116773939058290258314241133 43790227146858846867840425)
  ·
    refine ⟨32842670360144135150880319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43790227146858846867840425 32842670360144135150880319)
    ·
      refine ⟨49264005540216202726320479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32842670360144135150880319 49264005540216202726320479)
      ·
        refine ⟨73896008310324304089480719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49264005540216202726320479 73896008310324304089480719)
        ·
          refine ⟨110844012465486456134221079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73896008310324304089480719 110844012465486456134221079)
          ·
            refine ⟨166266018698229684201331619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110844012465486456134221079 166266018698229684201331619)
            ·
              refine ⟨249399028047344526301997429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166266018698229684201331619 249399028047344526301997429)
              ·
                refine ⟨23381158879438549340812259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249399028047344526301997429 23381158879438549340812259)
                ·
                  refine ⟨35071738319157824011218389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23381158879438549340812259 35071738319157824011218389)
                  ·
                    refine ⟨821993866855261500262931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35071738319157824011218389 821993866855261500262931)
                    ·
                      rfl

theorem cell23_4802482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_4802482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802482 prefixEnd_4802482 := by exact prefixLift 4802482
  have htrace : WordTrace (prefixWord ++ tailWord_4802482) baseStart_4802482 baseEnd_4802482 := by
    simpa [prefixWord, tailWord_4802482, baseEnd_4802482] using wordTrace_append hprefix tailTrace_4802482
  have hstable : (prefixWord ++ tailWord_4802482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802482).length < 2 ^ (prefixWord ++ tailWord_4802482).sum := by decide
  have hdescent : baseEnd_4802482 < baseStart_4802482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802529 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 5, 4]
def baseStart_4802529 : Nat := 118140960795 + 4802529 * 2 ^ 59
def prefixEnd_4802529 : Nat := 4983230072969 + 3 ^ 40 * 4802529 * 2
def baseEnd_4802529 : Nat := 822001911385515272300359

theorem tailTrace_4802529 : CollatzResearch.WordTrace tailWord_4802529 prefixEnd_4802529 822001911385515272300359 := by
  unfold tailWord_4802529
  simp only [CollatzResearch.WordTrace]
  refine ⟨175162622818265114498322641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116775081878843409665548427 175162622818265114498322641)
  ·
    refine ⟨131371967113698835873741981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175162622818265114498322641 131371967113698835873741981)
    ·
      refine ⟨49264487667637063452653243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131371967113698835873741981 49264487667637063452653243)
      ·
        refine ⟨73896731501455595178979865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49264487667637063452653243 73896731501455595178979865)
        ·
          refine ⟨55422548626091696384234899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73896731501455595178979865 55422548626091696384234899)
          ·
            refine ⟨83133822939137544576352349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55422548626091696384234899 83133822939137544576352349)
            ·
              refine ⟨31175183602176579216132131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83133822939137544576352349 31175183602176579216132131)
              ·
                refine ⟨46762775403264868824198197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31175183602176579216132131 46762775403264868824198197)
                ·
                  refine ⟨4384010194056081452268581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46762775403264868824198197 4384010194056081452268581)
                  ·
                    refine ⟨822001911385515272300359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4384010194056081452268581 822001911385515272300359)
                    ·
                      rfl

theorem cell23_4802529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_4802529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802529 prefixEnd_4802529 := by exact prefixLift 4802529
  have htrace : WordTrace (prefixWord ++ tailWord_4802529) baseStart_4802529 baseEnd_4802529 := by
    simpa [prefixWord, tailWord_4802529, baseEnd_4802529] using wordTrace_append hprefix tailTrace_4802529
  have hstable : (prefixWord ++ tailWord_4802529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802529).length < 2 ^ (prefixWord ++ tailWord_4802529).sum := by decide
  have hdescent : baseEnd_4802529 < baseStart_4802529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802603 : List Nat := [1, 1, 1, 1, 2, 1, 4, 7, 1, 1, 3]
def baseStart_4802603 : Nat := 118140960795 + 4802603 * 2 ^ 59
def prefixEnd_4802603 : Nat := 4983230072969 + 3 ^ 40 * 4802603 * 2
def baseEnd_4802603 : Nat := 2466043731724978527375737

theorem tailTrace_4802603 : CollatzResearch.WordTrace tailWord_4802603 prefixEnd_4802603 2466043731724978527375737 := by
  unfold tailWord_4802603
  simp only [CollatzResearch.WordTrace]
  refine ⟨175165321819997025136516463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116776881213331350091010975 175165321819997025136516463)
  ·
    refine ⟨262747982729995537704774695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175165321819997025136516463 262747982729995537704774695)
    ·
      refine ⟨394121974094993306557162043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262747982729995537704774695 394121974094993306557162043)
      ·
        refine ⟨591182961142489959835743065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394121974094993306557162043 591182961142489959835743065)
        ·
          refine ⟨443387220856867469876807299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591182961142489959835743065 443387220856867469876807299)
          ·
            refine ⟨665080831285301204815210949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443387220856867469876807299 665080831285301204815210949)
            ·
              refine ⟨124702655865993975902852053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 665080831285301204815210949 124702655865993975902852053)
              ·
                refine ⟨2922718496859233810223095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 124702655865993975902852053 2922718496859233810223095)
                ·
                  refine ⟨4384077745288850715334643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2922718496859233810223095 4384077745288850715334643)
                  ·
                    refine ⟨6576116617933276073001965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4384077745288850715334643 6576116617933276073001965)
                    ·
                      refine ⟨2466043731724978527375737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6576116617933276073001965 2466043731724978527375737)
                      ·
                        rfl

theorem cell23_4802603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 1, 1, 3].length) (baseStart_4802603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802603 prefixEnd_4802603 := by exact prefixLift 4802603
  have htrace : WordTrace (prefixWord ++ tailWord_4802603) baseStart_4802603 baseEnd_4802603 := by
    simpa [prefixWord, tailWord_4802603, baseEnd_4802603] using wordTrace_append hprefix tailTrace_4802603
  have hstable : (prefixWord ++ tailWord_4802603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802603).length < 2 ^ (prefixWord ++ tailWord_4802603).sum := by decide
  have hdescent : baseEnd_4802603 < baseStart_4802603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802629 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 2, 6, 3]
def baseStart_4802629 : Nat := 118140960795 + 4802629 * 2 ^ 59
def prefixEnd_4802629 : Nat := 4983230072969 + 3 ^ 40 * 4802629 * 2
def baseEnd_4802629 : Nat := 2466057082221995425650617

theorem tailTrace_4802629 : CollatzResearch.WordTrace tailWord_4802629 prefixEnd_4802629 2466057082221995425650617 := by
  unfold tailWord_4802629
  simp only [CollatzResearch.WordTrace]
  refine ⟨175166270117902831576962941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116777513411935221051308627 175166270117902831576962941)
  ·
    refine ⟨65687351294213561841361103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175166270117902831576962941 65687351294213561841361103)
    ·
      refine ⟨98531026941320342762041655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65687351294213561841361103 98531026941320342762041655)
      ·
        refine ⟨147796540411980514143062483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98531026941320342762041655 147796540411980514143062483)
        ·
          refine ⟨221694810617970771214593725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147796540411980514143062483 221694810617970771214593725)
          ·
            refine ⟨83135553981739039205472647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221694810617970771214593725 83135553981739039205472647)
            ·
              refine ⟨124703330972608558808208971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83135553981739039205472647 124703330972608558808208971)
              ·
                refine ⟨187054996458912838212313457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124703330972608558808208971 187054996458912838212313457)
                ·
                  refine ⟨140291247344184628659235093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187054996458912838212313457 140291247344184628659235093)
                  ·
                    refine ⟨6576152219258654468401645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 140291247344184628659235093 6576152219258654468401645)
                    ·
                      refine ⟨2466057082221995425650617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6576152219258654468401645 2466057082221995425650617)
                      ·
                        rfl

theorem cell23_4802629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_4802629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802629 prefixEnd_4802629 := by exact prefixLift 4802629
  have htrace : WordTrace (prefixWord ++ tailWord_4802629) baseStart_4802629 baseEnd_4802629 := by
    simpa [prefixWord, tailWord_4802629, baseEnd_4802629] using wordTrace_append hprefix tailTrace_4802629
  have hstable : (prefixWord ++ tailWord_4802629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802629).length < 2 ^ (prefixWord ++ tailWord_4802629).sum := by decide
  have hdescent : baseEnd_4802629 < baseStart_4802629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802630 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_4802630 : Nat := 118140960795 + 4802630 * 2 ^ 59
def prefixEnd_4802630 : Nat := 4983230072969 + 3 ^ 40 * 4802630 * 2
def baseEnd_4802630 : Nat := 2466057595702649921738113

theorem tailTrace_4802630 : CollatzResearch.WordTrace tailWord_4802630 prefixEnd_4802630 2466057595702649921738113 := by
  unfold tailWord_4802630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5473947080965600273367167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116777537727266139165166229 5473947080965600273367167)
  ·
    refine ⟨8210920621448400410050751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5473947080965600273367167 8210920621448400410050751)
    ·
      refine ⟨12316380932172600615076127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8210920621448400410050751 12316380932172600615076127)
      ·
        refine ⟨18474571398258900922614191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12316380932172600615076127 18474571398258900922614191)
        ·
          refine ⟨27711857097388351383921287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18474571398258900922614191 27711857097388351383921287)
          ·
            refine ⟨41567785646082527075881931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27711857097388351383921287 41567785646082527075881931)
            ·
              refine ⟨62351678469123790613822897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41567785646082527075881931 62351678469123790613822897)
              ·
                refine ⟨46763758851842842960367173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62351678469123790613822897 46763758851842842960367173)
                ·
                  refine ⟨8768204784720533055068845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46763758851842842960367173 8768204784720533055068845)
                  ·
                    refine ⟨3288076794270199895650817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8768204784720533055068845 3288076794270199895650817)
                    ·
                      refine ⟨2466057595702649921738113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288076794270199895650817 2466057595702649921738113)
                      ·
                        rfl

theorem cell23_4802630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_4802630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802630 prefixEnd_4802630 := by exact prefixLift 4802630
  have htrace : WordTrace (prefixWord ++ tailWord_4802630) baseStart_4802630 baseEnd_4802630 := by
    simpa [prefixWord, tailWord_4802630, baseEnd_4802630] using wordTrace_append hprefix tailTrace_4802630
  have hstable : (prefixWord ++ tailWord_4802630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802630).length < 2 ^ (prefixWord ++ tailWord_4802630).sum := by decide
  have hdescent : baseEnd_4802630 < baseStart_4802630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802653 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4802653 : Nat := 118140960795 + 4802653 * 2 ^ 59
def prefixEnd_4802653 : Nat := 4983230072969 + 3 ^ 40 * 4802653 * 2
def baseEnd_4802653 : Nat := 822023135252567777250169

theorem tailTrace_4802653 : CollatzResearch.WordTrace tailWord_4802653 prefixEnd_4802653 822023135252567777250169 := by
  unfold tailWord_4802653
  simp only [CollatzResearch.WordTrace]
  refine ⟨175167145469815883675836613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116778096979877255783891075 175167145469815883675836613)
  ·
    refine ⟨32843839775590478189219365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175167145469815883675836613 32843839775590478189219365)
    ·
      refine ⟨6158219957923214660478631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32843839775590478189219365 6158219957923214660478631)
      ·
        refine ⟨9237329936884821990717947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6158219957923214660478631 9237329936884821990717947)
        ·
          refine ⟨13855994905327232986076921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9237329936884821990717947 13855994905327232986076921)
          ·
            refine ⟨10391996178995424739557691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13855994905327232986076921 10391996178995424739557691)
            ·
              refine ⟨15587994268493137109336537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10391996178995424739557691 15587994268493137109336537)
              ·
                refine ⟨11690995701369852832002403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15587994268493137109336537 11690995701369852832002403)
                ·
                  refine ⟨17536493552054779248003605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11690995701369852832002403 17536493552054779248003605)
                  ·
                    refine ⟨822023135252567777250169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17536493552054779248003605 822023135252567777250169)
                    ·
                      rfl

theorem cell23_4802653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4802653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802653 prefixEnd_4802653 := by exact prefixLift 4802653
  have htrace : WordTrace (prefixWord ++ tailWord_4802653) baseStart_4802653 baseEnd_4802653 := by
    simpa [prefixWord, tailWord_4802653, baseEnd_4802653] using wordTrace_append hprefix tailTrace_4802653
  have hstable : (prefixWord ++ tailWord_4802653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802653).length < 2 ^ (prefixWord ++ tailWord_4802653).sum := by decide
  have hdescent : baseEnd_4802653 < baseStart_4802653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802656 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 4]
def baseStart_4802656 : Nat := 118140960795 + 4802656 * 2 ^ 59
def prefixEnd_4802656 : Nat := 4983230072969 + 3 ^ 40 * 4802656 * 2
def baseEnd_4802656 : Nat := 2466070946199666820012993

theorem tailTrace_4802656 : CollatzResearch.WordTrace tailWord_4802656 prefixEnd_4802656 2466070946199666820012993 := by
  unfold tailWord_4802656
  simp only [CollatzResearch.WordTrace]
  refine ⟨87583627444402507594097911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116778169925870010125463881 87583627444402507594097911)
  ·
    refine ⟨131375441166603761391146867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87583627444402507594097911 131375441166603761391146867)
    ·
      refine ⟨197063161749905642086720301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131375441166603761391146867 197063161749905642086720301)
      ·
        refine ⟨73898685656214615782520113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197063161749905642086720301 73898685656214615782520113)
        ·
          refine ⟨55424014242160961836890085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73898685656214615782520113 55424014242160961836890085)
          ·
            refine ⟨10392002670405180344416891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55424014242160961836890085 10392002670405180344416891)
            ·
              refine ⟨15588004005607770516625337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10392002670405180344416891 15588004005607770516625337)
              ·
                refine ⟨11691003004205827887469003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15588004005607770516625337 11691003004205827887469003)
                ·
                  refine ⟨17536504506308741831203505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11691003004205827887469003 17536504506308741831203505)
                  ·
                    refine ⟨13152378379731556373402629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17536504506308741831203505 13152378379731556373402629)
                    ·
                      refine ⟨2466070946199666820012993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13152378379731556373402629 2466070946199666820012993)
                      ·
                        rfl

theorem cell23_4802656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_4802656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802656 prefixEnd_4802656 := by exact prefixLift 4802656
  have htrace : WordTrace (prefixWord ++ tailWord_4802656) baseStart_4802656 baseEnd_4802656 := by
    simpa [prefixWord, tailWord_4802656, baseEnd_4802656] using wordTrace_append hprefix tailTrace_4802656
  have hstable : (prefixWord ++ tailWord_4802656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802656).length < 2 ^ (prefixWord ++ tailWord_4802656).sum := by decide
  have hdescent : baseEnd_4802656 < baseStart_4802656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802666 : List Nat := [3, 1, 3, 2, 4, 10]
def baseStart_4802666 : Nat := 118140960795 + 4802666 * 2 ^ 59
def prefixEnd_4802666 : Nat := 4983230072969 + 3 ^ 40 * 4802666 * 2
def baseEnd_4802666 : Nat := 10148461238708690456329

theorem tailTrace_4802666 : CollatzResearch.WordTrace tailWord_4802666 prefixEnd_4802666 10148461238708690456329 := by
  unfold tailWord_4802666
  simp only [CollatzResearch.WordTrace]
  refine ⟨43791904904692196724014963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116778413079179191264039901 43791904904692196724014963)
  ·
    refine ⟨65687857357038295086022445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43791904904692196724014963 65687857357038295086022445)
    ·
      refine ⟨24632946508889360657258417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65687857357038295086022445 24632946508889360657258417)
      ·
        refine ⟨18474709881667020492943813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24632946508889360657258417 18474709881667020492943813)
        ·
          refine ⟨3464008102812566342426965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18474709881667020492943813 3464008102812566342426965)
          ·
            refine ⟨10148461238708690456329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3464008102812566342426965 10148461238708690456329)
            ·
              rfl

theorem cell23_4802666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 10].length) (baseStart_4802666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802666 prefixEnd_4802666 := by exact prefixLift 4802666
  have htrace : WordTrace (prefixWord ++ tailWord_4802666) baseStart_4802666 baseEnd_4802666 := by
    simpa [prefixWord, tailWord_4802666, baseEnd_4802666] using wordTrace_append hprefix tailTrace_4802666
  have hstable : (prefixWord ++ tailWord_4802666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802666).length < 2 ^ (prefixWord ++ tailWord_4802666).sum := by decide
  have hdescent : baseEnd_4802666 < baseStart_4802666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802679 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 2, 7]
def baseStart_4802679 : Nat := 118140960795 + 4802679 * 2 ^ 59
def prefixEnd_4802679 : Nat := 4983230072969 + 3 ^ 40 * 4802679 * 2
def baseEnd_4802679 : Nat := 822027585418240076675129

theorem tailTrace_4802679 : CollatzResearch.WordTrace tailWord_4802679 prefixEnd_4802679 822027585418240076675129 := by
  unfold tailWord_4802679
  simp only [CollatzResearch.WordTrace]
  refine ⟨175168093767721690116283091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116778729178481126744188727 175168093767721690116283091)
  ·
    refine ⟨262752140651582535174424637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175168093767721690116283091 262752140651582535174424637)
    ·
      refine ⟨98532052744343450690409239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262752140651582535174424637 98532052744343450690409239)
      ·
        refine ⟨147798079116515176035613859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98532052744343450690409239 147798079116515176035613859)
        ·
          refine ⟨221697118674772764053420789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147798079116515176035613859 221697118674772764053420789)
          ·
            refine ⟨20784104875759946630008199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221697118674772764053420789 20784104875759946630008199)
            ·
              refine ⟨31176157313639919945012299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20784104875759946630008199 31176157313639919945012299)
              ·
                refine ⟨46764235970459879917518449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31176157313639919945012299 46764235970459879917518449)
                ·
                  refine ⟨35073176977844909938138837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46764235970459879917518449 35073176977844909938138837)
                  ·
                    refine ⟨822027585418240076675129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35073176977844909938138837 822027585418240076675129)
                    ·
                      rfl

theorem cell23_4802679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_4802679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802679 prefixEnd_4802679 := by exact prefixLift 4802679
  have htrace : WordTrace (prefixWord ++ tailWord_4802679) baseStart_4802679 baseEnd_4802679 := by
    simpa [prefixWord, tailWord_4802679, baseEnd_4802679] using wordTrace_append hprefix tailTrace_4802679
  have hstable : (prefixWord ++ tailWord_4802679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802679).length < 2 ^ (prefixWord ++ tailWord_4802679).sum := by decide
  have hdescent : baseEnd_4802679 < baseStart_4802679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802693 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 1, 3, 3]
def baseStart_4802693 : Nat := 118140960795 + 4802693 * 2 ^ 59
def prefixEnd_4802693 : Nat := 4983230072969 + 3 ^ 40 * 4802693 * 2
def baseEnd_4802693 : Nat := 2466089944983883175250323

theorem tailTrace_4802693 : CollatzResearch.WordTrace tailWord_4802693 prefixEnd_4802693 2466089944983883175250323 := by
  unfold tailWord_4802693
  simp only [CollatzResearch.WordTrace]
  refine ⟨175168604389670970507292733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116779069593113980338195155 175168604389670970507292733)
  ·
    refine ⟨65688226646126613940234775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175168604389670970507292733 65688226646126613940234775)
    ·
      refine ⟨98532339969189920910352163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65688226646126613940234775 98532339969189920910352163)
      ·
        refine ⟨147798509953784881365528245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98532339969189920910352163 147798509953784881365528245)
        ·
          refine ⟨13856110308167332628018273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147798509953784881365528245 13856110308167332628018273)
          ·
            refine ⟨10392082731125499471013705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13856110308167332628018273 10392082731125499471013705)
            ·
              refine ⟨7794062048344124603260279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10392082731125499471013705 7794062048344124603260279)
              ·
                refine ⟨11691093072516186904890419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7794062048344124603260279 11691093072516186904890419)
                ·
                  refine ⟨17536639608774280357335629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11691093072516186904890419 17536639608774280357335629)
                  ·
                    refine ⟨6576239853290355134000861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17536639608774280357335629 6576239853290355134000861)
                    ·
                      refine ⟨2466089944983883175250323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6576239853290355134000861 2466089944983883175250323)
                      ·
                        rfl

theorem cell23_4802693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_4802693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802693 prefixEnd_4802693 := by exact prefixLift 4802693
  have htrace : WordTrace (prefixWord ++ tailWord_4802693) baseStart_4802693 baseEnd_4802693 := by
    simpa [prefixWord, tailWord_4802693, baseEnd_4802693] using wordTrace_append hprefix tailTrace_4802693
  have hstable : (prefixWord ++ tailWord_4802693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802693).length < 2 ^ (prefixWord ++ tailWord_4802693).sum := by decide
  have hdescent : baseEnd_4802693 < baseStart_4802693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802706 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4802706 : Nat := 118140960795 + 4802706 * 2 ^ 59
def prefixEnd_4802706 : Nat := 4983230072969 + 3 ^ 40 * 4802706 * 2
def baseEnd_4802706 : Nat := 2466096620232391624387763

theorem tailTrace_4802706 : CollatzResearch.WordTrace tailWord_4802706 prefixEnd_4802706 2466096620232391624387763 := by
  unfold tailWord_4802706
  simp only [CollatzResearch.WordTrace]
  refine ⟨43792269634655968431878993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116779385692415915818343981 43792269634655968431878993)
  ·
    refine ⟨32844202225991976323909245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43792269634655968431878993 32844202225991976323909245)
    ·
      refine ⟨12316575834746991121465967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32844202225991976323909245 12316575834746991121465967)
      ·
        refine ⟨18474863752120486682198951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12316575834746991121465967 18474863752120486682198951)
        ·
          refine ⟨27712295628180730023298427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18474863752120486682198951 27712295628180730023298427)
          ·
            refine ⟨41568443442271095034947641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27712295628180730023298427 41568443442271095034947641)
            ·
              refine ⟨31176332581703321276210731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41568443442271095034947641 31176332581703321276210731)
              ·
                refine ⟨46764498872554981914316097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31176332581703321276210731 46764498872554981914316097)
                ·
                  refine ⟨35073374154416236435737073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46764498872554981914316097 35073374154416236435737073)
                  ·
                    refine ⟨26305030615812177326802805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35073374154416236435737073 26305030615812177326802805)
                    ·
                      refine ⟨2466096620232391624387763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26305030615812177326802805 2466096620232391624387763)
                      ·
                        rfl

theorem cell23_4802706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4802706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802706 prefixEnd_4802706 := by exact prefixLift 4802706
  have htrace : WordTrace (prefixWord ++ tailWord_4802706) baseStart_4802706 baseEnd_4802706 := by
    simpa [prefixWord, tailWord_4802706, baseEnd_4802706] using wordTrace_append hprefix tailTrace_4802706
  have hstable : (prefixWord ++ tailWord_4802706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802706).length < 2 ^ (prefixWord ++ tailWord_4802706).sum := by decide
  have hdescent : baseEnd_4802706 < baseStart_4802706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802709 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 1, 8]
def baseStart_4802709 : Nat := 118140960795 + 4802709 * 2 ^ 59
def prefixEnd_4802709 : Nat := 4983230072969 + 3 ^ 40 * 4802709 * 2
def baseEnd_4802709 : Nat := 822032720224785037550083

theorem tailTrace_4802709 : CollatzResearch.WordTrace tailWord_4802709 prefixEnd_4802709 822032720224785037550083 := by
  unfold tailWord_4802709
  simp only [CollatzResearch.WordTrace]
  refine ⟨175169187957613005239875181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116779458638408670159916787 175169187957613005239875181)
  ·
    refine ⟨65688445484104876964953193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175169187957613005239875181 65688445484104876964953193)
    ·
      refine ⟨49266334113078657723714895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65688445484104876964953193 49266334113078657723714895)
      ·
        refine ⟨73899501169617986585572343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49266334113078657723714895 73899501169617986585572343)
        ·
          refine ⟨110849251754426979878358515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73899501169617986585572343 110849251754426979878358515)
          ·
            refine ⟨166273877631640469817537773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110849251754426979878358515 166273877631640469817537773)
            ·
              refine ⟨62352704111865176181576665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166273877631640469817537773 62352704111865176181576665)
              ·
                refine ⟨46764528083898882136182499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62352704111865176181576665 46764528083898882136182499)
                ·
                  refine ⟨70146792125848323204273749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46764528083898882136182499 70146792125848323204273749)
                  ·
                    refine ⟨822032720224785037550083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70146792125848323204273749 822032720224785037550083)
                    ·
                      rfl

theorem cell23_4802709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_4802709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802709 prefixEnd_4802709 := by exact prefixLift 4802709
  have htrace : WordTrace (prefixWord ++ tailWord_4802709) baseStart_4802709 baseEnd_4802709 := by
    simpa [prefixWord, tailWord_4802709, baseEnd_4802709] using wordTrace_append hprefix tailTrace_4802709
  have hstable : (prefixWord ++ tailWord_4802709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802709).length < 2 ^ (prefixWord ++ tailWord_4802709).sum := by decide
  have hdescent : baseEnd_4802709 < baseStart_4802709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802714 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3]
def baseStart_4802714 : Nat := 118140960795 + 4802714 * 2 ^ 59
def prefixEnd_4802714 : Nat := 4983230072969 + 3 ^ 40 * 4802714 * 2
def baseEnd_4802714 : Nat := 2466100728077627593087727

theorem tailTrace_4802714 : CollatzResearch.WordTrace tailWord_4802714 prefixEnd_4802714 2466100728077627593087727 := by
  unfold tailWord_4802714
  simp only [CollatzResearch.WordTrace]
  refine ⟨43792342580648722773451799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116779580215063260729204797 43792342580648722773451799)
  ·
    refine ⟨65688513870973084160177699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43792342580648722773451799 65688513870973084160177699)
    ·
      refine ⟨98532770806459626240266549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65688513870973084160177699 98532770806459626240266549)
      ·
        refine ⟨9237447263105589960024989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98532770806459626240266549 9237447263105589960024989)
        ·
          refine ⟨3464042723664596235009371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9237447263105589960024989 3464042723664596235009371)
          ·
            refine ⟨5196064085496894352514057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3464042723664596235009371 5196064085496894352514057)
            ·
              refine ⟨3897048064122670764385543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5196064085496894352514057 3897048064122670764385543)
              ·
                refine ⟨5845572096184006146578315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3897048064122670764385543 5845572096184006146578315)
                ·
                  refine ⟨8768358144276009219867473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5845572096184006146578315 8768358144276009219867473)
                  ·
                    refine ⟨6576268608207006914900605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8768358144276009219867473 6576268608207006914900605)
                    ·
                      refine ⟨2466100728077627593087727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6576268608207006914900605 2466100728077627593087727)
                      ·
                        rfl

theorem cell23_4802714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_4802714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802714 prefixEnd_4802714 := by exact prefixLift 4802714
  have htrace : WordTrace (prefixWord ++ tailWord_4802714) baseStart_4802714 baseEnd_4802714 := by
    simpa [prefixWord, tailWord_4802714, baseEnd_4802714] using wordTrace_append hprefix tailTrace_4802714
  have hstable : (prefixWord ++ tailWord_4802714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802714).length < 2 ^ (prefixWord ++ tailWord_4802714).sum := by decide
  have hdescent : baseEnd_4802714 < baseStart_4802714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802720 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 1, 3, 2]
def baseStart_4802720 : Nat := 118140960795 + 4802720 * 2 ^ 59
def prefixEnd_4802720 : Nat := 4983230072969 + 3 ^ 40 * 4802720 * 2
def baseEnd_4802720 : Nat := 2466103808961554569612699

theorem tailTrace_4802720 : CollatzResearch.WordTrace tailWord_4802720 prefixEnd_4802720 2466103808961554569612699 := by
  unfold tailWord_4802720
  simp only [CollatzResearch.WordTrace]
  refine ⟨87584794580286577059262807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116779726107048769412350409 87584794580286577059262807)
  ·
    refine ⟨131377191870429865588894211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87584794580286577059262807 131377191870429865588894211)
    ·
      refine ⟨197065787805644798383341317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131377191870429865588894211 197065787805644798383341317)
      ·
        refine ⟨36949835213558399696876497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197065787805644798383341317 36949835213558399696876497)
        ·
          refine ⟨27712376410168799772657373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36949835213558399696876497 27712376410168799772657373)
          ·
            refine ⟨10392141153813299914746515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27712376410168799772657373 10392141153813299914746515)
            ·
              refine ⟨15588211730719949872119773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10392141153813299914746515 15588211730719949872119773)
              ·
                refine ⟨5845579399019981202044915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15588211730719949872119773 5845579399019981202044915)
                ·
                  refine ⟨8768369098529971803067373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5845579399019981202044915 8768369098529971803067373)
                  ·
                    refine ⟨3288138411948739426150265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8768369098529971803067373 3288138411948739426150265)
                    ·
                      refine ⟨2466103808961554569612699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288138411948739426150265 2466103808961554569612699)
                      ·
                        rfl

theorem cell23_4802720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_4802720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802720 prefixEnd_4802720 := by exact prefixLift 4802720
  have htrace : WordTrace (prefixWord ++ tailWord_4802720) baseStart_4802720 baseEnd_4802720 := by
    simpa [prefixWord, tailWord_4802720, baseEnd_4802720] using wordTrace_append hprefix tailTrace_4802720
  have hstable : (prefixWord ++ tailWord_4802720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802720).length < 2 ^ (prefixWord ++ tailWord_4802720).sum := by decide
  have hdescent : baseEnd_4802720 < baseStart_4802720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802746 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_4802746 : Nat := 118140960795 + 4802746 * 2 ^ 59
def prefixEnd_4802746 : Nat := 4983230072969 + 3 ^ 40 * 4802746 * 2
def baseEnd_4802746 : Nat := 2466117159458571467887579

theorem tailTrace_4802746 : CollatzResearch.WordTrace tailWord_4802746 prefixEnd_4802746 2466117159458571467887579 := by
  unfold tailWord_4802746
  simp only [CollatzResearch.WordTrace]
  refine ⟨43792634364619740139743023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116780358305652640372648061 43792634364619740139743023)
  ·
    refine ⟨65688951546929610209614535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43792634364619740139743023 65688951546929610209614535)
    ·
      refine ⟨98533427320394415314421803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65688951546929610209614535 98533427320394415314421803)
      ·
        refine ⟨147800140980591622971632705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98533427320394415314421803 147800140980591622971632705)
        ·
          refine ⟨110850105735443717228724529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147800140980591622971632705 110850105735443717228724529)
          ·
            refine ⟨83137579301582787921543397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110850105735443717228724529 83137579301582787921543397)
            ·
              refine ⟨15588296119046772735289387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83137579301582787921543397 15588296119046772735289387)
              ·
                refine ⟨23382444178570159102934081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15588296119046772735289387 23382444178570159102934081)
                ·
                  refine ⟨17536833133927619327200561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23382444178570159102934081 17536833133927619327200561)
                  ·
                    refine ⟨13152624850445714495400421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17536833133927619327200561 13152624850445714495400421)
                    ·
                      refine ⟨2466117159458571467887579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13152624850445714495400421 2466117159458571467887579)
                      ·
                        rfl

theorem cell23_4802746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_4802746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802746 prefixEnd_4802746 := by exact prefixLift 4802746
  have htrace : WordTrace (prefixWord ++ tailWord_4802746) baseStart_4802746 baseEnd_4802746 := by
    simpa [prefixWord, tailWord_4802746, baseEnd_4802746] using wordTrace_append hprefix tailTrace_4802746
  have hstable : (prefixWord ++ tailWord_4802746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802746).length < 2 ^ (prefixWord ++ tailWord_4802746).sum := by decide
  have hdescent : baseEnd_4802746 < baseStart_4802746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802754 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_4802754 : Nat := 118140960795 + 4802754 * 2 ^ 59
def prefixEnd_4802754 : Nat := 4983230072969 + 3 ^ 40 * 4802754 * 2
def baseEnd_4802754 : Nat := 2466121267303807436587543

theorem tailTrace_4802754 : CollatzResearch.WordTrace tailWord_4802754 prefixEnd_4802754 2466121267303807436587543 := by
  unfold tailWord_4802754
  simp only [CollatzResearch.WordTrace]
  refine ⟨43792707310612494481315829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116780552828299985283508877 43792707310612494481315829)
  ·
    refine ⟨4105566310369921357623359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43792707310612494481315829 4105566310369921357623359)
    ·
      refine ⟨6158349465554882036435039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4105566310369921357623359 6158349465554882036435039)
      ·
        refine ⟨9237524198332323054652559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6158349465554882036435039 9237524198332323054652559)
        ·
          refine ⟨13856286297498484581978839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9237524198332323054652559 13856286297498484581978839)
          ·
            refine ⟨20784429446247726872968259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13856286297498484581978839 20784429446247726872968259)
            ·
              refine ⟨31176644169371590309452389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20784429446247726872968259 31176644169371590309452389)
              ·
                refine ⟨5845620781757173183022323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31176644169371590309452389 5845620781757173183022323)
                ·
                  refine ⟨8768431172635759774533485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5845620781757173183022323 8768431172635759774533485)
                  ·
                    refine ⟨3288161689738409915450057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8768431172635759774533485 3288161689738409915450057)
                    ·
                      refine ⟨2466121267303807436587543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288161689738409915450057 2466121267303807436587543)
                      ·
                        rfl

theorem cell23_4802754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_4802754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802754 prefixEnd_4802754 := by exact prefixLift 4802754
  have htrace : WordTrace (prefixWord ++ tailWord_4802754) baseStart_4802754 baseEnd_4802754 := by
    simpa [prefixWord, tailWord_4802754, baseEnd_4802754] using wordTrace_append hprefix tailTrace_4802754
  have hstable : (prefixWord ++ tailWord_4802754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802754).length < 2 ^ (prefixWord ++ tailWord_4802754).sum := by decide
  have hdescent : baseEnd_4802754 < baseStart_4802754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802796 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_4802796 : Nat := 118140960795 + 4802796 * 2 ^ 59
def prefixEnd_4802796 : Nat := 4983230072969 + 3 ^ 40 * 4802796 * 2
def baseEnd_4802796 : Nat := 2466142833491296272262349

theorem tailTrace_4802796 : CollatzResearch.WordTrace tailWord_4802796 prefixEnd_4802796 2466142833491296272262349 := by
  unfold tailWord_4802796
  simp only [CollatzResearch.WordTrace]
  refine ⟨87586180554148909549146121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116781574072198546065528161 87586180554148909549146121)
  ·
    refine ⟨65689635415611682161859591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87586180554148909549146121 65689635415611682161859591)
    ·
      refine ⟨98534453123417523242789387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65689635415611682161859591 98534453123417523242789387)
      ·
        refine ⟨147801679685126284864184081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98534453123417523242789387 147801679685126284864184081)
        ·
          refine ⟨110851259763844713648138061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147801679685126284864184081 110851259763844713648138061)
          ·
            refine ⟨41569222411441767618051773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110851259763844713648138061 41569222411441767618051773)
            ·
              refine ⟨15588458404290662856769415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41569222411441767618051773 15588458404290662856769415)
              ·
                refine ⟨23382687606435994285154123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15588458404290662856769415 23382687606435994285154123)
                ·
                  refine ⟨35074031409653991427731185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23382687606435994285154123 35074031409653991427731185)
                  ·
                    refine ⟨26305523557240493570798389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35074031409653991427731185 26305523557240493570798389)
                    ·
                      refine ⟨2466142833491296272262349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26305523557240493570798389 2466142833491296272262349)
                      ·
                        rfl

theorem cell23_4802796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_4802796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802796 prefixEnd_4802796 := by exact prefixLift 4802796
  have htrace : WordTrace (prefixWord ++ tailWord_4802796) baseStart_4802796 baseEnd_4802796 := by
    simpa [prefixWord, tailWord_4802796, baseEnd_4802796] using wordTrace_append hprefix tailTrace_4802796
  have hstable : (prefixWord ++ tailWord_4802796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802796).length < 2 ^ (prefixWord ++ tailWord_4802796).sum := by decide
  have hdescent : baseEnd_4802796 < baseStart_4802796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802820 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_4802820 : Nat := 118140960795 + 4802820 * 2 ^ 59
def prefixEnd_4802820 : Nat := 4983230072969 + 3 ^ 40 * 4802820 * 2
def baseEnd_4802820 : Nat := 822051719009001392787413

theorem tailTrace_4802820 : CollatzResearch.WordTrace tailWord_4802820 prefixEnd_4802820 822051719009001392787413 := by
  unfold tailWord_4802820
  simp only [CollatzResearch.WordTrace]
  refine ⟨87586618230105435598582957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116782157640140580798110609 87586618230105435598582957)
  ·
    refine ⟨32844981836289538349468609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87586618230105435598582957 32844981836289538349468609)
    ·
      refine ⟨24633736377217153762101457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32844981836289538349468609 24633736377217153762101457)
      ·
        refine ⟨18475302282912865321576093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24633736377217153762101457 18475302282912865321576093)
        ·
          refine ⟨6928238356092324495591035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18475302282912865321576093 6928238356092324495591035)
          ·
            refine ⟨10392357534138486743386553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6928238356092324495591035 10392357534138486743386553)
            ·
              refine ⟨7794268150603865057539915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10392357534138486743386553 7794268150603865057539915)
              ·
                refine ⟨11691402225905797586309873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7794268150603865057539915 11691402225905797586309873)
                ·
                  refine ⟨8768551669429348189732405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11691402225905797586309873 8768551669429348189732405)
                  ·
                    refine ⟨822051719009001392787413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8768551669429348189732405 822051719009001392787413)
                    ·
                      rfl

theorem cell23_4802820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_4802820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802820 prefixEnd_4802820 := by exact prefixLift 4802820
  have htrace : WordTrace (prefixWord ++ tailWord_4802820) baseStart_4802820 baseEnd_4802820 := by
    simpa [prefixWord, tailWord_4802820, baseEnd_4802820] using wordTrace_append hprefix tailTrace_4802820
  have hstable : (prefixWord ++ tailWord_4802820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802820).length < 2 ^ (prefixWord ++ tailWord_4802820).sum := by decide
  have hdescent : baseEnd_4802820 < baseStart_4802820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802843 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 3]
def baseStart_4802843 : Nat := 118140960795 + 4802843 * 2 ^ 59
def prefixEnd_4802843 : Nat := 4983230072969 + 3 ^ 40 * 4802843 * 2
def baseEnd_4802843 : Nat := 2466166967082057588374633

theorem tailTrace_4802843 : CollatzResearch.WordTrace tailWord_4802843 prefixEnd_4802843 2466166967082057588374633 := by
  unfold tailWord_4802843
  simp only [CollatzResearch.WordTrace]
  refine ⟨175174075339127546125253183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116782716892751697416835455 175174075339127546125253183)
  ·
    refine ⟨262761113008691319187879775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175174075339127546125253183 262761113008691319187879775)
    ·
      refine ⟨394141669513036978781819663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262761113008691319187879775 394141669513036978781819663)
      ·
        refine ⟨591212504269555468172729495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394141669513036978781819663 591212504269555468172729495)
        ·
          refine ⟨886818756404333202259094243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591212504269555468172729495 886818756404333202259094243)
          ·
            refine ⟨1330228134606499803388641365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886818756404333202259094243 1330228134606499803388641365)
            ·
              refine ⟨15588610952419919570960641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1330228134606499803388641365 15588610952419919570960641)
              ·
                refine ⟨11691458214314939678220481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15588610952419919570960641 11691458214314939678220481)
                ·
                  refine ⟨8768593660736204758665361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11691458214314939678220481 8768593660736204758665361)
                  ·
                    refine ⟨6576445245552153568999021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8768593660736204758665361 6576445245552153568999021)
                    ·
                      refine ⟨2466166967082057588374633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6576445245552153568999021 2466166967082057588374633)
                      ·
                        rfl

theorem cell23_4802843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 3].length) (baseStart_4802843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802843 prefixEnd_4802843 := by exact prefixLift 4802843
  have htrace : WordTrace (prefixWord ++ tailWord_4802843) baseStart_4802843 baseEnd_4802843 := by
    simpa [prefixWord, tailWord_4802843, baseEnd_4802843] using wordTrace_append hprefix tailTrace_4802843
  have hstable : (prefixWord ++ tailWord_4802843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802843).length < 2 ^ (prefixWord ++ tailWord_4802843).sum := by decide
  have hdescent : baseEnd_4802843 < baseStart_4802843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802930 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_4802930 : Nat := 118140960795 + 4802930 * 2 ^ 59
def prefixEnd_4802930 : Nat := 4983230072969 + 3 ^ 40 * 4802930 * 2
def baseEnd_4802930 : Nat := 2466211639898998747986733

theorem tailTrace_4802930 : CollatzResearch.WordTrace tailWord_4802930 prefixEnd_4802930 2466211639898998747986733 := by
  unfold tailWord_4802930
  simp only [CollatzResearch.WordTrace]
  refine ⟨43794312122453089995917561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116784832326541573322446829 43794312122453089995917561)
  ·
    refine ⟨32845734091839817496938171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43794312122453089995917561 32845734091839817496938171)
    ·
      refine ⟨49268601137759726245407257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32845734091839817496938171 49268601137759726245407257)
      ·
        refine ⟨36951450853319794684055443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49268601137759726245407257 36951450853319794684055443)
        ·
          refine ⟨55427176279979692026083165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36951450853319794684055443 55427176279979692026083165)
          ·
            refine ⟨20785191104992384509781187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55427176279979692026083165 20785191104992384509781187)
            ·
              refine ⟨31177786657488576764671781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20785191104992384509781187 31177786657488576764671781)
              ·
                refine ⟨5845834998279108143375959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31177786657488576764671781 5845834998279108143375959)
                ·
                  refine ⟨8768752497418662215063939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5845834998279108143375959 8768752497418662215063939)
                  ·
                    refine ⟨13153128746127993322595909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8768752497418662215063939 13153128746127993322595909)
                    ·
                      refine ⟨2466211639898998747986733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13153128746127993322595909 2466211639898998747986733)
                      ·
                        rfl

theorem cell23_4802930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_4802930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802930 prefixEnd_4802930 := by exact prefixLift 4802930
  have htrace : WordTrace (prefixWord ++ tailWord_4802930) baseStart_4802930 baseEnd_4802930 := by
    simpa [prefixWord, tailWord_4802930, baseEnd_4802930] using wordTrace_append hprefix tailTrace_4802930
  have hstable : (prefixWord ++ tailWord_4802930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802930).length < 2 ^ (prefixWord ++ tailWord_4802930).sum := by decide
  have hdescent : baseEnd_4802930 < baseStart_4802930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802953 : List Nat := [1, 2, 1, 1, 6, 3, 9]
def baseStart_4802953 : Nat := 118140960795 + 4802953 * 2 ^ 59
def prefixEnd_4802953 : Nat := 4983230072969 + 3 ^ 40 * 4802953 * 2
def baseEnd_4802953 : Nat := 30447203085852495777767

theorem tailTrace_4802953 : CollatzResearch.WordTrace tailWord_4802953 prefixEnd_4802953 30447203085852495777767 := by
  unfold tailWord_4802953
  simp only [CollatzResearch.WordTrace]
  refine ⟨175178087368729034911757513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116785391579152689941171675 175178087368729034911757513)
  ·
    refine ⟨131383565526546776183818135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175178087368729034911757513 131383565526546776183818135)
    ·
      refine ⟨197075348289820164275727203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131383565526546776183818135 197075348289820164275727203)
      ·
        refine ⟨295613022434730246413590805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197075348289820164275727203 295613022434730246413590805)
        ·
          refine ⟨13856860426627980300637069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 295613022434730246413590805 13856860426627980300637069)
          ·
            refine ⟨5196322659985492612738901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13856860426627980300637069 5196322659985492612738901)
            ·
              refine ⟨30447203085852495777767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5196322659985492612738901 30447203085852495777767)
              ·
                rfl

theorem cell23_4802953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 9].length) (baseStart_4802953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802953 prefixEnd_4802953 := by exact prefixLift 4802953
  have htrace : WordTrace (prefixWord ++ tailWord_4802953) baseStart_4802953 baseEnd_4802953 := by
    simpa [prefixWord, tailWord_4802953, baseEnd_4802953] using wordTrace_append hprefix tailTrace_4802953
  have hstable : (prefixWord ++ tailWord_4802953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802953).length < 2 ^ (prefixWord ++ tailWord_4802953).sum := by decide
  have hdescent : baseEnd_4802953 < baseStart_4802953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802974 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_4802974 : Nat := 118140960795 + 4802974 * 2 ^ 59
def prefixEnd_4802974 : Nat := 4983230072969 + 3 ^ 40 * 4802974 * 2
def baseEnd_4802974 : Nat := 822078077682598858612177

theorem tailTrace_4802974 : CollatzResearch.WordTrace tailWord_4802974 prefixEnd_4802974 822078077682598858612177 := by
  unfold tailWord_4802974
  simp only [CollatzResearch.WordTrace]
  refine ⟨21897356662706619437283997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116785902201101970332181317 21897356662706619437283997)
  ·
    refine ⟨8211508748514982288981499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21897356662706619437283997 8211508748514982288981499)
    ·
      refine ⟨12317263122772473433472249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8211508748514982288981499 12317263122772473433472249)
      ·
        refine ⟨9237947342079355075104187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12317263122772473433472249 9237947342079355075104187)
        ·
          refine ⟨13856921013119032612656281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9237947342079355075104187 13856921013119032612656281)
          ·
            refine ⟨10392690759839274459492211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13856921013119032612656281 10392690759839274459492211)
            ·
              refine ⟨15589036139758911689238317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10392690759839274459492211 15589036139758911689238317)
              ·
                refine ⟨5845888552409591883464369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15589036139758911689238317 5845888552409591883464369)
                ·
                  refine ⟨4384416414307193912598277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5845888552409591883464369 4384416414307193912598277)
                  ·
                    refine ⟨822078077682598858612177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4384416414307193912598277 822078077682598858612177)
                    ·
                      rfl

theorem cell23_4802974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_4802974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802974 prefixEnd_4802974 := by exact prefixLift 4802974
  have htrace : WordTrace (prefixWord ++ tailWord_4802974) baseStart_4802974 baseEnd_4802974 := by
    simpa [prefixWord, tailWord_4802974, baseEnd_4802974] using wordTrace_append hprefix tailTrace_4802974
  have hstable : (prefixWord ++ tailWord_4802974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802974).length < 2 ^ (prefixWord ++ tailWord_4802974).sum := by decide
  have hdescent : baseEnd_4802974 < baseStart_4802974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802984 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_4802984 : Nat := 118140960795 + 4802984 * 2 ^ 59
def prefixEnd_4802984 : Nat := 4983230072969 + 3 ^ 40 * 4802984 * 2
def baseEnd_4802984 : Nat := 2466239367854341536711485

theorem tailTrace_4802984 : CollatzResearch.WordTrace tailWord_4802984 prefixEnd_4802984 2466239367854341536711485 := by
  unfold tailWord_4802984
  simp only [CollatzResearch.WordTrace]
  refine ⟨87589609015808363603068003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116786145354411151470757337 87589609015808363603068003)
  ·
    refine ⟨131384413523712545404602005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87589609015808363603068003 131384413523712545404602005)
    ·
      refine ⟨6158644383924025565840719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131384413523712545404602005 6158644383924025565840719)
      ·
        refine ⟨9237966575886038348761079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6158644383924025565840719 9237966575886038348761079)
        ·
          refine ⟨13856949863829057523141619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9237966575886038348761079 13856949863829057523141619)
          ·
            refine ⟨20785424795743586284712429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13856949863829057523141619 20785424795743586284712429)
            ·
              refine ⟨7794534298403844856767161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20785424795743586284712429 7794534298403844856767161)
              ·
                refine ⟨5845900723802883642575371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7794534298403844856767161 5845900723802883642575371)
                ·
                  refine ⟨8768851085704325463863057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5845900723802883642575371 8768851085704325463863057)
                  ·
                    refine ⟨6576638314278244097897293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8768851085704325463863057 6576638314278244097897293)
                    ·
                      refine ⟨2466239367854341536711485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6576638314278244097897293 2466239367854341536711485)
                      ·
                        rfl

theorem cell23_4802984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_4802984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802984 prefixEnd_4802984 := by exact prefixLift 4802984
  have htrace : WordTrace (prefixWord ++ tailWord_4802984) baseStart_4802984 baseEnd_4802984 := by
    simpa [prefixWord, tailWord_4802984, baseEnd_4802984] using wordTrace_append hprefix tailTrace_4802984
  have hstable : (prefixWord ++ tailWord_4802984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802984).length < 2 ^ (prefixWord ++ tailWord_4802984).sum := by decide
  have hdescent : baseEnd_4802984 < baseStart_4802984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4802997 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_4802997 : Nat := 118140960795 + 4802997 * 2 ^ 59
def prefixEnd_4802997 : Nat := 4983230072969 + 3 ^ 40 * 4802997 * 2
def baseEnd_4802997 : Nat := 2466246043102849985848925

theorem tailTrace_4802997 : CollatzResearch.WordTrace tailWord_4802997 prefixEnd_4802997 2466246043102849985848925 := by
  unfold tailWord_4802997
  simp only [CollatzResearch.WordTrace]
  refine ⟨175179692180569630426359245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116786461453713086950906163 175179692180569630426359245)
  ·
    refine ⟨65692384567713611409884717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175179692180569630426359245 65692384567713611409884717)
    ·
      refine ⟨24634644212892604278706769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65692384567713611409884717 24634644212892604278706769)
      ·
        refine ⟨18475983159669453209030077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24634644212892604278706769 18475983159669453209030077)
        ·
          refine ⟨6928493684876044953386279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18475983159669453209030077 6928493684876044953386279)
          ·
            refine ⟨10392740527314067430079419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6928493684876044953386279 10392740527314067430079419)
            ·
              refine ⟨15589110790971101145119129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10392740527314067430079419 15589110790971101145119129)
              ·
                refine ⟨11691833093228325858839347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15589110790971101145119129 11691833093228325858839347)
                ·
                  refine ⟨17537749639842488788259021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11691833093228325858839347 17537749639842488788259021)
                  ·
                    refine ⟨6576656114940933295597133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17537749639842488788259021 6576656114940933295597133)
                    ·
                      refine ⟨2466246043102849985848925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6576656114940933295597133 2466246043102849985848925)
                      ·
                        rfl

theorem cell23_4802997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_4802997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4802997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4802997 prefixEnd_4802997 := by exact prefixLift 4802997
  have htrace : WordTrace (prefixWord ++ tailWord_4802997) baseStart_4802997 baseEnd_4802997 := by
    simpa [prefixWord, tailWord_4802997, baseEnd_4802997] using wordTrace_append hprefix tailTrace_4802997
  have hstable : (prefixWord ++ tailWord_4802997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4802997).length < 2 ^ (prefixWord ++ tailWord_4802997).sum := by decide
  have hdescent : baseEnd_4802997 < baseStart_4802997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4802997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803058 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 1, 3, 2]
def baseStart_4803058 : Nat := 118140960795 + 4803058 * 2 ^ 59
def prefixEnd_4803058 : Nat := 4983230072969 + 3 ^ 40 * 4803058 * 2
def baseEnd_4803058 : Nat := 2466277365422774247186145

theorem tailTrace_4803058 : CollatzResearch.WordTrace tailWord_4803058 prefixEnd_4803058 2466277365422774247186145 := by
  unfold tailWord_4803058
  simp only [CollatzResearch.WordTrace]
  refine ⟨43795479258337159461082457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116787944688899091896219885 43795479258337159461082457)
  ·
    refine ⟨32846609443752869595811843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43795479258337159461082457 32846609443752869595811843)
    ·
      refine ⟨49269914165629304393717765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32846609443752869595811843 49269914165629304393717765)
      ·
        refine ⟨9238108906055494573822081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49269914165629304393717765 9238108906055494573822081)
        ·
          refine ⟨6928581679541620930366561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9238108906055494573822081 6928581679541620930366561)
          ·
            refine ⟨5196436259656215697774921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6928581679541620930366561 5196436259656215697774921)
            ·
              refine ⟨3897327194742161773331191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5196436259656215697774921 3897327194742161773331191)
              ·
                refine ⟨5845990792113242659996787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3897327194742161773331191 5845990792113242659996787)
                ·
                  refine ⟨8768986188169863989995181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5845990792113242659996787 8768986188169863989995181)
                  ·
                    refine ⟨3288369820563698996248193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8768986188169863989995181 3288369820563698996248193)
                    ·
                      refine ⟨2466277365422774247186145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288369820563698996248193 2466277365422774247186145)
                      ·
                        rfl

theorem cell23_4803058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_4803058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803058 prefixEnd_4803058 := by exact prefixLift 4803058
  have htrace : WordTrace (prefixWord ++ tailWord_4803058) baseStart_4803058 baseEnd_4803058 := by
    simpa [prefixWord, tailWord_4803058, baseEnd_4803058] using wordTrace_append hprefix tailTrace_4803058
  have hstable : (prefixWord ++ tailWord_4803058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803058).length < 2 ^ (prefixWord ++ tailWord_4803058).sum := by decide
  have hdescent : baseEnd_4803058 < baseStart_4803058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803103 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 1, 10]
def baseStart_4803103 : Nat := 118140960795 + 4803103 * 2 ^ 59
def prefixEnd_4803103 : Nat := 4983230072969 + 3 ^ 40 * 4803103 * 2
def baseEnd_4803103 : Nat := 822100157350742190374479

theorem tailTrace_4803103 : CollatzResearch.WordTrace tailWord_4803103 prefixEnd_4803103 822100157350742190374479 := by
  unfold tailWord_4803103
  simp only [CollatzResearch.WordTrace]
  refine ⟨175183558318185610529717963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116789038878790407019811975 175183558318185610529717963)
  ·
    refine ⟨262775337477278415794576945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175183558318185610529717963 262775337477278415794576945)
    ·
      refine ⟨197081503107958811845932709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262775337477278415794576945 197081503107958811845932709)
      ·
        refine ⟨36952781832742277221112383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197081503107958811845932709 36952781832742277221112383)
        ·
          refine ⟨55429172749113415831668575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36952781832742277221112383 55429172749113415831668575)
          ·
            refine ⟨83143759123670123747502863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55429172749113415831668575 83143759123670123747502863)
            ·
              refine ⟨124715638685505185621254295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83143759123670123747502863 124715638685505185621254295)
              ·
                refine ⟨187073458028257778431881443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124715638685505185621254295 187073458028257778431881443)
                ·
                  refine ⟨280610187042386667647822165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187073458028257778431881443 280610187042386667647822165)
                  ·
                    refine ⟨822100157350742190374479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 280610187042386667647822165 822100157350742190374479)
                    ·
                      rfl

theorem cell23_4803103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_4803103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803103 prefixEnd_4803103 := by exact prefixLift 4803103
  have htrace : WordTrace (prefixWord ++ tailWord_4803103) baseStart_4803103 baseEnd_4803103 := by
    simpa [prefixWord, tailWord_4803103, baseEnd_4803103] using wordTrace_append hprefix tailTrace_4803103
  have hstable : (prefixWord ++ tailWord_4803103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803103).length < 2 ^ (prefixWord ++ tailWord_4803103).sum := by decide
  have hdescent : baseEnd_4803103 < baseStart_4803103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803120 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 5, 4]
def baseStart_4803120 : Nat := 118140960795 + 4803120 * 2 ^ 59
def prefixEnd_4803120 : Nat := 4983230072969 + 3 ^ 40 * 4803120 * 2
def baseEnd_4803120 : Nat := 822103067074451001536953

theorem tailTrace_4803120 : CollatzResearch.WordTrace tailWord_4803120 prefixEnd_4803120 822103067074451001536953 := by
  unfold tailWord_4803120
  simp only [CollatzResearch.WordTrace]
  refine ⟨87592089179562011216543407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116789452239416014955391209 87592089179562011216543407)
  ·
    refine ⟨131388133769343016824815111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87592089179562011216543407 131388133769343016824815111)
    ·
      refine ⟨197082200654014525237222667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131388133769343016824815111 197082200654014525237222667)
      ·
        refine ⟨295623300981021787855834001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197082200654014525237222667 295623300981021787855834001)
        ·
          refine ⟨221717475735766340891875501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295623300981021787855834001 221717475735766340891875501)
          ·
            refine ⟨83144053400912377834453313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221717475735766340891875501 83144053400912377834453313)
            ·
              refine ⟨62358040050684283375839985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83144053400912377834453313 62358040050684283375839985)
              ·
                refine ⟨46768530038013212531879989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62358040050684283375839985 46768530038013212531879989)
                ·
                  refine ⟨4384549691063738674863749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46768530038013212531879989 4384549691063738674863749)
                  ·
                    refine ⟨822103067074451001536953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4384549691063738674863749 822103067074451001536953)
                    ·
                      rfl

theorem cell23_4803120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5, 4].length) (baseStart_4803120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803120 prefixEnd_4803120 := by exact prefixLift 4803120
  have htrace : WordTrace (prefixWord ++ tailWord_4803120) baseStart_4803120 baseEnd_4803120 := by
    simpa [prefixWord, tailWord_4803120, baseEnd_4803120] using wordTrace_append hprefix tailTrace_4803120
  have hstable : (prefixWord ++ tailWord_4803120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803120).length < 2 ^ (prefixWord ++ tailWord_4803120).sum := by decide
  have hdescent : baseEnd_4803120 < baseStart_4803120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803134 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_4803134 : Nat := 118140960795 + 4803134 * 2 ^ 59
def prefixEnd_4803134 : Nat := 4983230072969 + 3 ^ 40 * 4803134 * 2
def baseEnd_4803134 : Nat := 2466316389952515949835795

theorem tailTrace_4803134 : CollatzResearch.WordTrace tailWord_4803134 prefixEnd_4803134 2466316389952515949835795 := by
  unfold tailWord_4803134
  simp only [CollatzResearch.WordTrace]
  refine ⟨21898086122634162853012057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116789792654048868549397637 21898086122634162853012057)
  ·
    refine ⟨16423564591975622139759043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21898086122634162853012057 16423564591975622139759043)
    ·
      refine ⟨24635346887963433209638565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16423564591975622139759043 24635346887963433209638565)
      ·
        refine ⟨4619127541493143726807231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24635346887963433209638565 4619127541493143726807231)
        ·
          refine ⟨6928691312239715590210847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4619127541493143726807231 6928691312239715590210847)
          ·
            refine ⟨10393036968359573385316271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6928691312239715590210847 10393036968359573385316271)
            ·
              refine ⟨15589555452539360077974407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10393036968359573385316271 15589555452539360077974407)
              ·
                refine ⟨23384333178809040116961611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15589555452539360077974407 23384333178809040116961611)
                ·
                  refine ⟨35076499768213560175442417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23384333178809040116961611 35076499768213560175442417)
                  ·
                    refine ⟨26307374826160170131581813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35076499768213560175442417 26307374826160170131581813)
                    ·
                      refine ⟨2466316389952515949835795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26307374826160170131581813 2466316389952515949835795)
                      ·
                        rfl

theorem cell23_4803134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_4803134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803134 prefixEnd_4803134 := by exact prefixLift 4803134
  have htrace : WordTrace (prefixWord ++ tailWord_4803134) baseStart_4803134 baseEnd_4803134 := by
    simpa [prefixWord, tailWord_4803134, baseEnd_4803134] using wordTrace_append hprefix tailTrace_4803134
  have hstable : (prefixWord ++ tailWord_4803134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803134).length < 2 ^ (prefixWord ++ tailWord_4803134).sum := by decide
  have hdescent : baseEnd_4803134 < baseStart_4803134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803160 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 2, 5, 3]
def baseStart_4803160 : Nat := 118140960795 + 4803160 * 2 ^ 59
def prefixEnd_4803160 : Nat := 4983230072969 + 3 ^ 40 * 4803160 * 2
def baseEnd_4803160 : Nat := 2466329740449532848110675

theorem tailTrace_4803160 : CollatzResearch.WordTrace tailWord_4803160 prefixEnd_4803160 2466329740449532848110675 := by
  unfold tailWord_4803160
  simp only [CollatzResearch.WordTrace]
  refine ⟨87592818639489554632271467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116790424852652739509695289 87592818639489554632271467)
  ·
    refine ⟨131389227959234331948407201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87592818639489554632271467 131389227959234331948407201)
    ·
      refine ⟨98541920969425748961305401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131389227959234331948407201 98541920969425748961305401)
      ·
        refine ⟨73906440727069311720979051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98541920969425748961305401 73906440727069311720979051)
        ·
          refine ⟨110859661090603967581468577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73906440727069311720979051 110859661090603967581468577)
          ·
            refine ⟨83144745817952975686101433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110859661090603967581468577 83144745817952975686101433)
            ·
              refine ⟨62358559363464731764576075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83144745817952975686101433 62358559363464731764576075)
              ·
                refine ⟨93537839045197097646864113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62358559363464731764576075 93537839045197097646864113)
                ·
                  refine ⟨70153379283897823235148085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93537839045197097646864113 70153379283897823235148085)
                  ·
                    refine ⟨6576879307865420928295133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70153379283897823235148085 6576879307865420928295133)
                    ·
                      refine ⟨2466329740449532848110675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6576879307865420928295133 2466329740449532848110675)
                      ·
                        rfl

theorem cell23_4803160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_4803160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803160 prefixEnd_4803160 := by exact prefixLift 4803160
  have htrace : WordTrace (prefixWord ++ tailWord_4803160) baseStart_4803160 baseEnd_4803160 := by
    simpa [prefixWord, tailWord_4803160, baseEnd_4803160] using wordTrace_append hprefix tailTrace_4803160
  have hstable : (prefixWord ++ tailWord_4803160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803160).length < 2 ^ (prefixWord ++ tailWord_4803160).sum := by decide
  have hdescent : baseEnd_4803160 < baseStart_4803160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803187 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 4, 3, 2]
def baseStart_4803187 : Nat := 118140960795 + 4803187 * 2 ^ 59
def prefixEnd_4803187 : Nat := 4983230072969 + 3 ^ 40 * 4803187 * 2
def baseEnd_4803187 : Nat := 2466343604427204242473051

theorem tailTrace_4803187 : CollatzResearch.WordTrace tailWord_4803187 prefixEnd_4803187 2466343604427204242473051 := by
  unfold tailWord_4803187
  simp only [CollatzResearch.WordTrace]
  refine ⟨175186622049881292875775815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116791081366587528583850543 175186622049881292875775815)
  ·
    refine ⟨262779933074821939313663723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175186622049881292875775815 262779933074821939313663723)
    ·
      refine ⟨394169899612232908970495585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262779933074821939313663723 394169899612232908970495585)
      ·
        refine ⟨295627424709174681727871689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394169899612232908970495585 295627424709174681727871689)
        ·
          refine ⟨221720568531881011295903767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295627424709174681727871689 221720568531881011295903767)
          ·
            refine ⟨332580852797821516943855651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221720568531881011295903767 332580852797821516943855651)
            ·
              refine ⟨498871279196732275415783477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332580852797821516943855651 498871279196732275415783477)
              ·
                refine ⟨46769182424693650820229701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 498871279196732275415783477 46769182424693650820229701)
                ·
                  refine ⟨8769221704630059528793069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46769182424693650820229701 8769221704630059528793069)
                  ·
                    refine ⟨3288458139236272323297401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8769221704630059528793069 3288458139236272323297401)
                    ·
                      refine ⟨2466343604427204242473051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288458139236272323297401 2466343604427204242473051)
                      ·
                        rfl

theorem cell23_4803187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 3, 2].length) (baseStart_4803187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803187 prefixEnd_4803187 := by exact prefixLift 4803187
  have htrace : WordTrace (prefixWord ++ tailWord_4803187) baseStart_4803187 baseEnd_4803187 := by
    simpa [prefixWord, tailWord_4803187, baseEnd_4803187] using wordTrace_append hprefix tailTrace_4803187
  have hstable : (prefixWord ++ tailWord_4803187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803187).length < 2 ^ (prefixWord ++ tailWord_4803187).sum := by decide
  have hdescent : baseEnd_4803187 < baseStart_4803187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803228 : List Nat := [2, 2, 3, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_4803228 : Nat := 118140960795 + 4803228 * 2 ^ 59
def prefixEnd_4803228 : Nat := 4983230072969 + 3 ^ 40 * 4803228 * 2
def baseEnd_4803228 : Nat := 2466364657134038582060363

theorem tailTrace_4803228 : CollatzResearch.WordTrace tailWord_4803228 prefixEnd_4803228 2466364657134038582060363 := by
  unfold tailWord_4803228
  simp only [CollatzResearch.WordTrace]
  refine ⟨87594058721366378439009169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116792078295155171252012225 87594058721366378439009169)
  ·
    refine ⟨65695544041024783829256877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87594058721366378439009169 65695544041024783829256877)
    ·
      refine ⟨24635829015384293935971329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65695544041024783829256877 24635829015384293935971329)
      ·
        refine ⟨18476871761538220451978497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24635829015384293935971329 18476871761538220451978497)
        ·
          refine ⟨13857653821153665338983873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18476871761538220451978497 13857653821153665338983873)
          ·
            refine ⟨10393240365865249004237905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13857653821153665338983873 10393240365865249004237905)
            ·
              refine ⟨7794930274398936753178429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10393240365865249004237905 7794930274398936753178429)
              ·
                refine ⟨2923098852899601282441911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7794930274398936753178429 2923098852899601282441911)
                ·
                  refine ⟨4384648279349401923662867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2923098852899601282441911 4384648279349401923662867)
                  ·
                    refine ⟨6576972419024102885494301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4384648279349401923662867 6576972419024102885494301)
                    ·
                      refine ⟨2466364657134038582060363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6576972419024102885494301 2466364657134038582060363)
                      ·
                        rfl

theorem cell23_4803228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_4803228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803228 prefixEnd_4803228 := by exact prefixLift 4803228
  have htrace : WordTrace (prefixWord ++ tailWord_4803228) baseStart_4803228 baseEnd_4803228 := by
    simpa [prefixWord, tailWord_4803228, baseEnd_4803228] using wordTrace_append hprefix tailTrace_4803228
  have hstable : (prefixWord ++ tailWord_4803228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803228).length < 2 ^ (prefixWord ++ tailWord_4803228).sum := by decide
  have hdescent : baseEnd_4803228 < baseStart_4803228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803250 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_4803250 : Nat := 118140960795 + 4803250 * 2 ^ 59
def prefixEnd_4803250 : Nat := 4983230072969 + 3 ^ 40 * 4803250 * 2
def baseEnd_4803250 : Nat := 2466375953708437495985261

theorem tailTrace_4803250 : CollatzResearch.WordTrace tailWord_4803250 prefixEnd_4803250 2466375953708437495985261 := by
  unfold tailWord_4803250
  simp only [CollatzResearch.WordTrace]
  refine ⟨43797229962163263658829801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116792613232435369756879469 43797229962163263658829801)
  ·
    refine ⟨32847922471622447744122351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43797229962163263658829801 32847922471622447744122351)
    ·
      refine ⟨49271883707433671616183527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32847922471622447744122351 49271883707433671616183527)
      ·
        refine ⟨73907825561150507424275291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49271883707433671616183527 73907825561150507424275291)
        ·
          refine ⟨110861738341725761136412937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73907825561150507424275291 110861738341725761136412937)
          ·
            refine ⟨83146303756294320852309703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110861738341725761136412937 83146303756294320852309703)
            ·
              refine ⟨124719455634441481278464555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83146303756294320852309703 124719455634441481278464555)
              ·
                refine ⟨187079183451662221917696833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124719455634441481278464555 187079183451662221917696833)
                ·
                  refine ⟨140309387588746666438272625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187079183451662221917696833 140309387588746666438272625)
                  ·
                    refine ⟨105232040691559999828704469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 140309387588746666438272625 105232040691559999828704469)
                    ·
                      refine ⟨2466375953708437495985261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105232040691559999828704469 2466375953708437495985261)
                      ·
                        rfl

theorem cell23_4803250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_4803250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803250 prefixEnd_4803250 := by exact prefixLift 4803250
  have htrace : WordTrace (prefixWord ++ tailWord_4803250) baseStart_4803250 baseEnd_4803250 := by
    simpa [prefixWord, tailWord_4803250, baseEnd_4803250] using wordTrace_append hprefix tailTrace_4803250
  have hstable : (prefixWord ++ tailWord_4803250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803250).length < 2 ^ (prefixWord ++ tailWord_4803250).sum := by decide
  have hdescent : baseEnd_4803250 < baseStart_4803250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803251 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 3, 2, 2]
def baseStart_4803251 : Nat := 118140960795 + 4803251 * 2 ^ 59
def prefixEnd_4803251 : Nat := 4983230072969 + 3 ^ 40 * 4803251 * 2
def baseEnd_4803251 : Nat := 2466376467189091992072757

theorem tailTrace_4803251 : CollatzResearch.WordTrace tailWord_4803251 prefixEnd_4803251 2466376467189091992072757 := by
  unfold tailWord_4803251
  simp only [CollatzResearch.WordTrace]
  refine ⟨175188956321649431806105607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116792637547766287870737071 175188956321649431806105607)
  ·
    refine ⟨262783434482474147709158411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175188956321649431806105607 262783434482474147709158411)
    ·
      refine ⟨394175151723711221563737617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262783434482474147709158411 394175151723711221563737617)
      ·
        refine ⟨295631363792783416172803213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394175151723711221563737617 295631363792783416172803213)
        ·
          refine ⟨110861761422293781064801205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295631363792783416172803213 110861761422293781064801205)
          ·
            refine ⟨10393290133340041974825113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110861761422293781064801205 10393290133340041974825113)
            ·
              refine ⟨7794967600005031481118835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10393290133340041974825113 7794967600005031481118835)
              ·
                refine ⟨11692451400007547221678253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7794967600005031481118835 11692451400007547221678253)
                ·
                  refine ⟨4384669275002830208129345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11692451400007547221678253 4384669275002830208129345)
                  ·
                    refine ⟨3288501956252122656097009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4384669275002830208129345 3288501956252122656097009)
                    ·
                      refine ⟨2466376467189091992072757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3288501956252122656097009 2466376467189091992072757)
                      ·
                        rfl

theorem cell23_4803251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 2, 2].length) (baseStart_4803251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803251 prefixEnd_4803251 := by exact prefixLift 4803251
  have htrace : WordTrace (prefixWord ++ tailWord_4803251) baseStart_4803251 baseEnd_4803251 := by
    simpa [prefixWord, tailWord_4803251, baseEnd_4803251] using wordTrace_append hprefix tailTrace_4803251
  have hstable : (prefixWord ++ tailWord_4803251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803251).length < 2 ^ (prefixWord ++ tailWord_4803251).sum := by decide
  have hdescent : baseEnd_4803251 < baseStart_4803251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803261 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_4803261 : Nat := 118140960795 + 4803261 * 2 ^ 59
def prefixEnd_4803261 : Nat := 4983230072969 + 3 ^ 40 * 4803261 * 2
def baseEnd_4803261 : Nat := 822127200665212317649237

theorem tailTrace_4803261 : CollatzResearch.WordTrace tailWord_4803261 prefixEnd_4803261 822127200665212317649237 := by
  unfold tailWord_4803261
  simp only [CollatzResearch.WordTrace]
  refine ⟨175189321051613203513969637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116792880701075469009313091 175189321051613203513969637)
  ·
    refine ⟨32847997697177475658869307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175189321051613203513969637 32847997697177475658869307)
    ·
      refine ⟨49271996545766213488303961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32847997697177475658869307 49271996545766213488303961)
      ·
        refine ⟨36953997409324660116227971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49271996545766213488303961 36953997409324660116227971)
        ·
          refine ⟨55430996113986990174341957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36953997409324660116227971 55430996113986990174341957)
          ·
            refine ⟨10393311771372560657689117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55430996113986990174341957 10393311771372560657689117)
            ·
              refine ⟨3897491914264710246633419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10393311771372560657689117 3897491914264710246633419)
              ·
                refine ⟨5846237871397065369950129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3897491914264710246633419 5846237871397065369950129)
                ·
                  refine ⟨4384678403547799027462597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5846237871397065369950129 4384678403547799027462597)
                  ·
                    refine ⟨822127200665212317649237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4384678403547799027462597 822127200665212317649237)
                    ·
                      rfl

theorem cell23_4803261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_4803261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803261 prefixEnd_4803261 := by exact prefixLift 4803261
  have htrace : WordTrace (prefixWord ++ tailWord_4803261) baseStart_4803261 baseEnd_4803261 := by
    simpa [prefixWord, tailWord_4803261, baseEnd_4803261] using wordTrace_append hprefix tailTrace_4803261
  have hstable : (prefixWord ++ tailWord_4803261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803261).length < 2 ^ (prefixWord ++ tailWord_4803261).sum := by decide
  have hdescent : baseEnd_4803261 < baseStart_4803261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803264 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 4]
def baseStart_4803264 : Nat := 118140960795 + 4803264 * 2 ^ 59
def prefixEnd_4803264 : Nat := 4983230072969 + 3 ^ 40 * 4803264 * 2
def baseEnd_4803264 : Nat := 2466383142437600441210197

theorem tailTrace_4803264 : CollatzResearch.WordTrace tailWord_4803264 prefixEnd_4803264 2466383142437600441210197 := by
  unfold tailWord_4803264
  simp only [CollatzResearch.WordTrace]
  refine ⟨87594715235301167513164423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116792953647068223350885897 87594715235301167513164423)
  ·
    refine ⟨131392072852951751269746635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87594715235301167513164423 131392072852951751269746635)
    ·
      refine ⟨197088109279427626904619953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131392072852951751269746635 197088109279427626904619953)
      ·
        refine ⟨147816081959570720178464965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197088109279427626904619953 147816081959570720178464965)
        ·
          refine ⟨27715515367419510033462181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147816081959570720178464965 27715515367419510033462181)
          ·
            refine ⟨5196659131391158131274159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27715515367419510033462181 5196659131391158131274159)
            ·
              refine ⟨7794988697086737196911239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5196659131391158131274159 7794988697086737196911239)
              ·
                refine ⟨11692483045630105795366859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7794988697086737196911239 11692483045630105795366859)
                ·
                  refine ⟨17538724568445158693050289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11692483045630105795366859 17538724568445158693050289)
                  ·
                    refine ⟨13154043426333869019787717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17538724568445158693050289 13154043426333869019787717)
                    ·
                      refine ⟨2466383142437600441210197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13154043426333869019787717 2466383142437600441210197)
                      ·
                        rfl

theorem cell23_4803264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_4803264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803264 prefixEnd_4803264 := by exact prefixLift 4803264
  have htrace : WordTrace (prefixWord ++ tailWord_4803264) baseStart_4803264 baseEnd_4803264 := by
    simpa [prefixWord, tailWord_4803264, baseEnd_4803264] using wordTrace_append hprefix tailTrace_4803264
  have hstable : (prefixWord ++ tailWord_4803264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803264).length < 2 ^ (prefixWord ++ tailWord_4803264).sum := by decide
  have hdescent : baseEnd_4803264 < baseStart_4803264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803274 : List Nat := [3, 1, 2, 1, 4, 3, 2, 7]
def baseStart_4803274 : Nat := 118140960795 + 4803274 * 2 ^ 59
def prefixEnd_4803274 : Nat := 4983230072969 + 3 ^ 40 * 4803274 * 2
def baseEnd_4803274 : Nat := 91347713972005385262413

theorem tailTrace_4803274 : CollatzResearch.WordTrace tailWord_4803274 prefixEnd_4803274 91347713972005385262413 := by
  unfold tailWord_4803274
  simp only [CollatzResearch.WordTrace]
  refine ⟨43797448800141526683548219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116793196800377404489461917 43797448800141526683548219)
  ·
    refine ⟨65696173200212290025322329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43797448800141526683548219 65696173200212290025322329)
    ·
      refine ⟨49272129900159217518991747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65696173200212290025322329 49272129900159217518991747)
      ·
        refine ⟨73908194850238826278487621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49272129900159217518991747 73908194850238826278487621)
        ·
          refine ⟨13857786534419779927216429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73908194850238826278487621 13857786534419779927216429)
          ·
            refine ⟨5196669950407417472706161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13857786534419779927216429 5196669950407417472706161)
            ·
              refine ⟨3897502462805563104529621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5196669950407417472706161 3897502462805563104529621)
              ·
                refine ⟨91347713972005385262413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3897502462805563104529621 91347713972005385262413)
                ·
                  rfl

theorem cell23_4803274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 7].length) (baseStart_4803274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803274 prefixEnd_4803274 := by exact prefixLift 4803274
  have htrace : WordTrace (prefixWord ++ tailWord_4803274) baseStart_4803274 baseEnd_4803274 := by
    simpa [prefixWord, tailWord_4803274, baseEnd_4803274] using wordTrace_append hprefix tailTrace_4803274
  have hstable : (prefixWord ++ tailWord_4803274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803274).length < 2 ^ (prefixWord ++ tailWord_4803274).sum := by decide
  have hdescent : baseEnd_4803274 < baseStart_4803274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4803377 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 1, 7]
def baseStart_4803377 : Nat := 118140960795 + 4803377 * 2 ^ 59
def prefixEnd_4803377 : Nat := 4983230072969 + 3 ^ 40 * 4803377 * 2
def baseEnd_4803377 : Nat := 822147055250519499699059

theorem tailTrace_4803377 : CollatzResearch.WordTrace tailWord_4803377 prefixEnd_4803377 822147055250519499699059 := by
  unfold tailWord_4803377
  simp only [CollatzResearch.WordTrace]
  refine ⟨175193551919192955325192385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116795701279461970216794923 175193551919192955325192385)
  ·
    refine ⟨131395163939394716493894289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175193551919192955325192385 131395163939394716493894289)
    ·
      refine ⟨98546372954546037370420717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131395163939394716493894289 98546372954546037370420717)
      ·
        refine ⟨36954889857954764013907769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98546372954546037370420717 36954889857954764013907769)
        ·
          refine ⟨27716167393466073010430827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36954889857954764013907769 27716167393466073010430827)
          ·
            refine ⟨41574251090199109515646241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27716167393466073010430827 41574251090199109515646241)
            ·
              refine ⟨31180688317649332136734681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41574251090199109515646241 31180688317649332136734681)
              ·
                refine ⟨23385516238236999102551011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31180688317649332136734681 23385516238236999102551011)
                ·
                  refine ⟨35078274357355498653826517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23385516238236999102551011 35078274357355498653826517)
                  ·
                    refine ⟨822147055250519499699059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35078274357355498653826517 822147055250519499699059)
                    ·
                      rfl

theorem cell23_4803377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_4803377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4803377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4803377 prefixEnd_4803377 := by exact prefixLift 4803377
  have htrace : WordTrace (prefixWord ++ tailWord_4803377) baseStart_4803377 baseEnd_4803377 := by
    simpa [prefixWord, tailWord_4803377, baseEnd_4803377] using wordTrace_append hprefix tailTrace_4803377
  have hstable : (prefixWord ++ tailWord_4803377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4803377).length < 2 ^ (prefixWord ++ tailWord_4803377).sum := by decide
  have hdescent : baseEnd_4803377 < baseStart_4803377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4803377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
